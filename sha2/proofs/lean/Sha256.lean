import Compress
import SetChain
import Loop0
import Loop1
import FinalBlock

/-!
# Full SHA-256 refinement against `SHS.SHA256.Impl`

The per-round / per-block proofs (`compress_u32_spec`, `compress256_spec`)
live in `Compress.lean` so `Loop0` can import them without a
cycle. This file pulls everything together for the top-level `sha256_spec`.
-/



open Aeneas Aeneas.Std Result WP SHS.SHA256

/-! ## Full SHA-256

`sha256_inner` casts `data.size << 3` to `u64`; the cast silently wraps
on inputs ≥ 2^61 bytes. The Impl side `panic!`s above that threshold, so
the refinement carries `data.length < 2^61` as a precondition. -/

/-! ### Helper: `ByteArray.toList` of the materialized slice. -/
private theorem sliceToByteArray_toList (data : Slice U8) :
    (sliceToByteArray data).toList = data.val.map toUInt8 := by
  rw [ByteArray.toList_eq_data_toList]
  show ((data.val.map toUInt8).toArray).toList = data.val.map toUInt8
  simp

/-! ### Top-level theorem.

Bridges `Extraction.sha256_inner consts.H256_256 data` to
`Impl.sha256 (sliceToByteArray data)`. The byte-level final-block
construction (`finalBlockA` zero-init / data-copy / `0x80` marker /
branch on `remaining ≥ 56` / BE length bytes / final `compress256`
/ `loop1`) is factored through `padded_block_spec`. The BE-length and
loop0 IV bridges (`total_bits_bv_eq`, `H256_256_eq`) live in
`FinalBlock.lean` and `U32.lean` respectively. -/

/-- The main bridge theorem.

Strategy: `unfold Extraction.sha256_inner`. Then, in order:
* `step` through `Slice.len`, `>>> 6`, `&&& 63` (gives `blocks` and
  `remaining` with `blocks.val * 64 + remaining.val = data.length`).
* Apply `sha256_inner_loop0_spec` (composed with `H256_256_eq`) to
  discharge the per-block fold, threading `state` through.
* `step` through the cast + shift to materialize `total_bits`,
  using `total_bits_bv_eq` for the BV equality.
* Branch on `remaining ≥ 56`. In the ≥-arm, run an extra
  `compress256` over the partially-padded block (data tail + `0x80`
  marker, no length tag); in the <-arm, skip that step.
* In both arms, apply `padded_block_spec` to the (all-zero in the
  ≥-arm, partially-padded in the <-arm) block to install the
  big-endian length tag in the last 8 bytes. This is where the
  bulk of the bookkeeping lives.
* Run a final `compress256` on the resulting block.
* Apply `sha256_inner_loop1_spec` to convert the final state to
  output bytes; match against the Impl-side `Vector.ofFn` BE-emit
  via `Vector.ext`.

Most of the proof effort is delegated to `padded_block_spec`
(`FinalBlock.lean`), which walks through the mutable-index plumbing
of Aeneas's `Array.repeat`/`index_mut`/`copy_from_slice`/`index_mut_back`
chain. -/
private theorem sha256_inner_spec
    (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha256_inner Extraction.consts.H256_256 data
    ⦃ out => arrayU8ToVec out = Impl.sha256 (sliceToByteArray data) ⦄ := by
  unfold Extraction.sha256_inner
  step
  · show (6 : Int) < (System.Platform.numBits : Int)
    have h := System.Platform.numBits_eq
    rcases h with h | h <;> rw [h] <;> decide
  step
  -- `out` here is `blocks` (the first `>>> 6` step). Derive `out.val * 64 ≤ data.length`.
  have hbl : out.val * 64 ≤ data.length := by
    have h1 : (↑out : Nat) = data.length / 64 := by
      rw [out_post1, Nat.shiftRight_eq_div_pow]; rfl
    rw [h1]
    exact Nat.div_mul_le_self data.length 64
  -- Per-block fold + IV bridge.
  have hloop0 :
      Extraction.sha256_inner_loop0 ⟨0#usize, out⟩ data Extraction.consts.H256_256
      ⦃ s => arrayU32ToVec s =
          Fin.foldl out.val (loop0_step data out) Impl.H256_256 ⦄ := by
    apply spec_mono (sha256_inner_loop0_spec data Extraction.consts.H256_256 out hbl)
    intro s hs; rw [hs, H256_256_eq]
  apply spec_bind hloop0
  intro state hstate
  step  -- i3 = UScalar.cast .U64 data.len
  step  -- total_bits = i3 <<< 3
  -- Derive `remaining = data.length % 64` and
  -- `blocks * 64 + remaining = data.length`.
  have hrem_mod : remaining.val = data.length % 64 := by
    rw [remaining_post1]
    show ((data.len.val : Nat) &&& 63) = data.length % 64
    have : (data.len.val) &&& (2^6 - 1) = data.len.val % 2^6 :=
      Nat.and_two_pow_sub_one_eq_mod _ _
    simpa using this
  have hblocks : (out.val : Nat) = data.length / 64 := by
    rw [out_post1, Nat.shiftRight_eq_div_pow]; rfl
  have hsum : out.val * 64 + remaining.val = data.length := by
    rw [hrem_mod, hblocks]
    have := Nat.div_add_mod data.length 64
    omega
  have hrem_lt : remaining.val < 64 := by rw [hrem_mod]; exact Nat.mod_lt _ (by decide)
  step as ⟨discr1, hd1⟩
  -- Aeneas now wraps `core.array.Array.index_mut` results in
  -- `let (s, index_mut_back) := discr1; …`; `step` can't see through the
  -- pair-`let`, so destructure with `cases` (which iota-reduces in goal).
  obtain ⟨s, index_mut_back⟩ := discr1
  step as ⟨i4, hi4_v⟩
  step as ⟨s1, hs1_drop, hs1_len⟩
  -- copy_from_slice spec needs s.length = s1.length
  -- s.length = remaining.val (from hd1.2.1)
  -- s1.length = data.length - i4.val (from hs1_len)
  -- Need to show these are equal, using i4 = blocks*64 and remaining = data.length % 64.
  -- We have hbl: blocks * 64 ≤ data.length.
  have hcopy_len : s.length = s1.length := by
    rw [hd1.2.1, hs1_len, hi4_v]
    -- remaining = data.length - blocks * 64
    omega
  apply spec_bind (core.slice.Slice.copy_from_slice.step_spec _ s s1 hcopy_len)
  intro s2 hs2_eq
  -- Stage 3b: index_mut_usize remaining on (index_mut_back s2) — sets the 0x80 marker.
  have hbound1 : remaining.val < (index_mut_back s2).length := by
    have hlen : (index_mut_back s2).length = 64 := (index_mut_back s2).property
    omega
  apply spec_bind (Std.Array.index_mut_usize_spec (index_mut_back s2) remaining hbound1)
  rintro ⟨val_at_rem, set_back⟩ ⟨hset_back, hval_at⟩
  -- `set_back 128#u8` has the data bytes, 0x80 marker, and zeros — matches vA for all i < 64.
  set vA : Vector UInt8 64 := Vector.ofFn fun i : Fin 64 =>
    if i.val < remaining.val then (sliceToByteArray data).get! (out.val * 64 + i.val)
    else if i.val = remaining.val then 0x80
    else 0 with hvA_def
  have hfull_match : ∀ (i : Nat) (hi : i < 64),
      toUInt8 ((set_back 128#u8).val[i]'(by simp [(set_back 128#u8).property]; omega)) =
        vA[i]'(by omega) := by
    intro i hi
    have hsb_len : (set_back 128#u8).val.length = 64 := (set_back 128#u8).property
    have hs2v : s2.val = data.val.drop (out.val * 64) := by rw [← hs2_eq, hs1_drop, hi4_v]
    have hs2_len : s2.val.length = data.length - out.val * 64 := by
      rw [hs2v]; simp [List.length_drop]
    have hsb_val : (set_back 128#u8).val =
        ((List.replicate 64 (0#u8 : U8)).setSlice! 0 s2.val).set remaining.val 128#u8 := by
      rw [hset_back]; show (index_mut_back s2).val.set remaining.val (128#u8 : U8) = _
      rw [hd1.2.2 s2, Array.repeat_val]; rfl
    rw [List.Inhabited_getElem_eq_getElem! _ _ (by rw [hsb_len]; exact hi), hsb_val]
    have hvA_get : vA[i]'(by omega) =
        if i < remaining.val then (sliceToByteArray data).get! (out.val * 64 + i)
        else if i = remaining.val then (128 : UInt8) else 0 := by
      show (Vector.ofFn _)[i]'(by omega) = _; rw [Vector.getElem_ofFn]
    rw [hvA_get]
    have hsetSlice_len : ((List.replicate 64 (0#u8 : U8)).setSlice! 0 s2.val).length = 64 := by
      rw [List.length_setSlice!, List.length_replicate]
    by_cases hieq : i = remaining.val
    · rw [hieq, List.getElem!_set _ _ _ (by rw [hsetSlice_len]; omega),
        if_neg (show ¬ remaining.val < remaining.val from by omega), if_pos rfl]; rfl
    · rw [List.getElem!_set_ne _ remaining.val i 128#u8
            (by show Nat.not_eq remaining.val i; unfold Nat.not_eq; omega)]
      by_cases hilt : i < remaining.val
      · have hi_in_s2 : i < s2.val.length := by rw [hs2_len]; omega
        rw [List.getElem!_setSlice!_middle _ _ 0 i
          ⟨Nat.zero_le _, by simpa using hi_in_s2, by rw [List.length_replicate]; omega⟩]
        show toUInt8 (s2.val[i - 0]!) = _; simp only [Nat.sub_zero]; rw [if_pos hilt]
        have hd_idx : out.val * 64 + i < data.length := by scalar_tac
        rw [getElem!_pos s2.val i hi_in_s2,
          show s2.val[i]'hi_in_s2 = (data.val.drop (out.val * 64))[i]'(hs2v ▸ hi_in_s2)
            from by congr 1, List.getElem_drop]
        show _ = (⟨(data.val.map toUInt8).toArray⟩ : ByteArray).get! (out.val * 64 + i)
        have hda_idx : out.val * 64 + i < (data.val.map toUInt8).toArray.size := by
          simp; exact hd_idx
        rw [show ((⟨(data.val.map toUInt8).toArray⟩ : ByteArray).get! (out.val * 64 + i)) =
            (data.val.map toUInt8).toArray[out.val * 64 + i]! from rfl,
          getElem!_pos (data.val.map toUInt8).toArray (out.val * 64 + i) hda_idx]
        show toUInt8 _ = _; simp [List.getElem_map]
      · have hi_past_s2 : s2.val.length ≤ i := by rw [hs2_len]; omega
        rw [List.getElem!_setSlice!_suffix _ _ 0 i (by simpa),
          List.getElem!_replicate _ (show i < 64 from by omega)]
        show toUInt8 (0#u8 : U8) = _
        rw [if_neg (show ¬ i < remaining.val from by omega), if_neg hieq]; rfl
  -- `toUInt64 total_bits = data.length * 8` (shared by both arms).
  have htotal : toUInt64 total_bits = data.length.toUInt64 <<< 3 := by
    apply UInt64.toBitVec_inj.mp
    show total_bits.bv = (data.length.toUInt64 <<< 3).toBitVec
    have h1 : total_bits.bv = i3.bv <<< 3 := total_bits_post2
    have h2 : i3 = UScalar.cast UScalarTy.U64 data.len := i3_post
    rw [h1, h2]
    have := total_bits_bv_eq data h; rw [sliceToByteArray_size] at this; exact this
  by_cases hge : remaining ≥ 56#usize
  · -- ≥-arm: extra compress on vA block, then padded_block_spec on all-zero block.
    simp only [hge, ↓reduceIte]
    have hrem_ge56 : 56 ≤ remaining.val := by have hh := hge; scalar_tac
    simp only [lift, bind_tc_ok, bind_assoc]
    set sb1 := (Array.make 1#usize [set_back 128#u8] List.length_singleton).to_slice with hsb1_def
    have hsb1_val : sb1.val = [set_back 128#u8] := by rw [hsb1_def, Array.val_to_slice]; rfl
    apply spec_bind (compress256_spec state sb1)
    intro stateA hstateA
    rw [hsb1_val] at hstateA; simp only [List.foldl_cons, List.foldl_nil] at hstateA
    have hsb_to_vA : arrayU8ToVec (set_back 128#u8) = vA := by
      apply Vector.ext; intro k hk
      have hk64 : k < 64 := by simpa using hk
      rw [arrayU8ToVec_getElem (h := hk64)]; exact hfull_match k hk64
    rw [hsb_to_vA] at hstateA
    set vB : Vector UInt8 64 := Vector.replicate 64 (0 : UInt8) with hvB_def
    have hlow_zero : ∀ (i : Nat) (hi : i < 56),
        toUInt8 ((Array.repeat 64#usize (0#u8 : U8)).val[i]'(by
          simp; omega)) = vB[i]'(by omega) := by
      intro i hi
      have hbyte : (Array.repeat 64#usize (0#u8 : U8)).val[i]'(by
          simp; omega) = (0#u8 : U8) := by
        have hval : (Array.repeat 64#usize (0#u8 : U8)).val = List.replicate 64 (0#u8 : U8) :=
          Array.repeat_val 64#usize (0#u8 : U8)
        conv_lhs => rw [List.Inhabited_getElem_eq_getElem! _ _ (by
          simp; omega)]
        rw [hval, List.getElem!_replicate _ (show i < 64 from by omega)]
      rw [hbyte]
      show toUInt8 (0#u8 : U8) = vB[i]
      rw [hvB_def, Vector.getElem_replicate]
      rfl
    have hpad := padded_block_spec (Array.repeat 64#usize 0#u8) vB hlow_zero total_bits
    -- The outer pair-`let` is defeq to its iota-reduced form; use `show`
    -- to force Lean to view the goal in that shape so `apply spec_bind hpad`
    -- can match the prefix.
    show WP.spec (do
        let (s3, index_mut_back2) ←
          core.array.Array.index_mut (core.ops.index.IndexMutSlice
            (core.slice.index.SliceIndexRangeUsizeSlice U8))
            (Array.repeat 64#usize 0#u8) { start := 56#usize, «end» := 64#usize }
        let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3
                   (core.num.U64.to_be_bytes total_bits).to_slice
        let state2 ← Extraction.sha256.compress256 stateA
                       (Array.make 1#usize [index_mut_back2 s5] List.length_singleton).to_slice
        Extraction.sha256_inner_loop1 { start := 0#usize, «end» := 8#usize }
          state2 (Array.repeat 32#usize 0#u8)) _
    -- Reshape via `bind_assoc` and `bind_tc_ok` so the prefix matches `hpad`.
    rw [show
        (do
          let (s3, index_mut_back2) ←
            core.array.Array.index_mut (core.ops.index.IndexMutSlice
              (core.slice.index.SliceIndexRangeUsizeSlice U8))
              (Array.repeat 64#usize 0#u8) { start := 56#usize, «end» := 64#usize }
          let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3
                     (core.num.U64.to_be_bytes total_bits).to_slice
          let state2 ← Extraction.sha256.compress256 stateA
                         (Array.make 1#usize [index_mut_back2 s5] List.length_singleton).to_slice
          Extraction.sha256_inner_loop1 { start := 0#usize, «end» := 8#usize }
            state2 (Array.repeat 32#usize 0#u8) :
            Result (Std.Array U8 32#usize))
      = ((do
          let __discr ←
            core.array.Array.index_mut (core.ops.index.IndexMutSlice
              (core.slice.index.SliceIndexRangeUsizeSlice U8))
              (Array.repeat 64#usize 0#u8) { start := 56#usize, «end» := 64#usize }
          let a ← lift (core.num.U64.to_be_bytes total_bits)
          let s4 ← lift (Array.to_slice a)
          let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 __discr.1 s4
          ok (__discr.2 s5)) >>= fun final_block3 => do
        let state2 ← Extraction.sha256.compress256 stateA
                       (Array.make 1#usize [final_block3] List.length_singleton).to_slice
        Extraction.sha256_inner_loop1 { start := 0#usize, «end» := 8#usize }
          state2 (Array.repeat 32#usize 0#u8)) from by simp [lift, bind_tc_ok]]
    apply spec_bind hpad
    intro fb hfb
    set s6 := (Array.make 1#usize [fb] List.length_singleton).to_slice with hs6_def
    apply spec_bind (compress256_spec stateA s6)
    intro state2 hstate2
    have hs6_val : s6.val = [fb] := by rw [hs6_def, Array.val_to_slice]; rfl
    rw [hs6_val] at hstate2; simp only [List.foldl_cons, List.foldl_nil] at hstate2
    apply spec_mono (sha256_inner_loop1_spec state2 (Array.repeat 32#usize 0#u8))
    intro out hout; rw [hout]
    unfold Impl.sha256
    have hsize_lt : ¬ 2 ^ 61 ≤ (sliceToByteArray data).size := by
      simp [sliceToByteArray_size]; omega
    rw [if_neg hsize_lt]
    have hsz : (sliceToByteArray data).size = data.length := by simp
    have hvA_eq : vA = Vector.ofFn (fun k : Fin 64 =>
        if k.val < data.length % 64 then (sliceToByteArray data).get! (data.length / 64 * 64 + k.val)
        else if k.val = data.length % 64 then 128 else 0) := by
      rw [hvA_def, hrem_mod, hblocks]
    have hfb_full : arrayU8ToVec fb =
        Vector.ofFn (fun i : Fin 64 =>
          if i.val < 56 then (0 : UInt8)
          else (data.length.toUInt64 <<< 3 >>> ((63 - i.val) * 8).toUInt64 &&& 255).toUInt8) := by
      rw [hfb]; apply Vector.ext; intro i hi; simp only [Vector.getElem_ofFn]
      by_cases hi56 : i < 56
      · rw [if_pos hi56, if_pos hi56, hvB_def]; simp
      · rw [if_neg hi56, if_neg hi56, htotal]
    have hstate_prefix : arrayU32ToVec state =
        Fin.foldl (data.length / 64)
          (fun s i => Impl.compress s (Impl.toU32sFromBytes (sliceToByteArray data) (i.val * 64)))
          Impl.H256_256 := by rw [hstate, ← hblocks]; rfl
    have hstate_full : arrayU32ToVec stateA =
        Impl.compress
          (Fin.foldl (data.length / 64)
            (fun s i => Impl.compress s (Impl.toU32sFromBytes (sliceToByteArray data) (i.val * 64)))
            Impl.H256_256)
          (Impl.toU32s (Vector.ofFn (fun k : Fin 64 =>
            if k.val < data.length % 64 then (sliceToByteArray data).get! (data.length / 64 * 64 + k.val)
            else if k.val = data.length % 64 then 128 else 0))) := by
      rw [hstateA, hstate_prefix, ← hvA_eq]
    have hcond : ¬ data.length % 64 < 56 := by rw [← hrem_mod]; simp at hge; omega
    rw [hstate2, hstate_full, hfb_full]; simp only [hsz, if_neg hcond]; rfl
  · -- <-arm: remaining < 56, so no extra compress — apply padded_block_spec directly.
    simp only [hge, ↓reduceIte]
    have hrem_lt56 : remaining.val < 56 := by simp at hge; scalar_tac
    -- padded_block_spec needs the low 56 bytes of `set_back 128#u8` to match vA.
    have hpad := padded_block_spec (set_back 128#u8) vA
      (fun i hi => hfull_match i (by omega)) total_bits
    -- Same iota-redex situation as the ≥-arm: outer pair-`let`s plus
    -- destructured index_mut. `show` reshapes; `rw` flattens to `>>= …`.
    show WP.spec (do
        let (s3, index_mut_back2) ←
          core.array.Array.index_mut (core.ops.index.IndexMutSlice
            (core.slice.index.SliceIndexRangeUsizeSlice U8))
            (set_back 128#u8) { start := 56#usize, «end» := 64#usize }
        let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3
                   (core.num.U64.to_be_bytes total_bits).to_slice
        let s6 ← lift (Array.to_slice (Array.make 1#usize [index_mut_back2 s5]
                                         List.length_singleton))
        let state2 ← Extraction.sha256.compress256 state s6
        Extraction.sha256_inner_loop1 { start := 0#usize, «end» := 8#usize }
          state2 (Array.repeat 32#usize 0#u8)) _
    rw [show
        (do
          let (s3, index_mut_back2) ←
            core.array.Array.index_mut (core.ops.index.IndexMutSlice
              (core.slice.index.SliceIndexRangeUsizeSlice U8))
              (set_back 128#u8) { start := 56#usize, «end» := 64#usize }
          let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3
                     (core.num.U64.to_be_bytes total_bits).to_slice
          let s6 ← lift (Array.to_slice (Array.make 1#usize [index_mut_back2 s5]
                                           List.length_singleton))
          let state2 ← Extraction.sha256.compress256 state s6
          Extraction.sha256_inner_loop1 { start := 0#usize, «end» := 8#usize }
            state2 (Array.repeat 32#usize 0#u8) :
            Result (Std.Array U8 32#usize))
      = ((do
          let __discr ←
            core.array.Array.index_mut (core.ops.index.IndexMutSlice
              (core.slice.index.SliceIndexRangeUsizeSlice U8))
              (set_back 128#u8) { start := 56#usize, «end» := 64#usize }
          let a ← lift (core.num.U64.to_be_bytes total_bits)
          let s4 ← lift (Array.to_slice a)
          let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 __discr.1 s4
          ok (__discr.2 s5)) >>= fun final_block3 => do
        let s6 ← lift (Array.to_slice (Array.make 1#usize [final_block3] List.length_singleton))
        let state2 ← Extraction.sha256.compress256 state s6
        Extraction.sha256_inner_loop1 { start := 0#usize, «end» := 8#usize }
          state2 (Array.repeat 32#usize 0#u8)) from by simp [lift, bind_tc_ok]]
    apply spec_bind hpad
    intro fb hfb
    simp only [lift, bind_tc_ok]
    set s6 := (Array.make 1#usize [fb] List.length_singleton).to_slice with hs6_def
    apply spec_bind (compress256_spec state s6)
    intro state2 hstate2
    have hs6_val : s6.val = [fb] := by rw [hs6_def, Array.val_to_slice]; rfl
    rw [hs6_val] at hstate2; simp only [List.foldl_cons, List.foldl_nil] at hstate2
    apply spec_mono (sha256_inner_loop1_spec state2 (Array.repeat 32#usize 0#u8))
    intro out hout; rw [hout]
    unfold Impl.sha256
    have hsize_lt : ¬ 2 ^ 61 ≤ (sliceToByteArray data).size := by
      simp [sliceToByteArray_size]; omega
    rw [if_neg hsize_lt]
    have hsz : (sliceToByteArray data).size = data.length := by simp
    apply Vector.ext; intro j hj
    simp only [Vector.getElem_ofFn]
    have hvA_eq : vA = Vector.ofFn (fun k : Fin 64 =>
        if k.val < data.length % 64 then (sliceToByteArray data).get! (data.length / 64 * 64 + k.val)
        else if k.val = data.length % 64 then 128 else 0) := by
      rw [hvA_def, hrem_mod, hblocks]
    have hfb_full : arrayU8ToVec fb =
        Vector.ofFn (fun i : Fin 64 =>
          if i.val < 56 then
            (Vector.ofFn (fun k : Fin 64 =>
              if k.val < data.length % 64 then (sliceToByteArray data).get! (data.length / 64 * 64 + k.val)
              else if k.val = data.length % 64 then 128 else 0))[i]
          else (data.length.toUInt64 <<< 3 >>> ((63 - i.val) * 8).toUInt64 &&& 255).toUInt8) := by
      rw [hfb, ← hvA_eq]; apply Vector.ext; intro i hi; simp only [Vector.getElem_ofFn]
      by_cases hi56 : i < 56
      · rw [if_pos hi56, if_pos hi56]
      · rw [if_neg hi56, if_neg hi56, htotal]
    have hstate_full : arrayU32ToVec state =
        Fin.foldl (data.length / 64)
          (fun s i => Impl.compress s (Impl.toU32sFromBytes (sliceToByteArray data) (i.val * 64)))
          Impl.H256_256 := by rw [hstate, ← hblocks]; rfl
    have hcond : data.length % 64 < 56 := by rw [← hrem_mod]; exact hrem_lt56
    rw [hstate2, hstate_full, hfb_full]; simp only [hsz, if_pos hcond]; rfl

/-- Public top-level spec: the Aeneas-extracted `sha256` returns the
same digest as `Impl.sha256` on the corresponding `ByteArray`. -/
theorem sha256_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha256 data
    ⦃ out =>
        ∃ ba : ByteArray, ba.toList = (data.val.map toUInt8) ∧
          (arrayU8ToVec out).toList = (Impl.sha256 ba).toList ⦄ := by
  unfold Extraction.sha256
  apply spec_mono (sha256_inner_spec data h)
  intro out hout
  refine ⟨sliceToByteArray data, sliceToByteArray_toList data, ?_⟩
  rw [hout]
  rfl


