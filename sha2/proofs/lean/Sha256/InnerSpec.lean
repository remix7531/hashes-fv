import Sha256.Compress
import Sha256.SetChain
import Sha256.Loop0
import Sha256.Loop1
import Sha256.FinalBlock
import Sha256.Inner

/-!
# IV-generic SHA-256 inner refinement

`sha2_inner_spec` is the IV-parameterized version of the SHA-256 inner-spec.
Both `Sha256.lean::sha256_inner_spec` (the SHA-256 corollary) and
`Sha224.lean::sha224_spec` consume it.

The proof structure: `step` through `Slice.len`, `>>> 6`, `&&& 63`; apply
`sha256_inner_loop0_spec` (with IV bridge `hiv`); branch on
`remaining ≥ 56`; apply `padded_block_spec` to install the BE length tag;
final `compress256`; `sha256_inner_loop1_spec` for the BE-emit; close by
matching against `Local.sha2Inner256`'s `Vector.ofFn` BE-emit via
`Vector.ext`.
-/

open Aeneas Aeneas.Std Result WP SHS.SHA256

/-- IV-generic version: for any IV `iv` whose `arrayU32ToVec` view is
`iv_vec`, `Extraction.sha256_inner iv data` returns the IV-parameterized
Impl-layer core applied to the same IV.

The SHA-256 inner-spec (`Sha256.lean::sha256_inner_spec`) is the corollary at
`iv = consts.H256_256, iv_vec = Impl.H256_256` bridged through
`Local.sha256_eq_sha2Inner256`.  SHA-224 (`Sha224.lean::sha224_spec`) uses
the corollary at `iv = consts.H256_224, iv_vec = Local.H256_224`. -/
theorem sha2_inner_spec
    (iv : Array U32 8#usize) (iv_vec : Vector UInt32 8)
    (hiv : arrayU32ToVec iv = iv_vec)
    (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha256_inner iv data
    ⦃ out => arrayU8ToVec out = Local.sha2Inner256 iv_vec (sliceToByteArray data) ⦄ := by
  unfold Extraction.sha256_inner
  step
  · show (6 : Int) < (System.Platform.numBits : Int)
    have h := System.Platform.numBits_eq
    rcases h with h | h <;> rw [h] <;> decide
  step
  have hbl : out.val * 64 ≤ data.length := by
    have h1 : (↑out : Nat) = data.length / 64 := by
      rw [out_post1, Nat.shiftRight_eq_div_pow]; rfl
    rw [h1]
    exact Nat.div_mul_le_self data.length 64
  have hloop0 :
      Extraction.sha256_inner_loop0 ⟨0#usize, out⟩ data iv
      ⦃ s => arrayU32ToVec s =
          Fin.foldl out.val (loop0_step data out) iv_vec ⦄ := by
    apply spec_mono (sha256_inner_loop0_spec data iv out hbl)
    intro s hs; rw [hs, hiv]
  apply spec_bind hloop0
  intro state hstate
  step
  step
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
  obtain ⟨s, index_mut_back⟩ := discr1
  step as ⟨i4, hi4_v⟩
  step as ⟨s1, hs1_drop, hs1_len⟩
  have hcopy_len : s.length = s1.length := by
    rw [hd1.2.1, hs1_len, hi4_v]
    omega
  apply spec_bind (core.slice.Slice.copy_from_slice.step_spec _ s s1 hcopy_len)
  intro s2 hs2_eq
  have hbound1 : remaining.val < (index_mut_back s2).length := by
    have hlen : (index_mut_back s2).length = 64 := (index_mut_back s2).property
    omega
  apply spec_bind (Std.Array.index_mut_usize_spec (index_mut_back s2) remaining hbound1)
  rintro ⟨val_at_rem, set_back⟩ ⟨hset_back, hval_at⟩
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
  have htotal : toUInt64 total_bits = data.length.toUInt64 <<< 3 := by
    apply UInt64.toBitVec_inj.mp
    show total_bits.bv = (data.length.toUInt64 <<< 3).toBitVec
    have h1 : total_bits.bv = i3.bv <<< 3 := total_bits_post2
    have h2 : i3 = UScalar.cast UScalarTy.U64 data.len := i3_post
    rw [h1, h2]
    have := total_bits_bv_eq data h; rw [sliceToByteArray_size] at this; exact this
  by_cases hge : remaining ≥ 56#usize
  · simp only [hge, ↓reduceIte]
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
    rw [padded_block_reshape (Array.repeat 64#usize 0#u8) total_bits
          (fun final_block3 => do
            let state2 ← Extraction.sha256.compress256 stateA
                           (Array.make 1#usize [final_block3] List.length_singleton).to_slice
            Extraction.sha256_inner_loop1 { start := 0#usize, «end» := 8#usize }
              state2 (Array.repeat 32#usize 0#u8))]
    apply spec_bind hpad
    intro fb hfb
    set s6 := (Array.make 1#usize [fb] List.length_singleton).to_slice with hs6_def
    apply spec_bind (compress256_spec stateA s6)
    intro state2 hstate2
    have hs6_val : s6.val = [fb] := by rw [hs6_def, Array.val_to_slice]; rfl
    rw [hs6_val] at hstate2; simp only [List.foldl_cons, List.foldl_nil] at hstate2
    apply spec_mono (sha256_inner_loop1_spec state2 (Array.repeat 32#usize 0#u8))
    intro out hout; rw [hout]
    unfold Local.sha2Inner256 SHS.SHA256.Impl.sha256State
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
          iv_vec := by rw [hstate, ← hblocks]; rfl
    have hstate_full : arrayU32ToVec stateA =
        Impl.compress
          (Fin.foldl (data.length / 64)
            (fun s i => Impl.compress s (Impl.toU32sFromBytes (sliceToByteArray data) (i.val * 64)))
            iv_vec)
          (Impl.toU32s (Vector.ofFn (fun k : Fin 64 =>
            if k.val < data.length % 64 then (sliceToByteArray data).get! (data.length / 64 * 64 + k.val)
            else if k.val = data.length % 64 then 128 else 0))) := by
      rw [hstateA, hstate_prefix, ← hvA_eq]
    have hcond : ¬ data.length % 64 < 56 := by rw [← hrem_mod]; simp at hge; omega
    rw [hstate2, hstate_full, hfb_full]; simp only [hsz, if_neg hcond]; rfl
  · simp only [hge, ↓reduceIte]
    have hrem_lt56 : remaining.val < 56 := by simp at hge; scalar_tac
    have hpad := padded_block_spec (set_back 128#u8) vA
      (fun i hi => hfull_match i (by omega)) total_bits
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
    rw [padded_block_reshape (set_back 128#u8) total_bits
          (fun final_block3 => do
            let s6 ← lift (Array.to_slice (Array.make 1#usize [final_block3] List.length_singleton))
            let state2 ← Extraction.sha256.compress256 state s6
            Extraction.sha256_inner_loop1 { start := 0#usize, «end» := 8#usize }
              state2 (Array.repeat 32#usize 0#u8))]
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
    unfold Local.sha2Inner256 SHS.SHA256.Impl.sha256State
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
          iv_vec := by rw [hstate, ← hblocks]; rfl
    have hcond : data.length % 64 < 56 := by rw [← hrem_mod]; exact hrem_lt56
    rw [hstate2, hstate_full, hfb_full]; simp only [hsz, if_pos hcond]; rfl
