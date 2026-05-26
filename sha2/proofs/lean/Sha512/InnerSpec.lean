import Sha512.Compress
import Sha512.SetChain
import Sha512.Loop0
import Sha512.Loop1
import Sha512.FinalBlock
import Sha512.Inner

/-!
# IV-generic SHA-512 inner refinement

64-bit analogue of `Sha256/InnerSpec.lean`.  `sha2_inner_spec_512` is the
IV-parameterized version of the SHA-512 inner-spec.  Both `Sha512.lean`,
`Sha384.lean`, `Sha512_256.lean`, `Sha512_224.lean` consume it.

The proof structure mirrors SHA-256 with width adjustments: blocks
`>>> 7`, remainder `&&& 127`, block size 128, padding threshold 112,
output 64 bytes, length tag U128 (16 bytes) instead of U64 (8 bytes).
The U128 length tag is bridged via `total_bits_bv_eq_u128_shifted`,
`u128_be_byte_high_zero`, `u128_be_byte_low_eq_u64`.
-/

open Aeneas Aeneas.Std Result WP SHS.SHA512

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
/-- IV-generic version: for any IV `iv` whose `arrayU64ToVec` view is
`iv_vec`, `Extraction.sha512_inner iv data` returns the IV-parameterized
Impl-layer core applied to the same IV.

The four public-digest specs (`sha512_spec`, `sha384_spec`,
`sha512_256_spec`, `sha512_224_spec`) are corollaries at the appropriate
IV bridged through `Local.sha512_eq_sha2Inner512` etc. -/
theorem sha2_inner_spec_512
    (iv : Array U64 8#usize) (iv_vec : Vector UInt64 8)
    (hiv : arrayU64ToVec iv = iv_vec)
    (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha512_inner iv data
    ⦃ out => arrayU8ToVec out = Local.sha2Inner512 iv_vec (sliceToByteArray data) ⦄ := by
  unfold Extraction.sha512_inner
  step
  · show (7 : Int) < (System.Platform.numBits : Int)
    have h := System.Platform.numBits_eq
    rcases h with h | h <;> rw [h] <;> decide
  step
  have hbl : out.val * 128 ≤ data.length := by
    have h1 : (↑out : Nat) = data.length / 128 := by
      rw [out_post1, Nat.shiftRight_eq_div_pow]; rfl
    rw [h1]
    exact Nat.div_mul_le_self data.length 128
  have hloop0 :
      Extraction.sha512_inner_loop0 ⟨0#usize, out⟩ data iv
      ⦃ s => arrayU64ToVec s =
          Fin.foldl out.val (loop0_step_512 data out) iv_vec ⦄ := by
    apply spec_mono (sha512_inner_loop0_spec data iv out hbl)
    intro s hs; rw [hs, hiv]
  apply spec_bind hloop0
  intro state hstate
  step
  step
  have hrem_mod : remaining.val = data.length % 128 := by
    rw [remaining_post1]
    show ((data.len.val : Nat) &&& 127) = data.length % 128
    have : (data.len.val) &&& (2^7 - 1) = data.len.val % 2^7 :=
      Nat.and_two_pow_sub_one_eq_mod _ _
    simpa using this
  have hblocks : (out.val : Nat) = data.length / 128 := by
    rw [out_post1, Nat.shiftRight_eq_div_pow]; rfl
  have hsum : out.val * 128 + remaining.val = data.length := by
    rw [hrem_mod, hblocks]
    have := Nat.div_add_mod data.length 128
    omega
  have hrem_lt : remaining.val < 128 := by rw [hrem_mod]; exact Nat.mod_lt _ (by decide)
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
    have hlen : (index_mut_back s2).length = 128 := (index_mut_back s2).property
    omega
  apply spec_bind (Std.Array.index_mut_usize_spec (index_mut_back s2) remaining hbound1)
  rintro ⟨val_at_rem, set_back⟩ ⟨hset_back, hval_at⟩
  set vA : Vector UInt8 128 := Vector.ofFn fun i : Fin 128 =>
    if i.val < remaining.val then (sliceToByteArray data).get! (out.val * 128 + i.val)
    else if i.val = remaining.val then 0x80
    else 0 with hvA_def
  have hfull_match : ∀ (i : Nat) (hi : i < 128),
      toUInt8 ((set_back 128#u8).val[i]'(by simp [(set_back 128#u8).property]; omega)) =
        vA[i]'(by omega) := by
    intro i hi
    have hsb_len : (set_back 128#u8).val.length = 128 := (set_back 128#u8).property
    have hs2v : s2.val = data.val.drop (out.val * 128) := by rw [← hs2_eq, hs1_drop, hi4_v]
    have hs2_len : s2.val.length = data.length - out.val * 128 := by
      rw [hs2v]; simp [List.length_drop]
    have hsb_val : (set_back 128#u8).val =
        ((List.replicate 128 (0#u8 : U8)).setSlice! 0 s2.val).set remaining.val 128#u8 := by
      rw [hset_back]; show (index_mut_back s2).val.set remaining.val (128#u8 : U8) = _
      rw [hd1.2.2 s2, Array.repeat_val]; rfl
    rw [List.Inhabited_getElem_eq_getElem! _ _ (by rw [hsb_len]; exact hi), hsb_val]
    have hvA_get : vA[i]'(by omega) =
        if i < remaining.val then (sliceToByteArray data).get! (out.val * 128 + i)
        else if i = remaining.val then (128 : UInt8) else 0 := by
      show (Vector.ofFn _)[i]'(by omega) = _; rw [Vector.getElem_ofFn]
    rw [hvA_get]
    have hsetSlice_len : ((List.replicate 128 (0#u8 : U8)).setSlice! 0 s2.val).length = 128 := by
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
        have hd_idx : out.val * 128 + i < data.length := by scalar_tac
        rw [getElem!_pos s2.val i hi_in_s2,
          show s2.val[i]'hi_in_s2 = (data.val.drop (out.val * 128))[i]'(hs2v ▸ hi_in_s2)
            from by congr 1, List.getElem_drop]
        show _ = (⟨(data.val.map toUInt8).toArray⟩ : ByteArray).get! (out.val * 128 + i)
        have hda_idx : out.val * 128 + i < (data.val.map toUInt8).toArray.size := by
          simp; exact hd_idx
        rw [show ((⟨(data.val.map toUInt8).toArray⟩ : ByteArray).get! (out.val * 128 + i)) =
            (data.val.map toUInt8).toArray[out.val * 128 + i]! from rfl,
          getElem!_pos (data.val.map toUInt8).toArray (out.val * 128 + i) hda_idx]
        show toUInt8 _ = _; simp [List.getElem_map]
      · have hi_past_s2 : s2.val.length ≤ i := by rw [hs2_len]; omega
        rw [List.getElem!_setSlice!_suffix _ _ 0 i (by simpa),
          List.getElem!_replicate _ (show i < 128 from by omega)]
        show toUInt8 (0#u8 : U8) = _
        rw [if_neg (show ¬ i < remaining.val from by omega), if_neg hieq]; rfl
  /- Total bits bridge: U128 BV equals `BitVec.ofNat 128 (data.length * 8)`. -/
  have htotal_bv : total_bits.bv = BitVec.ofNat 128 (data.length * 8) := by
    have h1 : total_bits.bv = i3.bv <<< 3 := total_bits_post2
    have h2 : i3 = UScalar.cast UScalarTy.U128 data.len := i3_post
    rw [h1, h2]
    have := total_bits_bv_eq_u128_shifted data h
    show ((UScalar.cast UScalarTy.U128 data.len).bv <<< 3) = _
    convert this using 0
  /- Combined: the Aeneas final-block byte at `i ∈ [112..128)` equals the
     Impl byte (either zero for `i < 120` or U64-shift-mask for `i ≥ 120`). -/
  have hlen8 : data.length * 8 < 2 ^ 64 := by
    have h1 : (2 : Nat) ^ 61 * 8 = 2 ^ 64 := by decide
    have h2 : (0 : Nat) < 8 := by decide
    have h3 := (Nat.mul_lt_mul_right h2).mpr h
    omega
  by_cases hge : remaining ≥ 112#usize
  · simp only [hge, ↓reduceIte]
    have hrem_ge112 : 112 ≤ remaining.val := by have hh := hge; scalar_tac
    simp only [lift, bind_tc_ok, bind_assoc]
    set sb1 := (Array.make 1#usize [set_back 128#u8] List.length_singleton).to_slice with hsb1_def
    have hsb1_val : sb1.val = [set_back 128#u8] := by rw [hsb1_def, Array.val_to_slice]; rfl
    apply spec_bind (compress512_spec state sb1)
    intro stateA hstateA
    rw [hsb1_val] at hstateA; simp only [List.foldl_cons, List.foldl_nil] at hstateA
    have hsb_to_vA : arrayU8ToVec (set_back 128#u8) = vA := by
      apply Vector.ext; intro k hk
      have hk128 : k < 128 := by simpa using hk
      rw [arrayU8ToVec_getElem (h := hk128)]; exact hfull_match k hk128
    rw [hsb_to_vA] at hstateA
    set vB : Vector UInt8 128 := Vector.replicate 128 (0 : UInt8) with hvB_def
    have hlow_zero : ∀ (i : Nat) (hi : i < 112),
        toUInt8 ((Array.repeat 128#usize (0#u8 : U8)).val[i]'(by
          simp; omega)) = vB[i]'(by omega) := by
      intro i hi
      have hbyte : (Array.repeat 128#usize (0#u8 : U8)).val[i]'(by
          simp; omega) = (0#u8 : U8) := by
        have hval : (Array.repeat 128#usize (0#u8 : U8)).val = List.replicate 128 (0#u8 : U8) :=
          Array.repeat_val 128#usize (0#u8 : U8)
        conv_lhs => rw [List.Inhabited_getElem_eq_getElem! _ _ (by
          simp; omega)]
        rw [hval, List.getElem!_replicate _ (show i < 128 from by omega)]
      rw [hbyte]
      show toUInt8 (0#u8 : U8) = vB[i]
      rw [hvB_def, Vector.getElem_replicate]
      rfl
    have hpad := padded_block_spec_512 (Array.repeat 128#usize 0#u8) vB hlow_zero total_bits
    show WP.spec (do
        let (s3, index_mut_back2) ←
          core.array.Array.index_mut (core.ops.index.IndexMutSlice
            (core.slice.index.SliceIndexRangeUsizeSlice U8))
            (Array.repeat 128#usize 0#u8) { start := 112#usize, «end» := 128#usize }
        let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3
                   (core.num.U128.to_be_bytes total_bits).to_slice
        let state2 ← Extraction.sha512.compress512 stateA
                       (Array.make 1#usize [index_mut_back2 s5] List.length_singleton).to_slice
        Extraction.sha512_inner_loop1 { start := 0#usize, «end» := 8#usize }
          state2 (Array.repeat 64#usize 0#u8)) _
    rw [padded_block_reshape_512 (Array.repeat 128#usize 0#u8) total_bits
          (fun final_block3 => do
            let state2 ← Extraction.sha512.compress512 stateA
                           (Array.make 1#usize [final_block3] List.length_singleton).to_slice
            Extraction.sha512_inner_loop1 { start := 0#usize, «end» := 8#usize }
              state2 (Array.repeat 64#usize 0#u8))]
    apply spec_bind hpad
    intro fb hfb
    set s6 := (Array.make 1#usize [fb] List.length_singleton).to_slice with hs6_def
    apply spec_bind (compress512_spec stateA s6)
    intro state2 hstate2
    have hs6_val : s6.val = [fb] := by rw [hs6_def, Array.val_to_slice]; rfl
    rw [hs6_val] at hstate2; simp only [List.foldl_cons, List.foldl_nil] at hstate2
    apply spec_mono (sha512_inner_loop1_spec state2 (Array.repeat 64#usize 0#u8))
    intro out hout; rw [hout]
    unfold Local.sha2Inner512 SHS.SHA512.Impl.sha512State
    have hsz : (sliceToByteArray data).size = data.length := by simp
    have hvA_eq : vA = Vector.ofFn (fun k : Fin 128 =>
        if k.val < data.length % 128 then (sliceToByteArray data).get! (data.length / 128 * 128 + k.val)
        else if k.val = data.length % 128 then 128 else 0) := by
      rw [hvA_def, hrem_mod, hblocks]
    /- The Aeneas-side final block: bytes [0..112) = vB (= 0), bytes
       [112..128) = U128 BE shift-mask of total_bits. -/
    have hfb_full : arrayU8ToVec fb =
        Vector.ofFn (fun i : Fin 128 =>
          if i.val < 112 then (0 : UInt8)
          else if i.val < 120 then 0
          else ((data.length.toUInt64 <<< 3 >>> ((127 - i.val) * 8).toUInt64) &&& 255).toUInt8) := by
      rw [hfb]; apply Vector.ext; intro i hi; simp only [Vector.getElem_ofFn]
      by_cases hi112 : i < 112
      · rw [if_pos hi112, if_pos hi112, hvB_def]; simp
      · rw [if_neg hi112, if_neg hi112]
        rw [htotal_bv]
        by_cases hi120 : i < 120
        · rw [if_pos hi120]
          have hk : i - 112 < 8 := by omega
          rw [show (127 - i) = 15 - (i - 112) from by omega]
          exact u128_be_byte_high_zero (data.length * 8) hlen8 (i - 112) hk
        · rw [if_neg hi120]
          have hk_lo : 8 ≤ i - 112 := by omega
          have hk_hi : i - 112 < 16 := by omega
          rw [show (127 - i) = 15 - (i - 112) from by omega]
          rw [u128_be_byte_low_eq_u64 (data.length * 8) hlen8 (i - 112) hk_lo hk_hi]
          /- Bridge `UInt64.ofNat (data.length * 8) = data.length.toUInt64 <<< 3`. -/
          have hbridge_u64 : UInt64.ofNat (data.length * 8) = data.length.toUInt64 <<< 3 := by
            apply UInt64.toBitVec_inj.mp
            show BitVec.ofNat 64 (data.length * 8) = _
            simp only [UInt64.toBitVec_shiftLeft]
            apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_ofNat]
            show data.length * 8 % 2 ^ 64 =
                  ((data.length.toUInt64).toBitVec.toNat <<< ((3 : UInt64).toBitVec.toNat % 64)) % 2 ^ 64
            have h1 : (data.length.toUInt64).toBitVec.toNat = data.length % 2 ^ 64 := rfl
            have h2 : (3 : UInt64).toBitVec.toNat = 3 := rfl
            rw [h1, h2]
            rw [show (3 % 64 : Nat) = 3 from rfl]
            rw [Nat.mod_eq_of_lt (show data.length < 2 ^ 64 by
              have h61 : (2 : Nat) ^ 61 < 2 ^ 64 := by decide
              omega)]
            rw [Nat.shiftLeft_eq]
          rw [hbridge_u64]
    have hstate_prefix : arrayU64ToVec state =
        Fin.foldl (data.length / 128)
          (fun s i => SHS.SHA512.Impl.compress s
            (SHS.SHA512.Impl.toU64sFromBytes (sliceToByteArray data) (i.val * 128)))
          iv_vec := by rw [hstate, ← hblocks]; rfl
    have hstate_full : arrayU64ToVec stateA =
        SHS.SHA512.Impl.compress
          (Fin.foldl (data.length / 128)
            (fun s i => SHS.SHA512.Impl.compress s
              (SHS.SHA512.Impl.toU64sFromBytes (sliceToByteArray data) (i.val * 128)))
            iv_vec)
          (SHS.SHA512.Impl.toU64s (Vector.ofFn (fun k : Fin 128 =>
            if k.val < data.length % 128 then (sliceToByteArray data).get! (data.length / 128 * 128 + k.val)
            else if k.val = data.length % 128 then 128 else 0))) := by
      rw [hstateA, hstate_prefix, ← hvA_eq]
    have hcond : ¬ data.length % 128 < 112 := by rw [← hrem_mod]; simp at hge; omega
    rw [hstate2, hstate_full, hfb_full]; simp only [hsz, if_neg hcond]; rfl
  · simp only [hge, ↓reduceIte]
    have hrem_lt112 : remaining.val < 112 := by simp at hge; scalar_tac
    have hpad := padded_block_spec_512 (set_back 128#u8) vA
      (fun i hi => hfull_match i (by omega)) total_bits
    show WP.spec (do
        let (s3, index_mut_back2) ←
          core.array.Array.index_mut (core.ops.index.IndexMutSlice
            (core.slice.index.SliceIndexRangeUsizeSlice U8))
            (set_back 128#u8) { start := 112#usize, «end» := 128#usize }
        let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3
                   (core.num.U128.to_be_bytes total_bits).to_slice
        let s6 ← lift (Array.to_slice (Array.make 1#usize [index_mut_back2 s5]
                                         List.length_singleton))
        let state2 ← Extraction.sha512.compress512 state s6
        Extraction.sha512_inner_loop1 { start := 0#usize, «end» := 8#usize }
          state2 (Array.repeat 64#usize 0#u8)) _
    rw [padded_block_reshape_512 (set_back 128#u8) total_bits
          (fun final_block3 => do
            let s6 ← lift (Array.to_slice (Array.make 1#usize [final_block3] List.length_singleton))
            let state2 ← Extraction.sha512.compress512 state s6
            Extraction.sha512_inner_loop1 { start := 0#usize, «end» := 8#usize }
              state2 (Array.repeat 64#usize 0#u8))]
    apply spec_bind hpad
    intro fb hfb
    simp only [lift, bind_tc_ok]
    set s6 := (Array.make 1#usize [fb] List.length_singleton).to_slice with hs6_def
    apply spec_bind (compress512_spec state s6)
    intro state2 hstate2
    have hs6_val : s6.val = [fb] := by rw [hs6_def, Array.val_to_slice]; rfl
    rw [hs6_val] at hstate2; simp only [List.foldl_cons, List.foldl_nil] at hstate2
    apply spec_mono (sha512_inner_loop1_spec state2 (Array.repeat 64#usize 0#u8))
    intro out hout; rw [hout]
    unfold Local.sha2Inner512 SHS.SHA512.Impl.sha512State
    have hsz : (sliceToByteArray data).size = data.length := by simp
    apply Vector.ext; intro j hj
    simp only [Vector.getElem_ofFn]
    have hvA_eq : vA = Vector.ofFn (fun k : Fin 128 =>
        if k.val < data.length % 128 then (sliceToByteArray data).get! (data.length / 128 * 128 + k.val)
        else if k.val = data.length % 128 then 128 else 0) := by
      rw [hvA_def, hrem_mod, hblocks]
    have hfb_full : arrayU8ToVec fb =
        Vector.ofFn (fun i : Fin 128 =>
          if i.val < 112 then
            (Vector.ofFn (fun k : Fin 128 =>
              if k.val < data.length % 128 then (sliceToByteArray data).get! (data.length / 128 * 128 + k.val)
              else if k.val = data.length % 128 then 128 else 0))[i]
          else if i.val < 120 then 0
          else ((data.length.toUInt64 <<< 3 >>> ((127 - i.val) * 8).toUInt64) &&& 255).toUInt8) := by
      rw [hfb, ← hvA_eq]; apply Vector.ext; intro i hi; simp only [Vector.getElem_ofFn]
      by_cases hi112 : i < 112
      · rw [if_pos hi112, if_pos hi112]
      · rw [if_neg hi112, if_neg hi112]
        rw [htotal_bv]
        by_cases hi120 : i < 120
        · rw [if_pos hi120]
          have hk : i - 112 < 8 := by omega
          rw [show (127 - i) = 15 - (i - 112) from by omega]
          exact u128_be_byte_high_zero (data.length * 8) hlen8 (i - 112) hk
        · rw [if_neg hi120]
          have hk_lo : 8 ≤ i - 112 := by omega
          have hk_hi : i - 112 < 16 := by omega
          rw [show (127 - i) = 15 - (i - 112) from by omega]
          rw [u128_be_byte_low_eq_u64 (data.length * 8) hlen8 (i - 112) hk_lo hk_hi]
          /- Bridge `UInt64.ofNat (data.length * 8) = data.length.toUInt64 <<< 3`. -/
          have hbridge_u64 : UInt64.ofNat (data.length * 8) = data.length.toUInt64 <<< 3 := by
            apply UInt64.toBitVec_inj.mp
            show BitVec.ofNat 64 (data.length * 8) = _
            simp only [UInt64.toBitVec_shiftLeft]
            apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_ofNat]
            show data.length * 8 % 2 ^ 64 =
                  ((data.length.toUInt64).toBitVec.toNat <<< ((3 : UInt64).toBitVec.toNat % 64)) % 2 ^ 64
            have h1 : (data.length.toUInt64).toBitVec.toNat = data.length % 2 ^ 64 := rfl
            have h2 : (3 : UInt64).toBitVec.toNat = 3 := rfl
            rw [h1, h2]
            rw [show (3 % 64 : Nat) = 3 from rfl]
            rw [Nat.mod_eq_of_lt (show data.length < 2 ^ 64 by
              have h61 : (2 : Nat) ^ 61 < 2 ^ 64 := by decide
              omega)]
            rw [Nat.shiftLeft_eq]
          rw [hbridge_u64]
    have hstate_full : arrayU64ToVec state =
        Fin.foldl (data.length / 128)
          (fun s i => SHS.SHA512.Impl.compress s
            (SHS.SHA512.Impl.toU64sFromBytes (sliceToByteArray data) (i.val * 128)))
          iv_vec := by rw [hstate, ← hblocks]; rfl
    have hcond : data.length % 128 < 112 := by rw [← hrem_mod]; exact hrem_lt112
    rw [hstate2, hstate_full, hfb_full]; simp only [hsz, if_pos hcond]; rfl
