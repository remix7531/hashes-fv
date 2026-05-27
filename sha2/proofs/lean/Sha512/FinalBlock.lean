import Word.U64

/-!
# Padding-block byte-equality bridge for SHA-512's final block

The Aeneas extraction (`Extraction.sha512_inner`) builds the FIPS 180-4
§5.1.2 padded final block in four regions: data copy `[0, remaining)`,
the `0x80` marker at `remaining`, zeros up to byte 112, then a 16-byte
length tag at `[112, 128)` (the high 8 bytes are zero — see file docstring
in `impl/SHA512.lean` for the U128-without-UInt128 trick).

The U64-width BE-byte extraction lemma `toUInt8_be_byte` lives in
`Common/U64.lean` (shared with SHA-256's `FinalBlock`); this file
adds the U128 sibling `toUInt8_be_byte_U128` and the `padded_block_spec_512`
top-level lemma for the SHA-512 final block.
-/

open Aeneas Aeneas.Std Result WP SHS.SHA512

/-- Byte `i` (`i < 16`) of the BE-encoding of a `U128`, in the canonical
shift-and-mask form returned by `BitVec.toBEBytes_getElem!_eq_shift_mask`. -/
theorem toUInt8_be_byte_U128 (total_bits : U128) (i : Nat) (hi : i < 16) :
    toUInt8 ((total_bits.bv.toBEBytes.map (UScalar.mk (ty := .U8)) : List U8)[i]!) =
      ⟨BitVec.setWidth 8 ((total_bits.bv >>> ((15 - i) * 8)) &&& BitVec.ofNat 128 0xff)⟩ := by
  have hlen_be : total_bits.bv.toBEBytes.length = 16 :=
    BitVec.toBEBytes_length total_bits.bv (by decide)
  have hmap : (total_bits.bv.toBEBytes.map (UScalar.mk (ty := .U8)) : List U8)[i]! =
              UScalar.mk (ty := .U8) (total_bits.bv.toBEBytes[i]!) := by
    simp [getElem!_pos, hlen_be, hi, List.getElem_map]
  rw [hmap]; apply UInt8.toBitVec_inj.mp
  show total_bits.bv.toBEBytes[i]! = _
  rw [BitVec.toBEBytes_getElem!_eq_shift_mask (n := 128) (by decide) total_bits.bv i
        (by simpa using hi)]

/-- Consumer-facing form: indexing `core.num.U128.to_be_bytes` directly,
matching the layout used by `padded_block_spec_512`. -/
theorem u128_be_bytes_match (total_bits : U128) (k : Nat) (hk : k < 16) :
    toUInt8 ((core.num.U128.to_be_bytes total_bits).val[k]!) =
      ⟨BitVec.setWidth 8 ((total_bits.bv >>> ((127 - (112 + k)) * 8)) &&&
        BitVec.ofNat 128 0xff)⟩ := by
  show toUInt8 ((total_bits.bv.toBEBytes.map (UScalar.mk (ty := .U8)) : List U8)[k]!) = _
  rw [toUInt8_be_byte_U128 total_bits k hk,
      show 127 - (112 + k) = 15 - k from by omega]

/-! ## The U128 length-tag cast bridge

When `data.length < 2^61`, `(UScalar.cast .U128 (Slice.len data)).bv <<< 3`
equals the 128-bit `BitVec` of `data.length * 8`.  This is the key bridge
for the U128-without-UInt128 trick: the high 8 bytes of
`(data.len.U128 <<< 3).toBEBytes` are unconditionally zero, and the low 8
bytes match the U64 BE-encoding of `data.length * 8`. -/

/-- Cast-shift form: `(UScalar.cast .U128 (Slice.len data)).bv <<< 3` equals
the 128-bit BV of `data.length * 8`. -/
theorem total_bits_bv_eq_u128_shifted (data : Slice U8) (h : data.length < 2 ^ 61) :
    ((UScalar.cast .U128 (Slice.len data)).bv <<< (3 : Nat)) =
      BitVec.ofNat 128 (data.length * 8) := by
  show ((Slice.len data).bv.zeroExtend 128) <<< 3 = _
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [show (Slice.len data).bv.toNat = data.length from rfl,
      Nat.mod_eq_of_lt (show data.length < 2 ^ 128 by
        have : (2 : Nat) ^ 61 < 2 ^ 128 := by decide
        omega)]
  show data.length <<< 3 % 2 ^ 128 = data.length * 8 % 2 ^ 128
  rw [Nat.shiftLeft_eq, show (2 ^ 3 : Nat) = 8 from rfl]

/-- Spec-level shape of the padded final block once both Aeneas and Impl
have written: data prefix, `0x80` marker, zero-fill, then the BE-emitted
length tag at byte range `[112, 128)`.

128-byte analogue of `Sha256/FinalBlock.lean::padded_block_spec`.  The
final block has 16-byte length tag (instead of 8); positions `[112..120)`
hold the high 8 bytes of the U128 (zero when `data.length < 2^61`) and
positions `[120..128)` hold the low 8 bytes (the U64 BE-encoding of
`data.length * 8`). -/
theorem padded_block_spec_512
    (finalBlockB_bytes : Array U8 128#usize)
    (vB : Vector UInt8 128)
    (hlow : ∀ (i : Nat) (hi : i < 112),
        toUInt8 (finalBlockB_bytes.val[i]'(by simp [finalBlockB_bytes.property]; omega)) =
          vB[i]'(by omega))
    (total_bits : U128) :
    (do
      let __discr ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice U8)) finalBlockB_bytes
          { start := 112#usize, «end» := 128#usize }
      let a ← lift (core.num.U128.to_be_bytes total_bits)
      let s4 ← lift (Array.to_slice a)
      let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 __discr.1 s4
      ok (__discr.2 s5) : Result (Array U8 128#usize))
    ⦃ final_block3 => arrayU8ToVec final_block3 =
        (Vector.ofFn fun i : Fin 128 =>
          if i.val < 112 then vB[i]
          else ⟨BitVec.setWidth 8
                  ((total_bits.bv >>> ((127 - i.val) * 8)) &&&
                    BitVec.ofNat 128 0xff)⟩) ⦄ := by
  unfold core.array.Array.index_mut core.ops.index.IndexMutSlice
    core.slice.index.Slice.index_mut
    core.slice.index.SliceIndexRangeUsizeSlice
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut Array.to_slice
    core.slice.Slice.copy_from_slice
  have hfb_len : finalBlockB_bytes.val.length = 128 := finalBlockB_bytes.property
  simp only [show (112#usize : Usize) ≤ 128#usize ∧
      (↑(128#usize : Usize) : ℕ) ≤ finalBlockB_bytes.val.length
      from ⟨by decide, by simp [hfb_len]⟩,
    bind_tc_ok, lift, and_self, ↓reduceIte]
  have hlen_eq : Slice.len (⟨List.slice (↑(112#usize : Usize) : Nat) (↑(128#usize : Usize) : Nat)
        finalBlockB_bytes.val, by scalar_tac⟩ : Slice U8) =
      Slice.len (⟨(core.num.U128.to_be_bytes total_bits).val, by scalar_tac⟩ : Slice U8) := by
    apply UScalar.eq_of_val_eq; simp [List.slice, hfb_len]
  simp only [hlen_eq, ↓reduceIte, bind_tc_ok, spec, theta, wp_return, Array.from_slice]
  have hsetSlice_len : ((finalBlockB_bytes.val).setSlice!
      (↑(112#usize : Usize) : Nat) (core.num.U128.to_be_bytes total_bits).val).length =
      (128#usize : Usize).val := by simp [hfb_len]
  simp only [hsetSlice_len, ↓reduceDIte]
  apply Vector.toArray_inj.mp; rw [Vector.toArray_ofFn]
  show (((finalBlockB_bytes.val.setSlice! 112 (core.num.U128.to_be_bytes total_bits).val).map
      toUInt8).toArray : Array UInt8) = _
  apply Array.ext (h₁ := by simp)
  intro k h1 _
  have hk : k < 128 := by simp at h1; omega
  rw [Array.getElem_ofFn, List.getElem_toArray, List.getElem_map,
      ← getElem!_pos _ _ (by simp [hfb_len]; exact hk)]
  by_cases hk112 : k < 112
  · rw [List.getElem!_setSlice!_prefix _ _ 112 k hk112]
    show toUInt8 (finalBlockB_bytes.val[k]!) = _
    rw [getElem!_pos finalBlockB_bytes.val k (by omega)]
    show _ = if (⟨k, hk⟩ : Fin 128).val < 112 then _ else _
    rw [if_pos (show (⟨k, hk⟩ : Fin 128).val < 112 from hk112)]; exact hlow k hk112
  · push Not at hk112
    rw [List.getElem!_setSlice!_middle _ _ 112 k (⟨hk112, by simp; omega, by omega⟩)]
    show _ = if (⟨k, hk⟩ : Fin 128).val < 112 then _ else _
    rw [if_neg (show ¬ (⟨k, hk⟩ : Fin 128).val < 112 from by simp; omega),
        u128_be_bytes_match total_bits (k - 112) (by omega)]
    show (⟨BitVec.setWidth 8 ((total_bits.bv >>> ((127 - (112 + (k - 112))) * 8)) &&&
            BitVec.ofNat 128 0xff)⟩ : UInt8) =
         (⟨BitVec.setWidth 8 ((total_bits.bv >>> ((127 - k) * 8)) &&&
            BitVec.ofNat 128 0xff)⟩ : UInt8)
    rw [show 127 - (112 + (k - 112)) = 127 - k from by omega]

/-! ## Bridge between the 128-bit BE-byte form and the U64 BE-byte form

When `n < 2^64`, the U128 BE-encoding of `n` is 8 zero bytes followed by
the U64 BE-encoding of `n`.  We use this to bridge between the Aeneas-side
`total_bits` (a `U128`) and the Impl-side `totalBits` (a `UInt64`). -/

/-- For `n < 2 ^ 64` and `k < 8`, the byte at position `112 + k` of the
U128 BE-encoding of `n` is zero. -/
theorem u128_be_byte_high_zero (n : Nat) (hn : n < 2 ^ 64) (k : Nat) (hk : k < 8) :
    (⟨BitVec.setWidth 8 ((BitVec.ofNat 128 n >>> ((15 - k) * 8)) &&&
        BitVec.ofNat 128 0xff)⟩ : UInt8) = 0 := by
  apply UInt8.toBitVec_inj.mp
  show BitVec.setWidth 8 ((BitVec.ofNat 128 n >>> ((15 - k) * 8)) &&&
        BitVec.ofNat 128 0xff) = 0#8
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat]
  have hn_shifted : n >>> ((15 - k) * 8) = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (by omega)))
  rw [Nat.mod_eq_of_lt (show n < 2^128 by
        have : (2:Nat) ^ 64 < 2 ^ 128 := by decide
        omega),
      show ((0xff : Nat) % 2 ^ 128) = 0xff from by decide, hn_shifted]
  simp

/-- For `n < 2 ^ 64` and `k ∈ [8..16)`, the byte at position `112 + k` of
the U128 BE-encoding of `n` equals the byte at position `k - 8` of the
U64 BE-encoding of `n.toUInt64`. -/
theorem u128_be_byte_low_eq_u64 (n : Nat) (hn : n < 2 ^ 64) (k : Nat)
    (_hk_lo : 8 ≤ k) (_hk_hi : k < 16) :
    (⟨BitVec.setWidth 8 ((BitVec.ofNat 128 n >>> ((15 - k) * 8)) &&&
        BitVec.ofNat 128 0xff)⟩ : UInt8) =
      (((UInt64.ofNat n) >>> ((15 - k) * 8).toUInt64) &&& 0xff).toUInt8 := by
  apply UInt8.toBitVec_inj.mp
  show BitVec.setWidth 8 ((BitVec.ofNat 128 n >>> ((15 - k) * 8)) &&&
        BitVec.ofNat 128 0xff) = _
  show _ = (((UInt64.ofNat n) >>> ((15 - k) * 8).toUInt64) &&& 0xff).toBitVec.setWidth 8
  apply BitVec.eq_of_toNat_eq
  have hshift_lt : (15 - k) * 8 < 64 := by omega
  have h128lt : n < 2 ^ 128 := by
    have : (2:Nat) ^ 64 < 2 ^ 128 := by decide
    omega
  have hand_eq : n >>> ((15 - k) * 8) &&& 0xff = n >>> ((15 - k) * 8) % 256 := by
    rw [show (0xff : Nat) = 256 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod (n := 8)]
  have hand_lt : n >>> ((15 - k) * 8) &&& 0xff < 2 ^ 8 := by
    rw [hand_eq]; exact Nat.mod_lt _ (by decide)
  /- Compute LHS as Nat -/
  have hLHS : (BitVec.setWidth 8 ((BitVec.ofNat 128 n >>> ((15 - k) * 8)) &&&
                  BitVec.ofNat 128 0xff)).toNat = (n >>> ((15 - k) * 8)) % 256 := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ushiftRight,
      BitVec.toNat_ofNat]
    rw [show ((0xff : Nat) % 2 ^ 128) = 0xff from by decide, Nat.mod_eq_of_lt h128lt,
        Nat.mod_eq_of_lt hand_lt, hand_eq]
  /- Compute RHS as Nat -/
  have hRHS : ((((UInt64.ofNat n) >>> ((15 - k) * 8).toUInt64) &&&
                  0xff).toBitVec.setWidth 8).toNat = (n >>> ((15 - k) * 8)) % 256 := by
    simp only [BitVec.toNat_setWidth, UInt64.toBitVec_and, UInt64.toBitVec_shiftRight,
      BitVec.toNat_and]
    have hcast_shift_nat :
        (((15 - k) * 8).toUInt64.toBitVec % (64 : BitVec 64)).toNat = (15 - k) * 8 := by
      simp only [BitVec.toNat_umod]
      rw [show (64 : BitVec 64).toNat = 64 from rfl]
      show ((15 - k) * 8) % 2 ^ 64 % 64 = (15 - k) * 8
      rw [Nat.mod_eq_of_lt (by omega : (15 - k) * 8 < 2 ^ 64), Nat.mod_eq_of_lt hshift_lt]
    /- The BV >>> BV reduces to BV >>> .toNat -/
    rw [show ((UInt64.ofNat n).toBitVec >>>
              (((15 - k) * 8).toUInt64.toBitVec % 64) : BitVec 64) =
            ((UInt64.ofNat n).toBitVec >>>
              (((15 - k) * 8).toUInt64.toBitVec % (64 : BitVec 64)).toNat : BitVec 64)
        from rfl,
        BitVec.toNat_ushiftRight, hcast_shift_nat,
        show ((UInt64.ofNat n).toBitVec.toNat) = n % 2 ^ 64 from rfl,
        show ((255 : UInt64).toBitVec.toNat) = 255 from rfl,
        Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hand_lt, hand_eq]
  rw [hLHS, hRHS]

/-! ## Iota-reshape for `padded_block_spec_512` consumers

Both arms of the `remaining ≥ 112` branch in `Sha512/InnerSpec.lean` need to
reshape the `do`-block so the prefix matches `padded_block_spec_512`'s
statement (which uses `lift (core.num.U128.to_be_bytes total_bits)` and
`lift (Array.to_slice a)`). This is a pure monadic-laws rewrite — both
sides reduce to the same `bind`-tree once `lift` is unfolded. -/

/-- The fused `index_mut`-then-`copy_from_slice` `do`-block equals the
explicit `lift`-decomposed prefix used by `padded_block_spec_512`, threaded
through an arbitrary continuation `k`. -/
theorem padded_block_reshape_512 {α : Type}
    (fb_initial : Array U8 128#usize) (total_bits : U128)
    (k : Array U8 128#usize → Result α) :
    (do
      let (s3, index_mut_back2) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice U8))
          fb_initial { start := 112#usize, «end» := 128#usize }
      let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3
                 (core.num.U128.to_be_bytes total_bits).to_slice
      k (index_mut_back2 s5))
    = ((do
        let __discr ←
          core.array.Array.index_mut (core.ops.index.IndexMutSlice
            (core.slice.index.SliceIndexRangeUsizeSlice U8))
            fb_initial { start := 112#usize, «end» := 128#usize }
        let a ← lift (core.num.U128.to_be_bytes total_bits)
        let s4 ← lift (Array.to_slice a)
        let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 __discr.1 s4
        ok (__discr.2 s5)) >>= k) := by
  simp [lift, bind_tc_ok]
