import U32
import Aeneas

/-!
# Padding-block byte-equality bridge for SHA-256's final block

The Aeneas extraction (`Extraction.sha256_inner`) builds the FIPS 180-4 §5.1.1
padded final block in four regions: data copy `[0, remaining)`, the
`0x80` marker at `remaining`, zeros up to byte 56, then the BE-encoded
bit-length at `[56, 64)`. The Impl-side spec
(`SHS.SHA256.Impl.sha256` in `fips-180-4-lean/impl/SHA256.lean`)
materializes the same regions via three `Vector.ofFn` snapshots
(`finalBlockA` after the marker write, `finalBlockB` post-branch, and
`finalBlockC` after the length-tag write).

This file's load-bearing lemma is `u64_be_bytes_match`: the `i`-th byte
of `core.num.U64.to_be_bytes total_bits` (Aeneas) equals
`((toUInt64 total_bits >>> ((63 - (56 + i)) * 8)) &&& 0xff).toUInt8`
(Impl-side `finalBlockC` byte at index `56 + i`).

The shared lemma `BitVec.toBEBytes_getElem!_eq_shift_mask` (used here and
in `Loop1`) provides the width-generic core: byte `i` of
`bv.toBEBytes` is the `i`-th big-endian shift-and-mask of `bv`.
-/



open Aeneas Aeneas.Std Result WP SHS.SHA256

/-! ## `UInt64`/`U64` scalar bridge

Mirrors `toUInt32`/`fromUInt32` from `U32.lean`. -/

@[inline] def toUInt64 (x : U64) : UInt64 := ⟨x.bv⟩
@[inline] def fromUInt64 (x : UInt64) : U64 := ⟨x.toBitVec⟩

@[simp] theorem toUInt64_bv (x : U64) : (toUInt64 x).toBitVec = x.bv := rfl
@[simp] theorem fromUInt64_bv (x : UInt64) : (fromUInt64 x).bv = x.toBitVec := rfl

@[simp] theorem toUInt64_fromUInt64 (x : UInt64) : toUInt64 (fromUInt64 x) = x := rfl
@[simp] theorem fromUInt64_toUInt64 (x : U64) : fromUInt64 (toUInt64 x) = x := rfl

/-! ## BE-byte layout of `core.num.U64.to_be_bytes`

Reduces to the upstream-Aeneas lemma `BitVec.toBEBytes_getElem!_eq_shift_mask`,
which expresses byte `i` of `bv.toBEBytes` as a width-generic shift-and-mask. -/

/-- Byte `i` (`i < 8`) of the BE-encoding of a `U64` equals the
shift-and-mask form `((toUInt64 total_bits >>> ((7-i)*8)) &&& 0xff).toUInt8`. -/
theorem toUInt8_be_byte (total_bits : U64) (i : Nat) (hi : i < 8) :
    toUInt8 ((total_bits.bv.toBEBytes.map (UScalar.mk (ty := .U8)) : List U8)[i]!) =
      ((toUInt64 total_bits >>> (UInt64.ofNat ((7 - i) * 8))) &&& 0xff).toUInt8 := by
  have hlen_be : total_bits.bv.toBEBytes.length = 8 :=
    BitVec.toBEBytes_length total_bits.bv (by decide)
  have hmap : (total_bits.bv.toBEBytes.map (UScalar.mk (ty := .U8)) : List U8)[i]! =
              UScalar.mk (ty := .U8) (total_bits.bv.toBEBytes[i]!) := by
    simp [getElem!_pos, hlen_be, hi, List.getElem_map]
  rw [hmap]
  apply UInt8.toBitVec_inj.mp
  show total_bits.bv.toBEBytes[i]! = _
  rw [BitVec.toBEBytes_getElem!_eq_shift_mask (n := 64) (by decide) total_bits.bv i
        (by simpa using hi)]
  rw [show (64 / 8 - 1 - i) = (7 - i) from by omega]
  show _ = ((((toUInt64 total_bits >>> (UInt64.ofNat ((7 - i) * 8))) &&& 0xff)).toBitVec).setWidth 8
  congr 1
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_shiftRight]
  have hk_lt : (7 - i) * 8 < 64 := by omega
  have h2 : ((UInt64.ofNat ((7 - i) * 8)).toBitVec % 64 : BitVec 64) =
            BitVec.ofNat 64 ((7 - i) * 8) := by
    have heq : (UInt64.ofNat ((7 - i) * 8)).toBitVec = BitVec.ofNat 64 ((7 - i) * 8) := rfl
    rw [heq]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_umod, BitVec.toNat_ofNat]
    rw [show (64 : BitVec 64).toNat = 64 from rfl]; omega
  have h3 : UInt64.toBitVec 255 = (BitVec.ofNat 64 0xff) := rfl
  have h1 : (toUInt64 total_bits).toBitVec = total_bits.bv := rfl
  rw [h2, h3, h1]
  show total_bits.bv >>> ((7 - i) * 8) &&& BitVec.ofNat 64 0xff =
       total_bits.bv >>> (BitVec.ofNat 64 ((7 - i) * 8)) &&& BitVec.ofNat 64 0xff
  congr 1
  show _ = total_bits.bv >>> (BitVec.ofNat 64 ((7 - i) * 8)).toNat
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-! ## Consumer-facing form

The Impl side indexes the BE length bytes at `i` for `56 ≤ i < 64` via
`((totalBits >>> ((63 - i) * 8)) &&& 0xff).toUInt8`. With `i = 56 + k`
(`k < 8`), `63 - i = 7 - k`, matching the Aeneas-side `to_be_bytes`
position `k`. -/

theorem u64_be_bytes_match (total_bits : U64) (k : Nat) (hk : k < 8) :
    toUInt8 ((core.num.U64.to_be_bytes total_bits).val[k]!) =
      ((toUInt64 total_bits >>> (UInt64.ofNat ((63 - (56 + k)) * 8))) &&& 0xff).toUInt8 := by
  show toUInt8 ((total_bits.bv.toBEBytes.map (UScalar.mk (ty := .U8)) : List U8)[k]!) = _
  rw [toUInt8_be_byte total_bits k hk, show 63 - (56 + k) = 7 - k from by omega]

/-- The BV-shift on the U64-cast of `Slice.len data` agrees with the
Impl-side `data.size.toUInt64 <<< 3`. Pure scalar identity; the
length bound argument is unused but kept for caller symmetry. -/
theorem total_bits_bv_eq (data : Slice U8) (_h : data.length < 2 ^ 61) :
    ((UScalar.cast .U64 (Slice.len data)).bv <<< (3 : Nat)) =
      ((sliceToByteArray data).size.toUInt64 <<< 3).toBitVec := by
  show ((Slice.len data).bv.zeroExtend 64) <<< 3 = _
  rw [sliceToByteArray_size]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft]

/-- Byte-by-byte equality between the Aeneas-side
final block (post the `[56..64] ← to_be_bytes total_bits` write) and
the Impl-side `finalBlockC`.

**Contract.** Suppose `finalBlockB_bytes : Array U8 64#usize` has its
low 56 bytes (indices `0..56`) matching the spec's `finalBlockB`
post-branch shape (i.e. either `finalBlockA` in the <-arm, or all
zeros in the ≥-arm). Specifically, abstracted over the `finalBlockB`
spec value `vB : Vector UInt8 64`:

  ∀ i < 56, toUInt8 finalBlockB_bytes.val[i]! = vB[i]

Then after writing the 8 BE bytes of `total_bits` into indices
`[56, 64)`, the resulting array's `arrayU8ToVec` view equals the
spec's `finalBlockC` built from `vB` and `total_bits`.

This is the load-bearing combinatorial lemma: it walks through one
`core.array.Array.index_mut` (range `[56..64]`) + `to_be_bytes` +
`copy_from_slice` + `index_mut_back` chain, using
`u64_be_bytes_match` for the per-byte BE equality. -/
theorem padded_block_spec
    (finalBlockB_bytes : Array U8 64#usize)
    (vB : Vector UInt8 64)
    (hlow : ∀ (i : Nat) (hi : i < 56),
        toUInt8 (finalBlockB_bytes.val[i]'(by simp [finalBlockB_bytes.property]; omega)) =
          vB[i]'(by omega))
    (total_bits : U64) :
    (do
      let __discr ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice U8)) finalBlockB_bytes
          { start := 56#usize, «end» := 64#usize }
      let a ← lift (core.num.U64.to_be_bytes total_bits)
      let s4 ← lift (Array.to_slice a)
      let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 __discr.1 s4
      ok (__discr.2 s5) : Result (Array U8 64#usize))
    ⦃ final_block3 => arrayU8ToVec final_block3 =
        (Vector.ofFn fun i : Fin 64 =>
          if i.val < 56 then vB[i]
          else ((toUInt64 total_bits >>>
                  (UInt64.ofNat ((63 - i.val) * 8))) &&& 0xff).toUInt8) ⦄ := by
  -- Walks `index_mut [56..64]` + `to_be_bytes` + `copy_from_slice` +
  -- `index_mut_back`, then `Vector.ext`. For `i < 56` both sides equal
  -- `vB[i]`; for `56 ≤ i < 64` they agree via `u64_be_bytes_match`.
  unfold core.array.Array.index_mut core.ops.index.IndexMutSlice
    core.slice.index.Slice.index_mut
    core.slice.index.SliceIndexRangeUsizeSlice
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut Array.to_slice
    core.slice.Slice.copy_from_slice
  have hfb_len : finalBlockB_bytes.val.length = 64 := finalBlockB_bytes.property
  simp only [show (56#usize : Usize) ≤ 64#usize ∧
      (↑(64#usize : Usize) : ℕ) ≤ finalBlockB_bytes.val.length
      from ⟨by decide, by simp [hfb_len]⟩,
    bind_tc_ok, lift, and_self, ↓reduceIte]
  have hlen_eq : Slice.len (⟨List.slice (↑(56#usize : Usize) : Nat) (↑(64#usize : Usize) : Nat)
        finalBlockB_bytes.val, by scalar_tac⟩ : Slice U8) =
      Slice.len (⟨(core.num.U64.to_be_bytes total_bits).val, by scalar_tac⟩ : Slice U8) := by
    apply UScalar.eq_of_val_eq; simp [List.slice, hfb_len]
  simp only [hlen_eq, ↓reduceIte, bind_tc_ok, spec, theta, wp_return]
  simp only [Array.from_slice]
  have hsetSlice_len : ((finalBlockB_bytes.val).setSlice!
      (↑(56#usize : Usize) : Nat) (core.num.U64.to_be_bytes total_bits).val).length =
      (64#usize : Usize).val := by
    simp [hfb_len]
  simp only [show ((finalBlockB_bytes.val).setSlice!
      (↑(56#usize : Usize) : Nat) (core.num.U64.to_be_bytes total_bits).val).length =
      (64#usize : Usize).val from hsetSlice_len, ↓reduceDIte]
  apply Vector.toArray_inj.mp
  rw [Vector.toArray_ofFn]
  show (((finalBlockB_bytes.val.setSlice! 56 (core.num.U64.to_be_bytes total_bits).val).map
      toUInt8).toArray : Array UInt8) = _
  apply Array.ext
  · simp
  intro k h1 _
  rw [Array.getElem_ofFn]
  have hk : k < 64 := by simp at h1; omega
  have hlen : (finalBlockB_bytes.val.setSlice! 56
      (core.num.U64.to_be_bytes total_bits).val).length = 64 := by simp [hfb_len]
  rw [List.getElem_toArray, List.getElem_map, ← getElem!_pos _ _ (by rw [hlen]; exact hk)]
  by_cases hk56 : k < 56
  · rw [List.getElem!_setSlice!_prefix _ _ 56 k hk56]
    show toUInt8 (finalBlockB_bytes.val[k]!) = _
    rw [getElem!_pos finalBlockB_bytes.val k (by omega)]
    show _ = if (⟨k, hk⟩ : Fin 64).val < 56 then _ else _
    rw [if_pos (show (⟨k, hk⟩ : Fin 64).val < 56 from hk56)]
    exact hlow k hk56
  · push Not at hk56
    rw [List.getElem!_setSlice!_middle _ _ 56 k
      (by refine ⟨hk56, ?_, ?_⟩
          · simp; omega
          · omega)]
    show _ = if (⟨k, hk⟩ : Fin 64).val < 56 then _ else _
    rw [if_neg (show ¬ (⟨k, hk⟩ : Fin 64).val < 56 from by simp; omega)]
    show toUInt8 ((core.num.U64.to_be_bytes total_bits).val[k - 56]!) =
        ((toUInt64 total_bits >>> UInt64.ofNat ((63 - (⟨k, hk⟩ : Fin 64).val) * 8))
          &&& 255).toUInt8
    have hk' : k - 56 < 8 := by omega
    rw [u64_be_bytes_match total_bits (k - 56) hk']
    show _ = ((toUInt64 total_bits >>> UInt64.ofNat ((63 - k) * 8)) &&& 255).toUInt8
    rw [show 63 - (56 + (k - 56)) = 63 - k from by omega]


