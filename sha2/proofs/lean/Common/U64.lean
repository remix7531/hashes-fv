import Aeneas
import Common.U8

/-!
# Word-size-agnostic 64-bit helpers: Aeneas `Std.U64` ↔ Lean core `UInt64`

Mirrors `Common/U8.lean` and the `toUInt32`/`fromUInt32` bridge in
`U32.lean`. These conversions are width-agnostic — they are used by
SHA-256 (length-tag emit), SHA-512 (state words), and the four
truncated variants (SHA-384, SHA-512/256, SHA-512/224, SHA-224) alike.

The BE byte-extraction lemma `toUInt8_be_byte` for `U64` is also shared:
SHA-256's `FinalBlock` uses it to refine the `[56, 64)` length-tag
layout, and SHA-512's `Loop1` uses it to refine the per-byte BE emit
in the digest finalization. The U32 and U128 width-specific variants
live in `Sha256/Loop1.lean` and `Sha512/FinalBlock.lean` respectively.
-/

open Aeneas Aeneas.Std

/-! ## Scalar conversions -/

@[inline] def toUInt64 (x : U64) : UInt64 := ⟨x.bv⟩
@[inline] def fromUInt64 (x : UInt64) : U64 := ⟨x.toBitVec⟩

@[simp] theorem toUInt64_bv (x : U64) : (toUInt64 x).toBitVec = x.bv := rfl
@[simp] theorem fromUInt64_bv (x : UInt64) : (fromUInt64 x).bv = x.toBitVec := rfl

@[simp] theorem toUInt64_fromUInt64 (x : UInt64) : toUInt64 (fromUInt64 x) = x := rfl
@[simp] theorem fromUInt64_toUInt64 (x : U64) : fromUInt64 (toUInt64 x) = x := rfl

/-! ## BE-byte extraction for `U64`

Reduces to the upstream-Aeneas lemma `BitVec.toBEBytes_getElem!_eq_shift_mask`,
which expresses byte `i` of `bv.toBEBytes` as a width-generic shift-and-mask. -/

/-- Byte `i` (`i < 8`) of the BE-encoding of a `U64` equals the
shift-and-mask form `((toUInt64 total_bits >>> ((7-i)*8)) &&& 0xff).toUInt8`.
Used by both SHA-256's `FinalBlock` (length-tag refinement) and SHA-512's
`Loop1` (digest finalization). -/
theorem toUInt8_be_byte (total_bits : U64) (i : Nat) (hi : i < 8) :
    toUInt8 ((total_bits.bv.toBEBytes.map (UScalar.mk (ty := .U8)) : List U8)[i]!) =
      ((toUInt64 total_bits >>> (UInt64.ofNat ((7 - i) * 8))) &&& 0xff).toUInt8 := by
  have hmap : (total_bits.bv.toBEBytes.map (UScalar.mk (ty := .U8)) : List U8)[i]! =
              UScalar.mk (ty := .U8) (total_bits.bv.toBEBytes[i]!) := by
    simp [getElem!_pos, BitVec.toBEBytes_length total_bits.bv (by decide), hi, List.getElem_map]
  rw [hmap]; apply UInt8.toBitVec_inj.mp
  show total_bits.bv.toBEBytes[i]! = _
  rw [BitVec.toBEBytes_getElem!_eq_shift_mask (n := 64) (by decide) total_bits.bv i
        (by simpa using hi), show (64 / 8 - 1 - i) = (7 - i) from by omega]
  show _ = ((((toUInt64 total_bits >>> (UInt64.ofNat ((7 - i) * 8))) &&& 0xff)).toBitVec).setWidth 8
  fcongr 1
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_shiftRight]
  have h2 : ((UInt64.ofNat ((7 - i) * 8)).toBitVec % 64 : BitVec 64) =
            BitVec.ofNat 64 ((7 - i) * 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_umod, BitVec.toNat_ofNat,
      show (UInt64.ofNat ((7 - i) * 8)).toBitVec = BitVec.ofNat 64 ((7 - i) * 8) from rfl]
    rw [show (64 : BitVec 64).toNat = 64 from rfl]; omega
  rw [h2, show UInt64.toBitVec 255 = (BitVec.ofNat 64 0xff) from rfl,
      show (toUInt64 total_bits).toBitVec = total_bits.bv from rfl]
  fcongr 1
  show _ = total_bits.bv >>> (BitVec.ofNat 64 ((7 - i) * 8)).toNat
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
