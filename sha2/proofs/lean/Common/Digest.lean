import Common.U8
import equiv.SHA256.Digest
import equiv.SHA256.Padding.ByteDecoding
import equiv.SHA256.Pipeline
import equiv.SHA512.Digest
import equiv.SHA512.Padding.ByteDecoding
import equiv.SHA512.Pipeline

/-!
# Aeneas-side digest and message views

The Aeneas-extracted SHA-2 algorithms return their digest as an
`Array U8 N#usize`; the FIPS-180-4 bitwise spec emits a `BitVec (8·N)`.
This module provides the bridges that let the top-level theorems read
as `digestBitVec (arrayU8ToVec out) = SHS.…sha… (sliceBitMessage data) _`
without inline `let` bindings or `(by …)` proof terms in the
postcondition. -/

open Aeneas Aeneas.Std

/-- Big-endian `BitVec` view of a `Vector UInt8 N` digest.  Generalises the
per-width `SHS.Equiv.SHA{256,512}.Digest.digestBitVec…` family to any `N`. -/
@[inline] def digestBitVec {N : Nat} (d : Vector UInt8 N) : BitVec (8 * N) :=
  SHS.Word.fromBits (d.toList.flatMap fun b => SHS.Equiv.Bytes.byteToBits b)

/-- Aeneas byte slice viewed as a FIPS-180-4 bit message (MSB-first per byte). -/
@[inline] def sliceBitMessage (data : Slice U8) : SHS.Message :=
  SHS.Equiv.SHA256.Padding.ByteDecoding.bytesToBitMessage (sliceToByteArray data)

/-! ## Bit-length bound bridges -/

/-- A byte slice with byte length below `2^61` has bit length below `2^64`
(consumed by SHA-256 / SHA-224 specs). -/
theorem sliceBitMessage_lt_2_64
    (data : Slice U8) (h : data.length < 2 ^ 61) :
    (sliceBitMessage data).length < 2 ^ 64 :=
  SHS.Equiv.SHA256.Pipeline.bitLen_lt_of_size_lt _
    (by simpa [sliceToByteArray_size] using h)

/-- A byte slice with byte length below `2^61` has bit length below `2^128`
(consumed by SHA-512 / SHA-384 / SHA-512/256 / SHA-512/224 specs). -/
theorem sliceBitMessage_lt_2_128
    (data : Slice U8) (h : data.length < 2 ^ 61) :
    (sliceBitMessage data).length < 2 ^ 128 :=
  SHS.Equiv.SHA512.Pipeline.bitLen_lt_of_size_lt _
    (by simpa [sliceToByteArray_size] using h)

/-! ## `digestBitVec` ≡ the per-width fips-pub-180-4 views -/

@[simp] theorem digestBitVec_eq_sha256 (d : Vector UInt8 32) :
    digestBitVec d = SHS.Equiv.SHA256.Digest.digestBitVec d := rfl

@[simp] theorem digestBitVec_eq_sha224 (d : Vector UInt8 28) :
    digestBitVec d = SHS.Equiv.SHA256.Digest.digestBitVec224 d := rfl

@[simp] theorem digestBitVec_eq_sha512 (d : Vector UInt8 64) :
    digestBitVec d = SHS.Equiv.SHA512.Digest.digestBitVec512 d := rfl

@[simp] theorem digestBitVec_eq_sha384 (d : Vector UInt8 48) :
    digestBitVec d = SHS.Equiv.SHA512.Digest.digestBitVec384 d := rfl

@[simp] theorem digestBitVec_eq_sha512_256 (d : Vector UInt8 32) :
    digestBitVec d = SHS.Equiv.SHA512.Digest.digestBitVec512_256 d := rfl

@[simp] theorem digestBitVec_eq_sha512_224 (d : Vector UInt8 28) :
    digestBitVec d = SHS.Equiv.SHA512.Digest.digestBitVec512_224 d := rfl

/-! ## SHA-256 ↔ SHA-512 `bytesToBitMessage` agreement

Both modules in `fips-pub-180-4` define their own `bytesToBitMessage`;
they coincide because both compose `ByteArray.toList` with the same
`byteToBits` expansion.  This lets `sliceBitMessage` (using the SHA-256
namespace) feed the SHA-512 family specs as well. -/

theorem sliceBitMessage_eq_sha512_bytesToBitMessage (data : Slice U8) :
    sliceBitMessage data =
      SHS.Equiv.SHA512.Padding.ByteDecoding.bytesToBitMessage
        (sliceToByteArray data) := rfl
