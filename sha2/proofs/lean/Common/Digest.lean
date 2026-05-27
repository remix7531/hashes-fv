import Common.U8
import equiv.SHA256.Digest
import equiv.SHA256.Padding.ByteDecoding
import equiv.SHA256.Pipeline
import equiv.SHA512.Digest
import equiv.SHA512.Padding.ByteDecoding
import equiv.SHA512.Pipeline

/-!
# Bytes <-> bits conversion

Single primitive `bytesToBits : List U8 -> SHS.Message` (MSB-first per
byte, FIPS 180-4 Sec. 3.1).  Both the input (slice payload) and output
(digest array payload) sides of every `<algo>_spec` theorem flow
through this one function.  `SHS.Word.fromBits` (upstream,
`spec/Setup.lean`) wraps the bit list into a `BitVec N` for the
digest side.

The bridges in this file connect our `bytesToBits` / `Word.fromBits`
forms to the per-namespace upstream `bytesToBitMessage` and per-width
`digestBitVec...` family consumed by `SHS.Equiv.SHA{256,512}.<algo>_correct`. -/

open Aeneas Aeneas.Std

/-- MSB-first FIPS-180-4 bit representation of an Aeneas byte list. -/
@[inline] def bytesToBits (bs : List U8) : SHS.Message :=
  bs.flatMap fun b => SHS.Equiv.Bytes.byteToBits (toUInt8 b)

/-! ## Length -/

@[simp] theorem bytesToBits_length (bs : List U8) :
    (bytesToBits bs).length = 8 * bs.length := by
  unfold bytesToBits
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.flatMap_cons, List.length_append,
               SHS.Equiv.Bytes.byteToBits_length, List.length_cons]
    omega

theorem bytesToBits_length_lt_2_64 (bs : List U8) (h : bs.length < 2 ^ 61) :
    (bytesToBits bs).length < 2 ^ 64 := by
  rw [bytesToBits_length]; omega

theorem bytesToBits_length_lt_2_128 (bs : List U8) (h : bs.length < 2 ^ 61) :
    (bytesToBits bs).length < 2 ^ 128 := by
  rw [bytesToBits_length]; omega

/-! ## Bridges to upstream forms

These lemmas let the `<algo>_spec` proofs rewrite our `bytesToBits` /
`Word.fromBits` forms into the upstream `bytesToBitMessage` /
`digestBitVec...` forms produced by `SHS.Equiv.SHA{256,512}.<algo>_correct`. -/

/-- `bytesToBits` over a slice payload matches the upstream SHA-256
`bytesToBitMessage` view of the same slice (via `sliceToByteArray`). -/
theorem bytesToBits_eq_sha256_bytesToBitMessage (data : Slice U8) :
    bytesToBits data.val =
      SHS.Equiv.SHA256.Padding.ByteDecoding.bytesToBitMessage
        (sliceToByteArray data) := by
  unfold bytesToBits SHS.Equiv.SHA256.Padding.ByteDecoding.bytesToBitMessage
  simp [sliceToByteArray, List.flatMap_map]

/-- The SHA-512 namespace's `bytesToBitMessage` coincides with the SHA-256
namespace's; the same equality holds. -/
theorem bytesToBits_eq_sha512_bytesToBitMessage (data : Slice U8) :
    bytesToBits data.val =
      SHS.Equiv.SHA512.Padding.ByteDecoding.bytesToBitMessage
        (sliceToByteArray data) :=
  bytesToBits_eq_sha256_bytesToBitMessage data

/-! ### Word.fromBits over bytesToBits matches the upstream digestBitVec... family -/

private theorem fromBits_bytesToBits_aux {N : Usize} {n : Nat}
    (a : Aeneas.Std.Array U8 N) :
    SHS.Word.fromBits (n := n) (bytesToBits a.val) =
      SHS.Word.fromBits (n := n)
        ((arrayU8ToVec a).toList.flatMap SHS.Equiv.Bytes.byteToBits) := by
  congr 1
  unfold bytesToBits
  rw [show (arrayU8ToVec a).toList = a.val.map toUInt8 from ?_]
  · rw [List.flatMap_map]
  · simp [arrayU8ToVec]

theorem fromBits_bytesToBits_eq_digestBitVec_sha256
    (a : Aeneas.Std.Array U8 32#usize) :
    SHS.Word.fromBits (n := 256) (bytesToBits a.val) =
      SHS.Equiv.SHA256.Digest.digestBitVec (arrayU8ToVec a) :=
  fromBits_bytesToBits_aux a

theorem fromBits_bytesToBits_eq_digestBitVec_sha224
    (a : Aeneas.Std.Array U8 28#usize) :
    SHS.Word.fromBits (n := 224) (bytesToBits a.val) =
      SHS.Equiv.SHA256.Digest.digestBitVec224 (arrayU8ToVec a) :=
  fromBits_bytesToBits_aux a

theorem fromBits_bytesToBits_eq_digestBitVec_sha512
    (a : Aeneas.Std.Array U8 64#usize) :
    SHS.Word.fromBits (n := 512) (bytesToBits a.val) =
      SHS.Equiv.SHA512.Digest.digestBitVec512 (arrayU8ToVec a) :=
  fromBits_bytesToBits_aux a

theorem fromBits_bytesToBits_eq_digestBitVec_sha384
    (a : Aeneas.Std.Array U8 48#usize) :
    SHS.Word.fromBits (n := 384) (bytesToBits a.val) =
      SHS.Equiv.SHA512.Digest.digestBitVec384 (arrayU8ToVec a) :=
  fromBits_bytesToBits_aux a

theorem fromBits_bytesToBits_eq_digestBitVec_sha512_256
    (a : Aeneas.Std.Array U8 32#usize) :
    SHS.Word.fromBits (n := 256) (bytesToBits a.val) =
      SHS.Equiv.SHA512.Digest.digestBitVec512_256 (arrayU8ToVec a) :=
  fromBits_bytesToBits_aux a

theorem fromBits_bytesToBits_eq_digestBitVec_sha512_224
    (a : Aeneas.Std.Array U8 28#usize) :
    SHS.Word.fromBits (n := 224) (bytesToBits a.val) =
      SHS.Equiv.SHA512.Digest.digestBitVec512_224 (arrayU8ToVec a) :=
  fromBits_bytesToBits_aux a
