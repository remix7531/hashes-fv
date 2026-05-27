import Sha256.ImplSpec
import Common.Digest
import equiv.SHA256.Main

/-!
# Public top-level SHA-256 / SHA-224 refinement against the FIPS-180-4 spec

Aeneas-extracted `Extraction.sha256` and `Extraction.sha224` return the
same digests as the FIPS-180-4 bitwise specifications
`SHS.SHA256.sha256` and `SHS.SHA256.sha224` for inputs shorter than
2^61 bytes. The Impl-level intermediaries live in `Sha256/ImplSpec.lean`;
this file chains them through `SHS.Equiv.SHA256.{sha256,sha224}_correct`
to land on the bitwise specs via the `bytesToBits` / `Word.fromBits`
bridge from `Common/Digest.lean`. -/

open Aeneas Aeneas.Std Result WP SHS.SHA256

/-- Public top-level spec: the Aeneas-extracted `sha256` returns the
same 256-bit digest as the FIPS-180-4 bitwise spec `SHS.SHA256.sha256`. -/
theorem sha256_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha256 data
    ⦃ out =>
        let hb := bytesToBits_length_lt_2_64 data.val h
        SHS.Word.fromBits (bytesToBits out.val) =
          SHS.SHA256.sha256 (bytesToBits data.val) hb ⦄ := by
  apply spec_mono (sha256_impl_spec data h)
  intro out hout
  simp only [bytesToBits_eq_sha256_bytesToBitMessage,
             fromBits_bytesToBits_eq_digestBitVec_sha256]
  rw [hout]
  exact SHS.Equiv.SHA256.sha256_correct _ (by simpa [sliceToByteArray_size] using h)

/-- Public top-level spec: the Aeneas-extracted `sha224` returns the
same 224-bit digest as the FIPS-180-4 bitwise spec `SHS.SHA256.sha224`. -/
theorem sha224_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha224 data
    ⦃ out =>
        let hb := bytesToBits_length_lt_2_64 data.val h
        SHS.Word.fromBits (bytesToBits out.val) =
          SHS.SHA256.sha224 (bytesToBits data.val) hb ⦄ := by
  apply spec_mono (sha224_impl_spec data h)
  intro out hout
  simp only [bytesToBits_eq_sha256_bytesToBitMessage,
             fromBits_bytesToBits_eq_digestBitVec_sha224]
  rw [hout]
  exact SHS.Equiv.SHA256.sha224_correct _ (by simpa [sliceToByteArray_size] using h)
