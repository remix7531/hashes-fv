import Sha512.ImplSpec
import Common.Digest
import equiv.SHA512.Main

/-!
# Public top-level SHA-512 family refinement against the FIPS-180-4 spec

Aeneas-extracted `Extraction.sha{512,384,512_256,512_224}` return the
same digests as their FIPS-180-4 bitwise spec counterparts for inputs
shorter than 2^61 bytes. The Impl-level intermediaries live in
`Sha512/ImplSpec.lean`; this file chains them through the per-algorithm
`SHS.Equiv.SHA512.<algo>_correct` to land on the bitwise specs via the
`bytesToBits` / `Word.fromBits` bridge from `Common/Digest.lean`. -/

open Aeneas Aeneas.Std Result WP SHS.SHA512

/-- Public top-level spec: the Aeneas-extracted `sha512` returns the
same 512-bit digest as the FIPS-180-4 bitwise spec `SHS.SHA512.sha512`. -/
theorem sha512_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha512 data
    ⦃ out =>
        let hb := bytesToBits_length_lt_2_128 data.val h
        SHS.Word.fromBits (bytesToBits out.val) =
          SHS.SHA512.sha512 (bytesToBits data.val) hb ⦄ := by
  apply spec_mono (sha512_impl_spec data h)
  intro out hout
  simp only [bytesToBits_eq_sha512_bytesToBitMessage,
             fromBits_bytesToBits_eq_digestBitVec_sha512]
  rw [hout]
  exact SHS.Equiv.SHA512.sha512_correct _ (by simpa [sliceToByteArray_size] using h)

/-- Public top-level spec: the Aeneas-extracted `sha384` returns the
same 384-bit digest as the FIPS-180-4 bitwise spec `SHS.SHA512.sha384`. -/
theorem sha384_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha384 data
    ⦃ out =>
        let hb := bytesToBits_length_lt_2_128 data.val h
        SHS.Word.fromBits (bytesToBits out.val) =
          SHS.SHA512.sha384 (bytesToBits data.val) hb ⦄ := by
  apply spec_mono (sha384_impl_spec data h)
  intro out hout
  simp only [bytesToBits_eq_sha512_bytesToBitMessage,
             fromBits_bytesToBits_eq_digestBitVec_sha384]
  rw [hout]
  exact SHS.Equiv.SHA512.sha384_correct _ (by simpa [sliceToByteArray_size] using h)

/-- Public top-level spec: the Aeneas-extracted `sha512_256` returns the
same 256-bit digest as the FIPS-180-4 bitwise spec `SHS.SHA512.sha512_256`. -/
theorem sha512_256_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha512_256 data
    ⦃ out =>
        let hb := bytesToBits_length_lt_2_128 data.val h
        SHS.Word.fromBits (bytesToBits out.val) =
          SHS.SHA512.sha512_256 (bytesToBits data.val) hb ⦄ := by
  apply spec_mono (sha512_256_impl_spec data h)
  intro out hout
  simp only [bytesToBits_eq_sha512_bytesToBitMessage,
             fromBits_bytesToBits_eq_digestBitVec_sha512_256]
  rw [hout]
  exact SHS.Equiv.SHA512.sha512_256_correct _ (by simpa [sliceToByteArray_size] using h)

/-- Public top-level spec: the Aeneas-extracted `sha512_224` returns the
same 224-bit digest as the FIPS-180-4 bitwise spec `SHS.SHA512.sha512_224`. -/
theorem sha512_224_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha512_224 data
    ⦃ out =>
        let hb := bytesToBits_length_lt_2_128 data.val h
        SHS.Word.fromBits (bytesToBits out.val) =
          SHS.SHA512.sha512_224 (bytesToBits data.val) hb ⦄ := by
  apply spec_mono (sha512_224_impl_spec data h)
  intro out hout
  simp only [bytesToBits_eq_sha512_bytesToBitMessage,
             fromBits_bytesToBits_eq_digestBitVec_sha512_224]
  rw [hout]
  exact SHS.Equiv.SHA512.sha512_224_correct _ (by simpa [sliceToByteArray_size] using h)
