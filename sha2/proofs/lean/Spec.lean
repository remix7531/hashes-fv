import Sha256
import equiv.SHA256.Main

/-!
# Spec-layer corollary

Compose the extraction-↔-Impl bridge with `fips-180-4-lean`'s
`SHS.Equiv.SHA256.sha256_correct` to land on the FIPS-180-4 spec.
-/

open Aeneas Aeneas.Std Result WP SHS.SHA256
open SHS.Equiv.SHA256.Digest (digestBitVec)
open SHS.Equiv.SHA256.Padding.ByteDecoding (bytesToBitMessage)

/-- Aeneas-extracted `Extraction.sha256` produces the FIPS-180-4 SHA-256 digest
of its input, for inputs below the `2^61`-byte length cap.

This is the Impl-layer statement (alias of `sha256_spec`); see
`sha256_fips_correct` below for the spec-layer corollary. -/
theorem sha256_correct (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha256 data
    ⦃ out =>
        ∃ ba : ByteArray, ba.toList = (data.val.map toUInt8) ∧
          (arrayU8ToVec out).toList = (Impl.sha256 ba).toList ⦄ :=
  sha256_spec data h

/-- Aeneas-extracted `Extraction.sha256` produces the FIPS-180-4 §6.2 SHA-256
digest of (the bit-list view of) its input, for inputs below the
`2^61`-byte length cap.

The right-hand side is the bitwise FIPS spec applied to
`bytesToBitMessage (sliceToByteArray data)`; the left-hand `out` is
viewed as a 256-bit big-endian `BitVec` via `digestBitVec`. -/
theorem sha256_fips_correct (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha256 data
    ⦃ out =>
        let ba := sliceToByteArray data
        have hba : ba.size < 2 ^ 61 := by
          show (sliceToByteArray data).size < 2 ^ 61
          simpa [sliceToByteArray_size] using h
        digestBitVec (arrayU8ToVec out) =
          SHS.SHA256.sha256 (bytesToBitMessage ba)
            (SHS.Equiv.SHA256.Pipeline.bitLen_lt_of_size_lt ba hba) ⦄ := by
  apply spec_mono (sha256_spec data h)
  intro out hout
  obtain ⟨ba', hba'_list, hout_list⟩ := hout
  have hba'_eq : ba' = sliceToByteArray data := by
    apply ByteArray.ext; apply Array.toList_inj.mp
    rw [← ByteArray.toList_eq_data_toList, hba'_list]
    simp [sliceToByteArray]
  have hvec_eq : arrayU8ToVec out = Impl.sha256 ba' :=
    Vector.toList_inj.mp hout_list
  set ba := sliceToByteArray data with hba_def
  have hba_size : ba.size < 2 ^ 61 := by simpa [hba_def, sliceToByteArray_size] using h
  have hcorr := SHS.Equiv.SHA256.sha256_correct ba hba_size
  rw [hvec_eq, hba'_eq, hcorr]
