import Sha256
import Sha512
import equiv.SHA256.Main
import equiv.SHA512.Main

/-!
# Spec-layer corollaries

Compose the extraction-↔-Impl bridges with `fips-180-4-lean`'s
`SHS.Equiv.SHA256.{sha256,sha224}_correct` and
`SHS.Equiv.SHA512.{sha512,sha384,sha512_256,sha512_224}_correct` to
land on the FIPS-180-4 bitwise spec.
-/

open Aeneas Aeneas.Std Result WP
open SHS.Equiv.SHA256.Digest (digestBitVec digestBitVec224)
open SHS.Equiv.SHA256.Padding.ByteDecoding (bytesToBitMessage)
open SHS.Equiv.SHA512.Digest (digestBitVec512 digestBitVec384
                              digestBitVec512_256 digestBitVec512_224)

/-! ## SHA-256 family -/

theorem sha256_correct (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha256 data
    ⦃ out =>
        ∃ ba : ByteArray, ba.toList = (data.val.map toUInt8) ∧
          (arrayU8ToVec out).toList = (SHS.SHA256.Impl.sha256 ba).toList ⦄ :=
  sha256_spec data h

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
  have hvec_eq : arrayU8ToVec out = SHS.SHA256.Impl.sha256 ba' :=
    Vector.toList_inj.mp hout_list
  set ba := sliceToByteArray data with hba_def
  have hba_size : ba.size < 2 ^ 61 := by simpa [hba_def, sliceToByteArray_size] using h
  have hcorr := SHS.Equiv.SHA256.sha256_correct ba hba_size
  rw [hvec_eq, hba'_eq, hcorr]

theorem sha224_correct (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha224 data
    ⦃ out =>
        ∃ ba : ByteArray, ba.toList = (data.val.map toUInt8) ∧
          (arrayU8ToVec out).toList = (SHS.SHA256.Impl.sha224 ba).toList ⦄ :=
  sha224_spec data h

theorem sha224_fips_correct (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha224 data
    ⦃ out =>
        let ba := sliceToByteArray data
        have hba : ba.size < 2 ^ 61 := by
          show (sliceToByteArray data).size < 2 ^ 61
          simpa [sliceToByteArray_size] using h
        digestBitVec224 (arrayU8ToVec out) =
          SHS.SHA256.sha224 (bytesToBitMessage ba)
            (SHS.Equiv.SHA256.Pipeline.bitLen_lt_of_size_lt ba hba) ⦄ := by
  apply spec_mono (sha224_spec data h)
  intro out hout
  obtain ⟨ba', hba'_list, hout_list⟩ := hout
  have hba'_eq : ba' = sliceToByteArray data := by
    apply ByteArray.ext; apply Array.toList_inj.mp
    rw [← ByteArray.toList_eq_data_toList, hba'_list]
    simp [sliceToByteArray]
  have hvec_eq : arrayU8ToVec out = SHS.SHA256.Impl.sha224 ba' :=
    Vector.toList_inj.mp hout_list
  set ba := sliceToByteArray data with hba_def
  have hba_size : ba.size < 2 ^ 61 := by simpa [hba_def, sliceToByteArray_size] using h
  have hcorr := SHS.Equiv.SHA256.sha224_correct ba hba_size
  rw [hvec_eq, hba'_eq, hcorr]

/-! ## SHA-512 family -/

theorem sha512_correct (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha512 data
    ⦃ out =>
        ∃ ba : ByteArray, ba.toList = (data.val.map toUInt8) ∧
          (arrayU8ToVec out).toList = (SHS.SHA512.Impl.sha512 ba).toList ⦄ :=
  sha512_spec data h

theorem sha512_fips_correct (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha512 data
    ⦃ out =>
        let ba := sliceToByteArray data
        have hba : ba.size < 2 ^ 61 := by
          show (sliceToByteArray data).size < 2 ^ 61
          simpa [sliceToByteArray_size] using h
        digestBitVec512 (arrayU8ToVec out) =
          SHS.SHA512.sha512 (SHS.Equiv.SHA512.Padding.ByteDecoding.bytesToBitMessage ba)
            (SHS.Equiv.SHA512.Pipeline.bitLen_lt_of_size_lt ba hba) ⦄ := by
  apply spec_mono (sha512_spec data h)
  intro out hout
  obtain ⟨ba', hba'_list, hout_list⟩ := hout
  have hba'_eq : ba' = sliceToByteArray data := by
    apply ByteArray.ext; apply Array.toList_inj.mp
    rw [← ByteArray.toList_eq_data_toList, hba'_list]
    simp [sliceToByteArray]
  have hvec_eq : arrayU8ToVec out = SHS.SHA512.Impl.sha512 ba' :=
    Vector.toList_inj.mp hout_list
  set ba := sliceToByteArray data with hba_def
  have hba_size : ba.size < 2 ^ 61 := by simpa [hba_def, sliceToByteArray_size] using h
  have hcorr := SHS.Equiv.SHA512.sha512_correct ba hba_size
  rw [hvec_eq, hba'_eq, hcorr]

theorem sha384_correct (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha384 data
    ⦃ out =>
        ∃ ba : ByteArray, ba.toList = (data.val.map toUInt8) ∧
          (arrayU8ToVec out).toList = (SHS.SHA512.Impl.sha384 ba).toList ⦄ :=
  sha384_spec data h

theorem sha384_fips_correct (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha384 data
    ⦃ out =>
        let ba := sliceToByteArray data
        have hba : ba.size < 2 ^ 61 := by
          show (sliceToByteArray data).size < 2 ^ 61
          simpa [sliceToByteArray_size] using h
        digestBitVec384 (arrayU8ToVec out) =
          SHS.SHA512.sha384 (SHS.Equiv.SHA512.Padding.ByteDecoding.bytesToBitMessage ba)
            (SHS.Equiv.SHA512.Pipeline.bitLen_lt_of_size_lt ba hba) ⦄ := by
  apply spec_mono (sha384_spec data h)
  intro out hout
  obtain ⟨ba', hba'_list, hout_list⟩ := hout
  have hba'_eq : ba' = sliceToByteArray data := by
    apply ByteArray.ext; apply Array.toList_inj.mp
    rw [← ByteArray.toList_eq_data_toList, hba'_list]
    simp [sliceToByteArray]
  have hvec_eq : arrayU8ToVec out = SHS.SHA512.Impl.sha384 ba' :=
    Vector.toList_inj.mp hout_list
  set ba := sliceToByteArray data with hba_def
  have hba_size : ba.size < 2 ^ 61 := by simpa [hba_def, sliceToByteArray_size] using h
  have hcorr := SHS.Equiv.SHA512.sha384_correct ba hba_size
  rw [hvec_eq, hba'_eq, hcorr]

theorem sha512_256_correct (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha512_256 data
    ⦃ out =>
        ∃ ba : ByteArray, ba.toList = (data.val.map toUInt8) ∧
          (arrayU8ToVec out).toList = (SHS.SHA512.Impl.sha512_256 ba).toList ⦄ :=
  sha512_256_spec data h

theorem sha512_256_fips_correct (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha512_256 data
    ⦃ out =>
        let ba := sliceToByteArray data
        have hba : ba.size < 2 ^ 61 := by
          show (sliceToByteArray data).size < 2 ^ 61
          simpa [sliceToByteArray_size] using h
        digestBitVec512_256 (arrayU8ToVec out) =
          SHS.SHA512.sha512_256 (SHS.Equiv.SHA512.Padding.ByteDecoding.bytesToBitMessage ba)
            (SHS.Equiv.SHA512.Pipeline.bitLen_lt_of_size_lt ba hba) ⦄ := by
  apply spec_mono (sha512_256_spec data h)
  intro out hout
  obtain ⟨ba', hba'_list, hout_list⟩ := hout
  have hba'_eq : ba' = sliceToByteArray data := by
    apply ByteArray.ext; apply Array.toList_inj.mp
    rw [← ByteArray.toList_eq_data_toList, hba'_list]
    simp [sliceToByteArray]
  have hvec_eq : arrayU8ToVec out = SHS.SHA512.Impl.sha512_256 ba' :=
    Vector.toList_inj.mp hout_list
  set ba := sliceToByteArray data with hba_def
  have hba_size : ba.size < 2 ^ 61 := by simpa [hba_def, sliceToByteArray_size] using h
  have hcorr := SHS.Equiv.SHA512.sha512_256_correct ba hba_size
  rw [hvec_eq, hba'_eq, hcorr]

theorem sha512_224_correct (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha512_224 data
    ⦃ out =>
        ∃ ba : ByteArray, ba.toList = (data.val.map toUInt8) ∧
          (arrayU8ToVec out).toList = (SHS.SHA512.Impl.sha512_224 ba).toList ⦄ :=
  sha512_224_spec data h

theorem sha512_224_fips_correct (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha512_224 data
    ⦃ out =>
        let ba := sliceToByteArray data
        have hba : ba.size < 2 ^ 61 := by
          show (sliceToByteArray data).size < 2 ^ 61
          simpa [sliceToByteArray_size] using h
        digestBitVec512_224 (arrayU8ToVec out) =
          SHS.SHA512.sha512_224 (SHS.Equiv.SHA512.Padding.ByteDecoding.bytesToBitMessage ba)
            (SHS.Equiv.SHA512.Pipeline.bitLen_lt_of_size_lt ba hba) ⦄ := by
  apply spec_mono (sha512_224_spec data h)
  intro out hout
  obtain ⟨ba', hba'_list, hout_list⟩ := hout
  have hba'_eq : ba' = sliceToByteArray data := by
    apply ByteArray.ext; apply Array.toList_inj.mp
    rw [← ByteArray.toList_eq_data_toList, hba'_list]
    simp [sliceToByteArray]
  have hvec_eq : arrayU8ToVec out = SHS.SHA512.Impl.sha512_224 ba' :=
    Vector.toList_inj.mp hout_list
  set ba := sliceToByteArray data with hba_def
  have hba_size : ba.size < 2 ^ 61 := by simpa [hba_def, sliceToByteArray_size] using h
  have hcorr := SHS.Equiv.SHA512.sha512_224_correct ba hba_size
  rw [hvec_eq, hba'_eq, hcorr]
