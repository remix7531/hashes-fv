import Sha512.Sha512
import Sha512.Inner
import Sha512.InnerSpec
import Common.Truncate

/-! # Full SHA-512/256 refinement against `SHS.SHA512.Impl.sha512_256` -/

open Aeneas Aeneas.Std Result WP SHS.SHA512

theorem sha512_256_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha512_256 data
    ⦃ out =>
        ∃ ba : ByteArray, ba.toList = (data.val.map toUInt8) ∧
          (arrayU8ToVec out).toList = (Impl.sha512_256 ba).toList ⦄ := by
  unfold Extraction.sha512_256
  apply spec_bind (sha2_inner_spec_512 Extraction.consts.H512_256 Impl.H0_512_256
                                        H512_256_eq data h)
  intro inner_out hinner
  apply spec_mono
    (array_truncate_spec (by decide : (32#usize : Usize).val ≤ (64#usize : Usize).val)
       inner_out _ hinner)
  intro out hout
  refine ⟨sliceToByteArray data, sliceToByteArray_toList data, ?_⟩
  rw [hout, Local.sha512_256_eq_sha2Inner512_take _
        (by simpa [sliceToByteArray_size] using h)]
  rfl
