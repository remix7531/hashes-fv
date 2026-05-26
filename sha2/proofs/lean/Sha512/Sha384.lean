import Sha512.Sha512
import Sha512.Inner
import Sha512.InnerSpec
import Common.Truncate

/-!
# Full SHA-384 refinement against `SHS.SHA512.Impl.sha384`

SHA-384 is SHA-512 with `H0_384` IV and a 48-byte truncation.
-/

open Aeneas Aeneas.Std Result WP SHS.SHA512

theorem sha384_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha384 data
    ⦃ out =>
        ∃ ba : ByteArray, ba.toList = (data.val.map toUInt8) ∧
          (arrayU8ToVec out).toList = (Impl.sha384 ba).toList ⦄ := by
  unfold Extraction.sha384
  apply spec_bind (sha2_inner_spec_512 Extraction.consts.H512_384 Impl.H0_384
                                        H512_384_eq data h)
  intro inner_out hinner
  apply spec_mono
    (array_truncate_spec (by decide : (48#usize : Usize).val ≤ (64#usize : Usize).val)
       inner_out _ hinner)
  intro out hout
  refine ⟨sliceToByteArray data, sliceToByteArray_toList data, ?_⟩
  rw [hout, Local.sha384_eq_sha2Inner512_take _
        (by simpa [sliceToByteArray_size] using h)]
  rfl
