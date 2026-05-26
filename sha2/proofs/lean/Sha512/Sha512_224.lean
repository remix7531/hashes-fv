import Sha512.Sha512
import Sha512.Inner
import Sha512.InnerSpec
import Common.Truncate
import Common.Digest
import equiv.SHA512.Main

/-! # Full SHA-512/224 refinement against the FIPS-180-4 bitwise spec -/

open Aeneas Aeneas.Std Result WP SHS.SHA512

private theorem sha512_224_impl_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha512_224 data
    ⦃ out => arrayU8ToVec out = Impl.sha512_224 (sliceToByteArray data) ⦄ := by
  unfold Extraction.sha512_224
  apply spec_bind (sha2_inner_spec_512 Extraction.consts.H512_224 Impl.H0_512_224
                                        H512_224_eq data h)
  intro inner_out hinner
  apply spec_mono
    (array_truncate_spec (by decide : (28#usize : Usize).val ≤ (64#usize : Usize).val)
       inner_out _ hinner)
  intro out hout
  apply Vector.toList_inj.mp
  rw [hout]
  exact (Local.sha512_224_eq_sha2Inner512_take (sliceToByteArray data)
        (by simpa [sliceToByteArray_size] using h)).symm

theorem sha512_224_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha512_224 data
    ⦃ out =>
        digestBitVec (arrayU8ToVec out) =
          SHS.SHA512.sha512_224 (sliceBitMessage data)
            (sliceBitMessage_lt_2_128 data h) ⦄ := by
  apply spec_mono (sha512_224_impl_spec data h)
  intro out hout
  rw [hout]
  show SHS.Equiv.SHA512.Digest.digestBitVec512_224 (Impl.sha512_224 _) = _
  exact SHS.Equiv.SHA512.sha512_224_correct _
    (by simpa [sliceToByteArray_size] using h)
