import Sha512.Sha512
import Common.Truncate

/-!
# Full SHA-384 refinement against the FIPS-180-4 bitwise spec

SHA-384 is SHA-512 with `H0_384` IV and a 48-byte truncation.  This file
proves Extraction's `sha384` against the bitwise FIPS spec
`SHS.SHA512.sha384` by chaining the Impl-side proof through
`SHS.Equiv.SHA512.sha384_correct`. -/

open Aeneas Aeneas.Std Result WP SHS.SHA512

private theorem sha384_impl_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha384 data
    ⦃ out => arrayU8ToVec out = Impl.sha384 (sliceToByteArray data) ⦄ := by
  unfold Extraction.sha384
  exact inner_truncate_digest_spec
    (by decide : (48#usize : Usize).val ≤ (64#usize : Usize).val) _ _ _
    (sha2_inner_spec_512 Extraction.consts.H512_384 Impl.H0_384 H512_384_eq data h)
    (Local.sha384_eq_sha2Inner512_take (sliceToByteArray data)
        (by simpa [sliceToByteArray_size] using h))

theorem sha384_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha384 data
    ⦃ out =>
        digestBitVec (arrayU8ToVec out) =
          SHS.SHA512.sha384 (sliceBitMessage data)
            (sliceBitMessage_lt_2_128 data h) ⦄ := by
  apply spec_mono (sha384_impl_spec data h)
  intro out hout; rw [hout]
  show SHS.Equiv.SHA512.Digest.digestBitVec384 (Impl.sha384 _) = _
  exact SHS.Equiv.SHA512.sha384_correct _ (by simpa [sliceToByteArray_size] using h)
