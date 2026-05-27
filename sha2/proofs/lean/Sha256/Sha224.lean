import Sha256.Sha256
import Sha256.Inner
import Sha256.InnerSpec
import Common.Truncate
import Common.Digest
import equiv.SHA256.Main

/-!
# Full SHA-224 refinement against the FIPS-180-4 bitwise spec

SHA-224 (FIPS 180-4 §6.3) is SHA-256 with the `H256_224` IV and a 28-byte
truncation of the BE-emitted state.  Aeneas-extracted `Extraction.sha224`
calls the same `sha256_inner` engine already proved correct against the
IV-generic `sha2_inner_spec` (`Sha2InnerSpec.lean`), then runs an
`index ..28` + `try_from` chain to materialize a `[u8; 28]`.  This file
lands the spec form by chaining through `SHS.Equiv.SHA256.sha224_correct`. -/

open Aeneas Aeneas.Std Result WP SHS.SHA256

private theorem sha224_impl_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha224 data
    ⦃ out => arrayU8ToVec out = Impl.sha224 (sliceToByteArray data) ⦄ := by
  unfold Extraction.sha224
  exact inner_truncate_digest_spec
    (by decide : (28#usize : Usize).val ≤ (32#usize : Usize).val) _ _ _
    (sha2_inner_spec Extraction.consts.H256_224 Impl.H256_224 Local.H256_224_eq data h)
    (Local.sha224_eq_sha2Inner256_take (sliceToByteArray data)
        (by simpa [sliceToByteArray_size] using h))

/-- Public top-level spec: the Aeneas-extracted `sha224` returns the
same 224-bit digest as the FIPS-180-4 bitwise spec `SHS.SHA256.sha224`. -/
theorem sha224_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha224 data
    ⦃ out =>
        digestBitVec (arrayU8ToVec out) =
          SHS.SHA256.sha224 (sliceBitMessage data)
            (sliceBitMessage_lt_2_64 data h) ⦄ := by
  apply spec_mono (sha224_impl_spec data h)
  intro out hout; rw [hout]
  show SHS.Equiv.SHA256.Digest.digestBitVec224 (Impl.sha224 _) = _
  exact SHS.Equiv.SHA256.sha224_correct _ (by simpa [sliceToByteArray_size] using h)
