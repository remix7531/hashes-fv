import Sha512.InnerSpec
import Common.Digest
import equiv.SHA512.Main

/-!
# Full SHA-512 refinement against the FIPS-180-4 bitwise spec

The IV-generic inner-spec body lives in `InnerSpec.lean` (shared with
SHA-384 / SHA-512/256 / SHA-512/224); this file specialises it at
`iv = H0_512`, wraps with the `Impl.sha512` panic clause via
`Local.sha512_eq_sha2Inner512`, then chains through
`SHS.Equiv.SHA512.sha512_correct` (from `fips-pub-180-4`) to land on
the bitwise spec `SHS.SHA512.sha512`. -/

open Aeneas Aeneas.Std Result WP SHS.SHA512

/-- SHA-512 Impl-level spec — corollary of the IV-generic
`sha2_inner_spec_512` at `iv = consts.H512_512, iv_vec = Impl.H0_512`,
bridged back to `Impl.sha512` via `Local.sha512_eq_sha2Inner512`. -/
private theorem sha512_impl_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha512 data
    ⦃ out => arrayU8ToVec out = Impl.sha512 (sliceToByteArray data) ⦄ := by
  unfold Extraction.sha512
  apply spec_mono (sha2_inner_spec_512 Extraction.consts.H512_512 Impl.H0_512 H512_512_eq data h)
  intro out hout; rw [hout, Local.sha512_eq_sha2Inner512 _ (by simpa [sliceToByteArray_size] using h)]

/-- Public top-level spec: the Aeneas-extracted `sha512` returns the
same 512-bit digest as the FIPS-180-4 bitwise spec `SHS.SHA512.sha512`. -/
theorem sha512_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha512 data
    ⦃ out =>
        digestBitVec (arrayU8ToVec out) =
          SHS.SHA512.sha512 (sliceBitMessage data)
            (sliceBitMessage_lt_2_128 data h) ⦄ := by
  apply spec_mono (sha512_impl_spec data h)
  intro out hout; rw [hout]
  show SHS.Equiv.SHA512.Digest.digestBitVec512 (Impl.sha512 _) = _
  exact SHS.Equiv.SHA512.sha512_correct _ (by simpa [sliceToByteArray_size] using h)
