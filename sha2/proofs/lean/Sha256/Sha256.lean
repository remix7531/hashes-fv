import Sha256.Compress
import Sha256.SetChain
import Sha256.Loop0
import Sha256.Loop1
import Sha256.FinalBlock
import Sha256.Inner
import Sha256.InnerSpec
import Common.Digest
import equiv.SHA256.Main

/-!
# Full SHA-256 refinement against the FIPS-180-4 bitwise spec

The IV-generic inner-spec body lives in `Sha2InnerSpec.lean` (shared
with SHA-224); this file specialises it at `iv = H256_256`, wraps with
the `Impl.sha256` panic clause via `Local.sha256_eq_sha2Inner256`, then
chains through `SHS.Equiv.SHA256.sha256_correct` (from `fips-pub-180-4`)
to land on the bitwise spec `SHS.SHA256.sha256`. -/

open Aeneas Aeneas.Std Result WP SHS.SHA256

/-- SHA-256 inner-spec — corollary of the IV-generic `sha2_inner_spec` at
`iv = consts.H256_256, iv_vec = Impl.H256_256`, bridged back to
`Impl.sha256` via `Local.sha256_eq_sha2Inner256`. -/
private theorem sha256_inner_spec
    (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha256_inner Extraction.consts.H256_256 data
    ⦃ out => arrayU8ToVec out = Impl.sha256 (sliceToByteArray data) ⦄ := by
  apply spec_mono
    (sha2_inner_spec Extraction.consts.H256_256 Impl.H256_256 H256_256_eq data h)
  intro out hout
  rw [hout, Local.sha256_eq_sha2Inner256 _
        (by simpa [sliceToByteArray_size] using h)]

private theorem sha256_impl_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha256 data
    ⦃ out => arrayU8ToVec out = Impl.sha256 (sliceToByteArray data) ⦄ := by
  unfold Extraction.sha256
  exact sha256_inner_spec data h

/-- Public top-level spec: the Aeneas-extracted `sha256` returns the
same 256-bit digest as the FIPS-180-4 bitwise spec `SHS.SHA256.sha256`. -/
theorem sha256_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha256 data
    ⦃ out =>
        digestBitVec (arrayU8ToVec out) =
          SHS.SHA256.sha256 (sliceBitMessage data)
            (sliceBitMessage_lt_2_64 data h) ⦄ := by
  apply spec_mono (sha256_impl_spec data h)
  intro out hout
  rw [hout]
  show SHS.Equiv.SHA256.Digest.digestBitVec (Impl.sha256 _) = _
  exact SHS.Equiv.SHA256.sha256_correct _
    (by simpa [sliceToByteArray_size] using h)
