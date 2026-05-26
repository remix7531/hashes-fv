import Sha256.Compress
import Sha256.SetChain
import Sha256.Loop0
import Sha256.Loop1
import Sha256.FinalBlock
import Sha256.Inner
import Sha256.InnerSpec

/-!
# Full SHA-256 refinement against `SHS.SHA256.Impl`

The IV-generic inner-spec body lives in `Sha2InnerSpec.lean` (shared
with SHA-224); this file specializes it at `iv = H256_256` and wraps
with the `Impl.sha256` panic clause via `Local.sha256_eq_sha2Inner256`.
-/

open Aeneas Aeneas.Std Result WP SHS.SHA256

/-! ### Top-level theorem.

`sha256_inner` casts `data.size << 3` to `u64`; the cast silently wraps on
inputs ≥ 2^61 bytes. The Impl side `panic!`s above that threshold, so the
refinement carries `data.length < 2^61` as a precondition. -/

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

/-- Public top-level spec: the Aeneas-extracted `sha256` returns the
same digest as `Impl.sha256` on the corresponding `ByteArray`. -/
theorem sha256_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha256 data
    ⦃ out =>
        ∃ ba : ByteArray, ba.toList = (data.val.map toUInt8) ∧
          (arrayU8ToVec out).toList = (Impl.sha256 ba).toList ⦄ := by
  unfold Extraction.sha256
  apply spec_mono (sha256_inner_spec data h)
  intro out hout
  refine ⟨sliceToByteArray data, sliceToByteArray_toList data, ?_⟩
  rw [hout]
  rfl
