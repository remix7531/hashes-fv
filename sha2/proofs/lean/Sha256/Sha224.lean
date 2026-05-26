import Sha256.Sha256
import Sha256.Inner
import Sha256.InnerSpec
import Common.Truncate

/-!
# Full SHA-224 refinement against `SHS.SHA256.Impl.sha224`

SHA-224 (FIPS 180-4 §6.3) is SHA-256 with the `H256_224` IV and a 28-byte
truncation of the BE-emitted state.  Aeneas-extracted `Extraction.sha224`
calls the same `sha256_inner` engine already proved correct against the
IV-generic `sha2_inner_spec` (`Sha2InnerSpec.lean`), then runs an
`index ..28` + `try_from` chain to materialize a `[u8; 28]`.

This file lands the top-level `sha224_spec`, directly parallel to
`sha256_spec`:

  `Extraction.sha224 data ⦃ out =>
     ∃ ba, ba.toList = data.val.map toUInt8 ∧
       (arrayU8ToVec out).toList = (Impl.sha224 ba).toList ⦄`.

The truncation chain is handled by the generic `array_truncate_spec` in
`Common/Truncate.lean` (instantiated at `M = 32, N = 28`); the bridge
from `take 28 of sha2Inner256 H256_224` to `Impl.sha224` is
`Local.sha224_eq_sha2Inner256_take`.
-/

open Aeneas Aeneas.Std Result WP SHS.SHA256

/-- Public top-level spec: the Aeneas-extracted `sha224` returns the
same digest as the upstream `Impl.sha224` on the corresponding `ByteArray`. -/
theorem sha224_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha224 data
    ⦃ out =>
        ∃ ba : ByteArray, ba.toList = (data.val.map toUInt8) ∧
          (arrayU8ToVec out).toList = (Impl.sha224 ba).toList ⦄ := by
  unfold Extraction.sha224
  apply spec_bind (sha2_inner_spec Extraction.consts.H256_224 Impl.H256_224
                                    Local.H256_224_eq data h)
  intro inner_out hinner
  apply spec_mono
    (array_truncate_spec (by decide : (28#usize : Usize).val ≤ (32#usize : Usize).val)
       inner_out _ hinner)
  intro out hout
  refine ⟨sliceToByteArray data, sliceToByteArray_toList data, ?_⟩
  rw [hout, Local.sha224_eq_sha2Inner256_take _
        (by simpa [sliceToByteArray_size] using h)]
  rfl
