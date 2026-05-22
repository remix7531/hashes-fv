import Sha256
import Sha2Inner
import Sha2InnerSpec
import Common.Truncate

/-!
# Full SHA-224 refinement against `Local.sha224`

SHA-224 (FIPS 180-4 §6.3) is SHA-256 with a different IV (`H256_224`) and a
28-byte truncation of the final state.  The Rust source mirrors this:
`pub fn sha224(data) = sha256_inner(H256_224, data)[..28]`, and the
Aeneas-extracted `Extraction.sha224` calls the same `sha256_inner` engine
already proved correct against the IV-generic `sha2_inner_spec`
(`Sha2InnerSpec.lean`), then runs an `index ..28` + `try_from` chain to
materialize a `[u8; 28]`.

The truncation chain is handled by the generic `array_truncate_spec`
in `Common/Truncate.lean`, instantiated here with `M = 32`, `N = 28`.

This file lands the top-level `sha224_spec : Extraction.sha224 data ⦃ out =>
∃ ba, … ∧ (arrayU8ToVec out).toList = (Local.sha224 ba).toList ⦄`.
-/

open Aeneas Aeneas.Std Result WP SHS.SHA256

/-- Public top-level spec: the Aeneas-extracted `sha224` returns the
same digest as `Local.sha224` on the corresponding `ByteArray`. -/
theorem sha224_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha224 data
    ⦃ out =>
        ∃ ba : ByteArray, ba.toList = (data.val.map toUInt8) ∧
          (arrayU8ToVec out).toList = (Local.sha224 ba).toList ⦄ := by
  unfold Extraction.sha224
  apply spec_bind (sha2_inner_spec Extraction.consts.H256_224 Local.H256_224
                                    Local.H256_224_eq data h)
  intro inner_out hinner
  apply spec_mono
    (array_truncate_spec (by decide : (28#usize : Usize).val ≤ (32#usize : Usize).val)
       inner_out _ hinner)
  intro out hout
  refine ⟨sliceToByteArray data, sliceToByteArray_toList data, ?_⟩
  rw [hout, Local.sha224_toList]
  rfl
