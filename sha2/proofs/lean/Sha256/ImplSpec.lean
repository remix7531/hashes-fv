import Sha256.Compress
import Sha256.SetChain
import Sha256.Loop0
import Sha256.Loop1
import Sha256.FinalBlock
import Sha256.Inner
import Sha256.InnerSpec
import Common.Truncate
import Common.U8

/-!
# Impl-level specs for the SHA-256 family

Corollaries of the IV-generic `sha2_inner_spec` (`Sha256/InnerSpec.lean`)
specialised at the per-algorithm IV, wrapped back through the panic
clause of `Impl.sha{256,224}`. These feed the public top-level
`sha{256,224}_spec` theorems in `Sha256.lean`. -/

open Aeneas Aeneas.Std Result WP SHS.SHA256

/-- SHA-256 Impl-level spec — corollary of `sha2_inner_spec` at
`iv = consts.H256_256, iv_vec = Impl.H256_256`, bridged back to
`Impl.sha256` via `Local.sha256_eq_sha2Inner256`. -/
theorem sha256_impl_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha256 data
    ⦃ out => arrayU8ToVec out = Impl.sha256 (sliceToByteArray data) ⦄ := by
  unfold Extraction.sha256
  apply spec_mono (sha2_inner_spec Extraction.consts.H256_256 Impl.H256_256 H256_256_eq data h)
  intro out hout
  rw [hout, Local.sha256_eq_sha2Inner256 _ (by simpa [sliceToByteArray_size] using h)]

/-- SHA-224 Impl-level spec — runs the same `sha256_inner` engine at
`iv = consts.H256_224, iv_vec = Impl.H256_224` and truncates to 28 bytes
via the shared `inner_truncate_digest_spec` helper. -/
theorem sha224_impl_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha224 data
    ⦃ out => arrayU8ToVec out = Impl.sha224 (sliceToByteArray data) ⦄ := by
  unfold Extraction.sha224
  exact inner_truncate_digest_spec
    (by decide : (28#usize : Usize).val ≤ (32#usize : Usize).val) _ _ _
    (sha2_inner_spec Extraction.consts.H256_224 Impl.H256_224 Local.H256_224_eq data h)
    (Local.sha224_eq_sha2Inner256_take (sliceToByteArray data)
        (by simpa [sliceToByteArray_size] using h))
