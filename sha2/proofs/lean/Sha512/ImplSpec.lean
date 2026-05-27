import Sha512.InnerSpec
import Common.Truncate
import Common.U8

/-!
# Impl-level specs for the SHA-512 family

Corollaries of the IV-generic `sha2_inner_spec_512` (`Sha512/InnerSpec.lean`)
specialised at the per-algorithm IV, wrapped back through the panic
clause of `Impl.sha{512,384,512_256,512_224}`. These feed the public
top-level `sha{512,384,512_256,512_224}_spec` theorems in `Sha512.lean`. -/

open Aeneas Aeneas.Std Result WP SHS.SHA512

/-- SHA-512 Impl-level spec — corollary of `sha2_inner_spec_512` at
`iv = consts.H512_512, iv_vec = Impl.H0_512`, bridged back to
`Impl.sha512` via `Local.sha512_eq_sha2Inner512`. -/
theorem sha512_impl_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha512 data
    ⦃ out => arrayU8ToVec out = Impl.sha512 (sliceToByteArray data) ⦄ := by
  unfold Extraction.sha512
  apply spec_mono
    (sha2_inner_spec_512 Extraction.consts.H512_512 Impl.H0_512 H512_512_eq data h)
  intro out hout
  rw [hout, Local.sha512_eq_sha2Inner512 _
        (by simpa [sliceToByteArray_size] using h)]

/-- SHA-384 Impl-level spec — runs the same `sha512_inner` engine at
`iv = consts.H512_384, iv_vec = Impl.H0_384` and truncates to 48 bytes. -/
theorem sha384_impl_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha384 data
    ⦃ out => arrayU8ToVec out = Impl.sha384 (sliceToByteArray data) ⦄ := by
  unfold Extraction.sha384
  exact inner_truncate_digest_spec
    (by decide : (48#usize : Usize).val ≤ (64#usize : Usize).val) _ _ _
    (sha2_inner_spec_512 Extraction.consts.H512_384 Impl.H0_384 H512_384_eq data h)
    (Local.sha384_eq_sha2Inner512_take (sliceToByteArray data)
        (by simpa [sliceToByteArray_size] using h))

/-- SHA-512/256 Impl-level spec — `iv = consts.H512_256, iv_vec =
Impl.H0_512_256`, truncated to 32 bytes. -/
theorem sha512_256_impl_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha512_256 data
    ⦃ out => arrayU8ToVec out = Impl.sha512_256 (sliceToByteArray data) ⦄ := by
  unfold Extraction.sha512_256
  exact inner_truncate_digest_spec
    (by decide : (32#usize : Usize).val ≤ (64#usize : Usize).val) _ _ _
    (sha2_inner_spec_512 Extraction.consts.H512_256 Impl.H0_512_256 H512_256_eq data h)
    (Local.sha512_256_eq_sha2Inner512_take (sliceToByteArray data)
        (by simpa [sliceToByteArray_size] using h))

/-- SHA-512/224 Impl-level spec — `iv = consts.H512_224, iv_vec =
Impl.H0_512_224`, truncated to 28 bytes. -/
theorem sha512_224_impl_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha512_224 data
    ⦃ out => arrayU8ToVec out = Impl.sha512_224 (sliceToByteArray data) ⦄ := by
  unfold Extraction.sha512_224
  exact inner_truncate_digest_spec
    (by decide : (28#usize : Usize).val ≤ (64#usize : Usize).val) _ _ _
    (sha2_inner_spec_512 Extraction.consts.H512_224 Impl.H0_512_224 H512_224_eq data h)
    (Local.sha512_224_eq_sha2Inner512_take (sliceToByteArray data)
        (by simpa [sliceToByteArray_size] using h))
