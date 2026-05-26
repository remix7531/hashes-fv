import Sha512.Compress
import Sha512.SetChain
import Sha512.Loop0
import Sha512.Loop1
import Sha512.FinalBlock
import Sha512.Inner
import Sha512.InnerSpec

/-!
# Full SHA-512 refinement against `SHS.SHA512.Impl`

The IV-generic inner-spec body lives in `InnerSpec.lean` (shared with
SHA-384 / SHA-512/256 / SHA-512/224); this file specialises it at
`iv = H0_512` and wraps with the `Impl.sha512` panic clause via
`Local.sha512_eq_sha2Inner512`. -/

open Aeneas Aeneas.Std Result WP SHS.SHA512

/-- SHA-512 inner-spec — corollary of the IV-generic `sha2_inner_spec_512`
at `iv = consts.H512_512, iv_vec = Impl.H0_512`, bridged back to
`Impl.sha512` via `Local.sha512_eq_sha2Inner512`. -/
private theorem sha512_inner_spec
    (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha512_inner Extraction.consts.H512_512 data
    ⦃ out => arrayU8ToVec out = Impl.sha512 (sliceToByteArray data) ⦄ := by
  apply spec_mono
    (sha2_inner_spec_512 Extraction.consts.H512_512 Impl.H0_512 H512_512_eq data h)
  intro out hout
  rw [hout, Local.sha512_eq_sha2Inner512 _
        (by simpa [sliceToByteArray_size] using h)]

/-- Public top-level spec: the Aeneas-extracted `sha512` returns the
same digest as `Impl.sha512` on the corresponding `ByteArray`. -/
theorem sha512_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha512 data
    ⦃ out =>
        ∃ ba : ByteArray, ba.toList = (data.val.map toUInt8) ∧
          (arrayU8ToVec out).toList = (Impl.sha512 ba).toList ⦄ := by
  unfold Extraction.sha512
  apply spec_mono (sha512_inner_spec data h)
  intro out hout
  refine ⟨sliceToByteArray data, sliceToByteArray_toList data, ?_⟩
  rw [hout]
  rfl
