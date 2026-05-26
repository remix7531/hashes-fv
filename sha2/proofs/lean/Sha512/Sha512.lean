import Word.U64
import Word.ToU64s
import Extraction
import equiv.SHA512.Main

/-!
# Top-level SHA-512 refinement statement (proof pending).

The SHA-256 family is fully proved; the SHA-512 family is structurally
parallel but the round-step / compress bridges are still being worked
out. This file currently states `sha512_spec` and admits it via `sorry`
so the downstream spec-layer corollary (`Spec.sha512_fips_correct`) can
still be type-checked.
-/

open Aeneas Aeneas.Std Result WP SHS.SHA512

theorem sha512_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha512 data
    ⦃ out =>
        ∃ ba : ByteArray, ba.toList = (data.val.map toUInt8) ∧
          (arrayU8ToVec out).toList = (Impl.sha512 ba).toList ⦄ := by
  sorry
