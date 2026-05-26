import Sha512

/-! Top-level SHA-384 refinement statement (proof pending). -/

open Aeneas Aeneas.Std Result WP SHS.SHA512

theorem sha384_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha384 data
    ⦃ out =>
        ∃ ba : ByteArray, ba.toList = (data.val.map toUInt8) ∧
          (arrayU8ToVec out).toList = (Impl.sha384 ba).toList ⦄ := by
  sorry
