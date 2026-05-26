import Sha512.Sha512

/-! Top-level SHA-512/224 refinement statement (proof pending). -/

open Aeneas Aeneas.Std Result WP SHS.SHA512

theorem sha512_224_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha512_224 data
    ⦃ out =>
        ∃ ba : ByteArray, ba.toList = (data.val.map toUInt8) ∧
          (arrayU8ToVec out).toList = (Impl.sha512_224 ba).toList ⦄ := by
  sorry
