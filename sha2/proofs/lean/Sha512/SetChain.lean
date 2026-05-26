import Word.U64

/-!
# 8-fold chain of `Aeneas.Std.Array.set` through `arrayU64ToVec`

Specialised helper used by `compress_u64_spec` to bridge the Aeneas
output (a chain of 8 `Array.set` calls on an 8-element state array)
to a literal `Vector` of 8 `UInt64`s.  Direct 64-bit port of
`Sha256/SetChain.lean`.
-/

open Aeneas Aeneas.Std

/-- An 8-fold chain of `Aeneas.Std.Array.set` over an 8-element `U64`
array, viewed through `arrayU64ToVec`, equals the literal vector of
the converted set values. -/
theorem arrayU64ToVec_set8_chain
    (state : Aeneas.Std.Array Aeneas.Std.U64 8#usize)
    (v0 v1 v2 v3 v4 v5 v6 v7 : Aeneas.Std.U64) :
    arrayU64ToVec
      (((((((((state.set 0#usize v0).set 1#usize v1).set 2#usize v2).set 3#usize v3).set
              4#usize v4).set 5#usize v5).set 6#usize v6).set 7#usize v7)) =
    (#v[toUInt64 v0, toUInt64 v1, toUInt64 v2, toUInt64 v3,
        toUInt64 v4, toUInt64 v5, toUInt64 v6, toUInt64 v7] : Vector UInt64 8) := by
  apply Vector.toList_inj.mp
  rcases state with ⟨l, hl⟩
  match l, hl with
  | [_, _, _, _, _, _, _, _], _ =>
    simp [arrayU64ToVec, Aeneas.Std.Array.set, Vector.toList]
