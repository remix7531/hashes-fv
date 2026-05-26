import Word.U32

/-!
# 8-fold chain of `Aeneas.Std.Array.set` through `arrayU32ToVec`

Specialised helper used by `compress_u32_spec` to bridge the Aeneas
output (a chain of 8 `Array.set` calls on an 8-element state array)
to a literal `Vector` of 8 `UInt32`s.
-/



open Aeneas Aeneas.Std

/-- An 8-fold chain of `Aeneas.Std.Array.set` over an 8-element `U32`
array, viewed through `arrayU32ToVec`, equals the literal vector of
the converted set values. -/
theorem arrayU32ToVec_set8_chain
    (state : Aeneas.Std.Array Aeneas.Std.U32 8#usize)
    (v0 v1 v2 v3 v4 v5 v6 v7 : Aeneas.Std.U32) :
    arrayU32ToVec
      (((((((((state.set 0#usize v0).set 1#usize v1).set 2#usize v2).set 3#usize v3).set
              4#usize v4).set 5#usize v5).set 6#usize v6).set 7#usize v7)) =
    (#v[toUInt32 v0, toUInt32 v1, toUInt32 v2, toUInt32 v3,
        toUInt32 v4, toUInt32 v5, toUInt32 v6, toUInt32 v7] : Vector UInt32 8) := by
  -- Decompose the underlying list via the length-8 invariant, then
  -- `simp` reduces the 8-fold `Array.set` ↔ `List.set` chain to a literal cons-list.
  apply Vector.toList_inj.mp
  rcases state with ⟨l, hl⟩
  match l, hl with
  | [_, _, _, _, _, _, _, _], _ =>
    simp [arrayU32ToVec, Aeneas.Std.Array.set, Vector.toList]


