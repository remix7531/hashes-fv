import Aeneas

/-!
# Word-size-agnostic `Vector` helpers

Tiny `Vector` bridge lemmas used by both SHA-256 and SHA-512 refinement
proofs to align bounded `Vector.set` / `Vector.getElem` with their
default (`set!` / `getElem!`) counterparts when the index is in range.
-/

/-- `Vector.set` (bounds-proof form) coincides with `Vector.set!` when the
index is in range. -/
theorem vector_set_eq_set!
    {α : Type _} {n : Nat} (v : Vector α n) (i : Nat) (x : α) (h : i < n) :
    v.set i x h = v.set! i x := by
  apply Vector.toArray_inj.mp
  simp [Array.setIfInBounds, h]

/-- Symmetric form: `Vector.set!` coincides with the bounded `Vector.set`. -/
theorem vector_set!_eq_set_of_lt
    {α : Type _} {n : Nat} (v : Vector α n) (i : Nat) (x : α) (h : i < n) :
    v.set! i x = v.set i x h := by
  rw [← vector_set_eq_set! v i x h]

/-- `getElem!` agrees with `getElem` on Vectors when the index is in range. -/
theorem vector_getElem!_eq_getElem
    {α : Type _} [Inhabited α] {n : Nat} (v : Vector α n) (i : Nat) (h : i < n) :
    v[i]! = v[i]'h := by
  simp [getElem!_pos, h]

/-- Pointwise-agreement form of `Vector.ofFn` truncation: two `Vector.ofFn`
applications whose underlying functions agree on the shorter `Fin K`
satisfy `(short).toList = (long).toList.take K`.  Used by the four
truncated SHA-2 family bridges (SHA-224, SHA-384, SHA-512/256,
SHA-512/224) to refine `Impl.shaXxx` against `take K of sha2InnerW IV`. -/
theorem vector_ofFn_take_of_agree
    {α : Type _} [Inhabited α] {K M : Nat} (hKM : K ≤ M)
    (f : Fin K → α) (g : Fin M → α)
    (hfg : ∀ (k : Nat) (hk : k < K),
      f ⟨k, hk⟩ = g ⟨k, Nat.lt_of_lt_of_le hk hKM⟩) :
    (Vector.ofFn f).toList = (Vector.ofFn g).toList.take K := by
  apply List.ext_getElem
  · simp [hKM]
  · intro k hk _
    have hkK : k < K := by simpa using hk
    rw [Vector.getElem_toList (h := by simp; exact hkK),
        Vector.getElem_ofFn (h := hkK),
        List.getElem_take,
        Vector.getElem_toList (h := by simp; omega),
        Vector.getElem_ofFn (h := by omega)]
    exact hfg k hkK
