import Aeneas

/-!
# Word-size-agnostic weakest-precondition utilities

Helpers around the Aeneas weakest-precondition predicate `_ ⦃ _ ⦄`
that are shared between the SHA-256 and SHA-512 refinement proofs.
-/

open Aeneas Aeneas.Std Result WP

/-- Unpack an Aeneas spec hypothesis `act ⦃ post ⦄` into a concrete `ok` witness:
if the action satisfies `post`, then it cannot be `.fail` or `.div`. -/
theorem ok_of_spec {α} {act : Result α} {post : α → Prop}
    (h : act ⦃ s => post s ⦄) : ∃ v, act = .ok v ∧ post v := by
  cases hact : act with
  | ok v => rw [hact] at h; rw [spec_ok] at h; exact ⟨v, rfl, h⟩
  | fail e => rw [hact] at h; rw [spec_fail] at h; exact h.elim
  | div => rw [hact] at h; rw [spec_div] at h; exact h.elim
