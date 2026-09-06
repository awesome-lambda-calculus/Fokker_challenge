import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Properties

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- If opening with a free variable produces a term without free variables, then the
variable was not inserted at all. -/
theorem openRec_fvar_eq_self_of_fv_empty {M : Term String} {x : String} :
    ∀ i, (M⟦i ↝ Term.fvar x⟧).fv = ∅ → M⟦i ↝ Term.fvar x⟧ = M := by
  intro i h
  induction M generalizing i with
  | bvar j =>
      by_cases hij : i = j
      · simp [openRec, hij] at h
      · simp [openRec, hij]
  | fvar y => rfl
  | abs t ih =>
      simp only [openRec, fv] at h ⊢
      rw [ih _ h]
  | app f a ih₁ ih₂ =>
      simp only [openRec, fv, Finset.union_eq_empty] at h ⊢
      rw [ih₁ _ h.1, ih₂ _ h.2]
