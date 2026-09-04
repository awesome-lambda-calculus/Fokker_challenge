import FokkerChallenge.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

variable {Var : Type u}

/-- A term is a *pure de Bruijn term* if it contains no free variable. -/
inductive IsDB : Term Var → Prop
  /-- A bound variable is a pure de Bruijn term. -/
  | bvar (n : ℕ) : IsDB (bvar n)
  /-- An abstraction of a pure de Bruijn term is one. -/
  | abs {t : Term Var} : IsDB t → IsDB (abs t)
  /-- An application of pure de Bruijn terms is one. -/
  | app {t u : Term Var} : IsDB t → IsDB u → IsDB (app t u)

/-- Having no free variables is the same as being a pure de Bruijn term. -/
theorem fv_eq_empty_iff_isDB [DecidableEq Var] {t : Term Var} : fv t = ∅ ↔ IsDB t := by
  induction t with
  | bvar n => exact ⟨fun _ => .bvar n, fun _ => rfl⟩
  | fvar x =>
      constructor
      · intro h; simp [fv] at h
      · intro h; cases h
  | abs t ih =>
      constructor
      · intro h; exact .abs (ih.1 h)
      · intro h; cases h with | abs h => exact ih.2 h
  | app t u iht ihu =>
      constructor
      · intro h
        rw [fv, Finset.union_eq_empty] at h
        exact .app (iht.1 h.1) (ihu.1 h.2)
      · intro h
        cases h with
        | app h1 h2 => rw [fv, iht.2 h1, ihu.2 h2]; simp
