import FokkerChallenge.BetaCheck
import FokkerChallenge.EnhancedCslib.GenFinset

/-!
# The class of β-reducts of two-name-nameable terms

`BetaReductOfNamable T` says that `T` is a β-reduct of a term that can be named
with only the two variable names `x` and `y`.

This file proves the two structural facts that make the class useful for the
"one-point basis" question:

* `namableXY_app` / `BetaReductOfNamable.app`: nameability, and hence the class,
  is closed under application;
* `not_betaConv_of_betaReductOfNamable`: if `A` belongs to the class, then no
  applicative combination of `A` is β-convertible to a term that is not
  β-convertible to any nameable term.

Consequently, if some closed term is not β-convertible to any two-name term
(Statman, *Two variables are not enough*), then no term of the class can be a
one-point basis.
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- β-conversion. -/
abbrev BetaConv : Term String → Term String → Prop := Relation.EqvGen FullBeta

theorem betaConv_of_betaStar {M N : Term String} (h : M ↠βᶠ N) : BetaConv M N := by
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | tail _ hstep ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hstep)

/-- Every term of the class is β-convertible to a term nameable with two names. -/
theorem exists_namableXY_betaConv {T : Term String} (h : BetaReductOfNamable T) :
    ∃ S, namableXY S = true ∧ BetaConv S T := by
  obtain ⟨S, hS, hred⟩ := h
  exact ⟨S, hS, betaConv_of_betaStar hred⟩

/-- **The criterion.**  Suppose `A` is a β-reduct of a term nameable with the two
names `x`, `y`, and suppose `U` is a closed term that is not β-convertible to any
such nameable term.  Then no applicative combination of `A` is β-convertible to
`U`; in particular `A` is not a one-point basis. -/
theorem not_betaConv_of_betaReductOfNamable
    {A : Term String} (hA : BetaReductOfNamable A)
    {U : Term String} (hU : ∀ S, namableXY S = true → ¬ BetaConv S U)
    {C : Term String} (hC : ClosedUnderApp (fun t => t = A) C) : ¬ BetaConv C U := by
  have hCcl : BetaReductOfNamable C := by
    refine BetaReductOfNamable.closedUnderApp ?_
    induction hC with
    | base hb => exact ClosedUnderApp.base (hb ▸ hA)
    | app _ _ iha ihb => exact ClosedUnderApp.app iha ihb
  obtain ⟨S, hS, hconv⟩ := exists_namableXY_betaConv hCcl
  intro hCU
  exact hU S hS (Relation.EqvGen.trans _ _ _ hconv hCU)
