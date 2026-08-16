import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import FokkerChallenge.EnhancedCslib.HeadRed
import Cslib.Foundations.Data.HasFresh
import FokkerChallenge.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-!
# Internal parallel β-reduction

Following Takahashi, *Parallel reductions in λ-calculus* (1995), Section 2, we
define **internal** parallel β-reduction `IPar`: a parallel β-reduction which
never contracts the head redex.

The head redex of `λx⃗. (λy. P) Q R⃗` is `(λy. P) Q`, so an internal parallel
reduction of that term reduces `P`, `Q` and the `R⃗` in parallel (arbitrarily),
but leaves the outer redex in place.  This is exactly what the constructor
`IPar.appAbs` expresses.

The key facts proved here are that `IPar` is a parallel β-reduction, that it is
substitutive under renaming, and that it *reflects* head normal forms
(`IPar.headNF_back`).
-/


universe u

open Term

variable {Var : Type u}

/-- **Internal parallel β-reduction**: a parallel β-reduction that does not
contract the head redex. -/
inductive IPar : Term Var → Term Var → Prop
  /-- A free variable reduces to itself. -/
  | fvar (x : Var) : IPar (Term.fvar x) (Term.fvar x)
  /-- If the function part is not an abstraction, the head redex lies inside it. -/
  | app {M M' N N' : Term Var} :
      ¬ M.IsAbs → IPar M M' → Parallel N N' → IPar (Term.app M N) (Term.app M' N')
  /-- If the function part is an abstraction, the whole application is the head
  redex; it is kept, but its constituents may reduce arbitrarily. -/
  | appAbs (xs : Finset Var) {M M' N N' : Term Var} :
      (∀ x ∉ xs, Parallel (M ^ Term.fvar x) (M' ^ Term.fvar x)) → Parallel N N' →
      IPar (Term.app (Term.abs M) N) (Term.app (Term.abs M') N')
  /-- Under a binder, the head redex is the head redex of the body. -/
  | abs (xs : Finset Var) {M M' : Term Var} :
      (∀ x ∉ xs, IPar (M ^ Term.fvar x) (M' ^ Term.fvar x)) → IPar (Term.abs M) (Term.abs M')

theorem IPar.not_isAbs {A B : Term Var} (h : IPar A B) (hA : ¬ A.IsAbs) : ¬ B.IsAbs := by
  cases h with
  | fvar x => grind
  | app => grind
  | appAbs => grind
  | abs => exact absurd (by grind) hA

/-- An internal parallel reduction is a parallel reduction. -/
theorem IPar.toParallel {M N : Term Var} (h : IPar M N) : Parallel M N := by
  induction h with
  | fvar x => exact Parallel.fvar x
  | app _ _ hN ih => exact Parallel.app ih hN
  | appAbs xs hbody hN => exact Parallel.app (Parallel.abs xs hbody) hN
  | abs xs _ ih => exact Parallel.abs xs ih


@[scoped grind →]
theorem IPar.step_lc_l {M N : Term Var} (h : IPar M N) : LC M :=
  para_lc_l h.toParallel

theorem IPar.headNeutral_back {M N : Term Var} (h : IPar M N) (hn : HeadNeutral N) :
    HeadNeutral M := by
  induction h with
  | fvar x => exact HeadNeutral.fvar x
  | @app M M' N N' _ _ hN ih =>
      cases hn with
      | app hM' _ => exact HeadNeutral.app (ih hM') (para_lc_l hN)
  | appAbs xs hbody hN =>
      cases hn with
      | app hM' _ => cases hM'
  | abs xs _ _ => cases hn

variable  [DecidableEq Var]

theorem IPar.headNF_back {M N : Term Var} (h : IPar M N) (hn : HeadNF N) :
    HeadNF M := by
  induction h with
  | fvar x => exact HeadNF.neutral (HeadNeutral.fvar x)
  | @app M M' N N' hM hstep hN ih =>
      exact HeadNF.neutral
        ((IPar.app hM hstep hN).headNeutral_back (HeadNF.of_not_isAbs hn (by grind)))
  | @appAbs xs M M' N N' hbody hN =>
      have hneu := HeadNF.of_not_isAbs hn (by grind)
      cases hneu with
      | app hM' _ => cases hM'
  | @abs xs M M' hbody ih =>
      cases hn with
      | neutral hneu => cases hneu
      | @abs ys A hA =>
          refine HeadNF.abs (xs ∪ ys) ?_
          intro x hx
          simp only [Finset.mem_union, not_or] at hx
          exact ih x hx.1 (hA x hx.2)

variable  [HasFresh Var]

@[scoped grind →]
theorem IPar.step_lc_r {M N : Term Var} (h : IPar M N) : LC N :=
  para_lc_r h.toParallel

/-- Renaming a free variable preserves parallel β-reduction. -/
theorem Parallel.rename {A B : Term Var} (h : Parallel A B) (x y : Var) :
    Parallel (A[x:= (Term.fvar y)]) (B[x:= (Term.fvar y)]) :=
  para_subst x h (Parallel.fvar y)

/-- Parallel β-reduction lifts under a binder, via closing. -/
theorem Parallel.abs_close (x : Var) {A B : Term Var} (h : Parallel A B) :
    Parallel (Term.abs (A ^* x)) (Term.abs (B ^* x)) := by
  refine Parallel.abs ({x} ∪ fv A ∪ fv B) ?_
  intro y _
  rw [close_open_to_subst,close_open_to_subst]
  exact h.rename x y
  grind
  grind
  grind
  grind

/-- Renaming a free variable preserves internal parallel β-reduction. -/
theorem IPar.rename {A B : Term Var} (h : IPar A B) (x y : Var) :
    IPar (A[x:=(Term.fvar y)]) (B[x:=(Term.fvar y)]) := by
  induction h with
  | fvar z => by_cases hz : z = x <;> rw [subst_fvar] <;> split <;> exact IPar.fvar _
  | @app M M' N N' hM _ hN ih => exact IPar.app (by grind [isAbs_subst_fvar]) ih (hN.rename x y)
  | @appAbs xs M M' N N' hbody hN =>
      refine IPar.appAbs (xs ∪ {x} ∪ {y}) ?_ (hN.rename x y)
      intro z hz
      grind [(hbody z (by grind)).rename x y]
  | @abs xs M M' _ ih =>
      refine IPar.abs (xs ∪ {x}) ?_
      intro z hz
      grind [ih z (by grind)]

/-- Internal parallel β-reduction lifts under a binder, via closing. -/
theorem IPar.abs_close (x : Var) {A B : Term Var} (h : IPar A B) :
    IPar (Term.abs (A ^* x)) (Term.abs (B ^* x)) := by
  refine IPar.abs ({x} ∪ fv A ∪ fv B) ?_
  intro y _
  rw [close_open_to_subst,close_open_to_subst]
  exact h.rename x y
  grind
  grind
  grind
  grind
