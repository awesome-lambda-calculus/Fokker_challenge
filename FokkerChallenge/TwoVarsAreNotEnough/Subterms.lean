import FokkerChallenge.TwoVarsAreNotEnough.Basic
import FokkerChallenge.EnhancedCslib.Closedunderapp
import FokkerChallenge.EnhancedCslib.GenFinset

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

@[simp, scoped grind =]
def subterms : Term String -> List (Term String)
  | Term.bvar _ => []
  | Term.fvar _ => []
  | Term.abs (Term.abs t) => t.abs.abs :: (subterms t)
  | Term.abs _ => []
  | Term.app t1 t2 => subterms t1 ∪ subterms t2

theorem subterms_subset {t : Term String} :
    ∀ s ∈ t.subterms, s.subterms ⊆ t.subterms := by
  induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
  | h n _ => cases t with (simp_all; try subst_vars)
  | app _ _ => grind
  | abs t => cases t with (simp_all; try subst_vars)
    | abs _ => grind

theorem subterms_size {t} :
    ∀ s ∈ subterms t, s.fokker_size <= t.fokker_size := by
  induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
  | h n _ => cases t with (simp_all; try subst_vars)
  | app _ _ => grind
  | abs t => cases t with (simp_all; try subst_vars)
    | abs _ => grind

/-
theorem subterms_gen {t M} (h : Gen t M) : t.subterms = M.subterms := by
  induction h with grind
-/

theorem subterms_fv {t} (h : t.fv = ∅) :
    ∀ s ∈ subterms t, s.fv = ∅ := by
    induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
    | h n _ => cases t with  (simp_all; try subst_vars)
      | app _ _ => grind
      | abs t => cases t with (simp_all; try subst_vars)
        | abs _ => grind

theorem subterms_preserved_under_openRec {x i t} (h : two_vars_are_enough t) :
    t.subterms = t⟦i ↝ fvar x⟧.subterms := by
    induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
    | h n _ => cases t with
    | bvar _ => grind
    | fvar _ => grind
    | app _ _ => grind
    | abs t => cases t with grind

theorem subterms_two_vars_are_enough {t} (h : two_vars_are_enough t) :
    ∀ s ∈ subterms t, abs_two_vars_are_enough s := by
    induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
    | h n _ => cases t with (simp_all; try subst_vars)
      | app _ _ => grind
      | abs t => cases t with (simp_all; try subst_vars)
        | abs _ => grind

theorem two_vars_are_enough_subterms_lc {t} (h : two_vars_are_enough t) :
    ∀ s ∈ subterms t, s.LC := by grind [subterms_two_vars_are_enough]

theorem subterms_closedunderappbool {t} (h : ClosedUnderAppBool abs_two_vars_are_enough t) :
    ∀ s ∈ subterms t, abs_two_vars_are_enough s := by
    induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
    | h n _ => cases t with (simp_all; try subst_vars)
      | app _ _ => grind
      | abs t => cases t with (simp_all; try subst_vars)
        | abs _ => grind [subterms_two_vars_are_enough]

theorem closedUnderAppBool_genfinset_subterms {t}
    (h : ClosedUnderAppBool abs_two_vars_are_enough t) :
    GenFinset t.subterms t := by
  induction ht : t.fokker_size using Nat.strong_induction_on generalizing t with | h n ih =>
  cases t with
  | bvar _ => cases h
  | fvar _ => cases h
  | abs t => cases t <;> grind
  | app x y =>  have hx := @ih x.fokker_size (by grind) x (by grind) rfl
                have hy := @ih y.fokker_size (by grind) y (by grind) rfl
                refine .app (genfinset_subset (by grind) hx) (genfinset_subset (by grind) hy)

/-
@[scoped grind =]
def idempotent (terms : Finset (Term String)) : Prop :=
  terms.biUnion subterms = terms

theorem subterms_idempotent {t : Term String} : idempotent t.subterms := by
    induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
    | h n _ => cases t with
    | bvar _ => grind
    | fvar _ => grind
    | app _ _ => grind
    | abs t => cases t with grind
-/
