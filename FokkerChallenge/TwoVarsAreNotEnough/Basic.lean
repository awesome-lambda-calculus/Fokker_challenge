import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Foundations.Data.HasFresh
import FokkerChallenge.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Union

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

@[scoped grind =]
def two_vars_are_enough: Term String → Bool
  | Term.bvar n => n < 2
  | Term.fvar _ => true
  | Term.abs (Term.abs t) => two_vars_are_enough t
  | Term.app t1 t2 => two_vars_are_enough t1 && two_vars_are_enough t2
  | _ => false

@[scoped grind]
theorem two_vars_are_enough_lcat {t} (g : two_vars_are_enough t) : LcAt 2 t := by
  induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
  | h n ih => cases t with
  | fvar _ => grind
  | bvar n => grind
  | app t1 t2 => grind
  | abs t => cases t with
    | bvar _ => grind
    | fvar _ => grind
    | app _ _ => grind
    | abs t =>  specialize @ih _ ?_ t ?_ rfl
                grind
                grind
                unfold LcAt
                unfold LcAt
                refine lcAt_le _ _ _ (by omega) ih

@[scoped grind]
theorem two_vars_are_enough_lc {t} (g : two_vars_are_enough t) : t.abs.abs.LC := by
  rw [<- lcAt_iff_LC]
  unfold LcAt
  unfold LcAt
  simp
  apply two_vars_are_enough_lcat g

theorem two_vars_are_enough_openRec {i x t} (g : two_vars_are_enough t) :
  two_vars_are_enough (t⟦i ↝ fvar x⟧) := by
  induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
  | h n _ => cases t with
  | bvar _ => grind
  | fvar _ => grind
  | app _ _ => grind
  | abs t => cases t with grind

@[scoped grind =]
def subterms : Term String -> Finset (Term String)
  | Term.bvar _ => ∅
  | Term.fvar _ => ∅
  | Term.abs (Term.abs t) => insert t.abs.abs (subterms t)
  | Term.abs _ => ∅
  | Term.app t1 t2 => subterms t1 ∪ subterms t2

@[scoped grind]
theorem subterms_size {t} :
    ∀ s ∈ subterms t, s.fokker_size <= t.fokker_size := by
  induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
  | h n _ => cases t with
  | bvar _ => grind
  | fvar _ => grind
  | app _ _ => grind
  | abs t => cases t with grind

theorem subterms_gen {t M} (h : Gen t M) : t.subterms = M.subterms := by
  induction h with grind


@[scoped grind]
theorem subterms_two_vars_are_enough {t} (h : two_vars_are_enough t) :
    ∀ s ∈ subterms t, two_vars_are_enough s := by
    induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
    | h n _ => cases t with
      | bvar _ => grind
      | fvar _ => grind
      | app _ _ => grind
      | abs t => cases t with grind

theorem subterms_preserved_under_openRec {x i t} (h : two_vars_are_enough t) :
    t.subterms = t⟦i ↝ fvar x⟧.subterms := by
    induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
    | h n _ => cases t with
    | bvar _ => grind
    | fvar _ => grind
    | app _ _ => grind
    | abs t => cases t with grind

theorem two_vars_are_enough_subterms_lc {t} (h : two_vars_are_enough t) (hlc: t.LC) :
    ∀ s ∈ subterms t, s.LC := by
    induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
    | h n ih => cases t with
      | bvar _ => grind
      | fvar _ => grind
      | app t1 t2 =>  intros s hs
                      unfold subterms at hs
                      cases hlc
                      simp at hs
                      cases hs
                      · refine ih t1.fokker_size ?_ ?_ ?_ rfl ?_ ?_
                        all_goals grind
                      · refine ih t2.fokker_size ?_ ?_ ?_ rfl ?_ ?_
                        all_goals grind
      | abs t => cases t with
        | bvar _ => grind
        | fvar _ => grind
        | app _ _ => grind
        | abs t =>  intros s hs
                    unfold subterms at hs
                    simp at hs
                    cases hs with
                    | inl _ => grind
                    | inr h =>  cases hlc with | abs xs e hlc =>
                                have ⟨x, _⟩ := fresh_exists <| free_union [fv] String
                                specialize hlc x (by grind)
                                cases hlc with | abs ys e hlc =>
                                have ⟨y, _⟩ := fresh_exists <| free_union [fv] String
                                specialize hlc y (by grind)
                                refine @ih ((t⟦0 + 1 ↝ fvar x⟧) ^ fvar y).fokker_size ?_ ((t⟦0 + 1 ↝ fvar x⟧) ^ fvar y) ?_ ?_ ?_ ?_ ?_
                                any_goals grind
                                · apply two_vars_are_enough_openRec
                                  apply two_vars_are_enough_openRec
                                  grind
                                · unfold open'
                                  rw [<- subterms_preserved_under_openRec,
                                      <- subterms_preserved_under_openRec]
                                  grind
                                  grind
                                  apply two_vars_are_enough_openRec
                                  grind




inductive leftSpine (fs : Finset (Term String)) : Term String → Prop where
  | singleton : ∀ t ∈ fs, leftSpine fs t
  | leftApp   : ∀ t1 ∈ fs, ∀ t2, leftSpine fs t2 → leftSpine fs (t1.app t2)

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
