import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.ListFullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LeftmostReduction
import Cslib.Foundations.Data.HasFresh
import FokkerChallenge.Basic
import FokkerChallenge.FamousCombinator
import FokkerChallenge.EnhancedCslib.Basic
import FokkerChallenge.EnhancedCslib.FlipApp
import FokkerChallenge.EnhancedCslib.BetaNormalForm
import FokkerChallenge.EnhancedCslib.Closedunderapp
import FokkerChallenge.EnhancedCslib.List
import FokkerChallenge.EnhancedCslib.HeadNFSpineEta

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

@[scoped grind =]
def two_vars_are_enough: Term String → Bool
  | Term.bvar n => n < 2
  | Term.fvar _ => false
  | Term.abs (Term.abs t) => two_vars_are_enough t
  | Term.app t1 t2 => two_vars_are_enough t1 && two_vars_are_enough t2
  | _ => false

@[scoped grind <-]
theorem two_vars_are_enough_lc {t} (g : two_vars_are_enough t) : t.abs.abs.LC := by
  rw [<- lcAt_iff_LC]
  induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
  | h n ih => cases t with
  | fvar => grind
  | bvar => grind
  | app => grind
  | abs t => cases t with
    | bvar => grind
    | fvar => grind
    | app => grind
    | abs t =>  specialize @ih _ (by grind) t (by grind) rfl
                unfold LcAt LcAt
                exact lcAt_le _ _ _ (by omega) ih

theorem two_vars_are_enough_depth {M N1 N2: Term String}
  (hm : M.two_vars_are_enough)
  (h1 : N1.LC) (h2 : N2.LC) :
  M⟦1 ↝ N1⟧⟦0 ↝ N2⟧.depth <= M.depth.max (N1.depth.max N2.depth) := by
  induction h : M.fokker_size using Nat.strong_induction_on generalizing M with | h n ih =>
  cases M with
  | fvar _ => grind
  | bvar _ => grind
  | abs M => cases M <;> grind
  | app a b =>
      have := @ih _ (by grind) a (by grind) rfl
      have := @ih _ (by grind) b (by grind) rfl
      rw [openRec_app, openRec_app]
      grind

@[scoped grind =]
theorem two_vars_are_enough_fv {t} (h: two_vars_are_enough t) : t.fv = ∅ := by
  induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
    | h n _ => cases t with
  | bvar _ => grind
  | fvar _ => grind
  | app _ _ => grind
  | abs t => induction t with grind


@[scoped grind =]
def abs_two_vars_are_enough: Term String → Bool
  | Term.abs (Term.abs t) => two_vars_are_enough t
  | _ => false

theorem abs_two_vars_are_enough_weak {t} (h: abs_two_vars_are_enough t) :
  t.two_vars_are_enough := by
  unfold abs_two_vars_are_enough at h
  grind

@[scoped grind =]
theorem abs_two_vars_are_enough_fv {t} (h: abs_two_vars_are_enough t) : t.fv = ∅ :=
  two_vars_are_enough_fv (abs_two_vars_are_enough_weak h)

@[scoped grind <-]
theorem abs_two_vars_are_enough_lc {t} (h: abs_two_vars_are_enough t) : t.LC := by
  unfold abs_two_vars_are_enough at h
  split at h <;> grind




@[scoped grind]
def fvar_or_combinator (a: Term String) : Prop :=  a.IsFvar \/ a.abs_two_vars_are_enough

theorem two_vars_are_enough_openRec {t N1 N0}
  (g : two_vars_are_enough t)
  (h1: ClosedUnderApp fvar_or_combinator N1)
  (h2: ClosedUnderApp fvar_or_combinator N0) :
  ClosedUnderApp fvar_or_combinator (t⟦1 ↝ N1⟧⟦0 ↝ N0⟧) := by
  induction t with
  | fvar _ => grind
  | app _ _ => grind
  | abs t => cases t <;> grind
  | bvar a => unfold two_vars_are_enough at g
              have h : a = 0 \/ a = 1 := by grind
              cases h <;> subst_vars
              . grind
              . simp [openRec]
                rw [open_lc] <;> grind

/-
theorem recursive_app_fvar_fvar_or_combinator {i y M}
  (hm : ClosedUnderApp fvar_or_combinator M):
  ClosedUnderApp fvar_or_combinator ((fun a => a.app (fvar y))^[i] (M)) := by
  induction i generalizing M with (simp; grind)
-/


@[scoped grind]
def contain_x (M : Term String) := ∀ Y, M ↠βηᶠ Y -> "x" ∈ Y.fv

theorem beta_eta_nf_contain_x {M N : Term String}
  (steps : M ↠βηᶠ N)
  (h : Relation.Normal FullBetaEta N)
  (hn : "x" ∈ N.fv) : contain_x M  := by
    intros t ht
    obtain ⟨Z, hz1, hz2⟩ := confluent_beta_eta ht steps
    have := Relation.Normal.reflTransGen_eq h hz2
    subst_vars
    apply FullBetaEta.steps_fv at hz1
    apply hz1
    grind

theorem beta_eta_spline_contain_x {Ns : List _} {M : Term String}
  (steps : M ↠βηᶠ (Ns.foldl app (fvar "x"))) : contain_x M  := by
    intros t ht
    obtain ⟨Z, hz1, hz2⟩ := confluent_beta_eta ht steps
    obtain ⟨l, _, _⟩ := beta_eta_steps_preserve_fvar_apps hz2
    subst_vars
    apply FullBetaEta.steps_fv at hz1
    apply hz1
    rw [multiapp_fv]
    grind [union_foldl]

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
