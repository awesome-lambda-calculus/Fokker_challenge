import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import FokkerChallenge.EnhancedCslib.BetaEtaNormalForm

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-
  K = λx y. x
-/
def K : Term String := abs (abs (bvar 1))

theorem normal_K : Relation.Normal FullBetaEta K := by
  rw [<- normal_fullBetaEta_iff_no_beta_eta_redex]
  decide

def S : Term String :=
abs (abs (abs (
    app (app (bvar 2) (bvar 0))   -- x z
        (app (bvar 1) (bvar 0))   -- y z
  )))

/-
  M combinator in BAMT combinator systems
  M = λx.x x
-/
def M : Term String := abs (app (bvar 0) (bvar 0))

-- H0xy       = x(yy)
-- H(n + 1)xy = x(y(Hn))
@[simp, scoped grind =]
def H : Nat -> Term String
| 0 => ((bvar 1).app ((bvar 0).app (bvar 0))).abs.abs
| .succ n => ((bvar 1).app ((bvar 0).app (H n))).abs.abs

@[simp, scoped grind =]
theorem H_fv {n} : (H n).fv = ∅ := by induction n with grind

@[simp, scoped grind]
theorem H.LC {n} : (H n).LC := by
  rw [<- lcAt_iff_LC]
  induction n with
  | zero => simp
  | succ n h => simp
                exact lcAt_le _ _ _ (by omega) h

theorem normal_H {n} : Relation.Normal FullBetaEta (H n) := by
  induction n with rw [<- normal_fullBetaEta_iff_no_beta_eta_redex]
  | zero => decide
  | succ n h =>
    left
    rw [<- normal_fullBetaEta_iff_no_beta_eta_redex] at h
    refine ⟨?_, ?_⟩
    . simp [has_beta_redex]
      cases h with grind [H.LC]
    . simp [has_eta_redex]
      cases h with grind [H.LC]

theorem H_succ_reduce {n} : ((H (n + 1)).app (fvar "x")).app (fvar "y") ↠βᶠ ((fvar "x").app ((fvar "y").app (H n))) := by
    apply Relation.ReflTransGen.head
    apply Xi.appR
    grind
    apply Xi.base
    apply Beta.beta
    have : H (n+1) = ((bvar 1).app ((bvar 0).app (H n))).abs.abs := by simp
    rw [<- this]
    grind [H.LC]
    grind
    refine Relation.ReflTransGen.single (Xi.base ?_)
    unfold open' openRec openRec openRec
    rw [openRec_bvar, open_lc]
    split <;> try grind
    have : (((fvar "x").app ((bvar 0).app (H n))).open' (fvar "y")) =
           (((fvar "x").app ((fvar "y").app (H n)))) := by
      unfold open' openRec openRec
      rw [openRec_bvar, open_lc]
      split <;> grind
      grind [H.LC]
    rw [<- this]
    apply Beta.beta
    apply LC.abs ∅
    grind [H.LC]
    grind
    grind [H.LC]

theorem H_0_reduce : ((H 0).app (fvar "x")).app (fvar "y") ↠βᶠ ((fvar "x").app ((fvar "y").app (fvar "y"))) := by
    apply Relation.ReflTransGen.head
    apply Xi.appR
    grind
    apply Xi.base
    apply Beta.beta
    rw [<- lcAt_iff_LC]
    decide
    grind
    refine .head ((Xi.base (.beta ?_ (by grind)))) ?_
    unfold openRec openRec openRec
    split <;> try grind
    split <;> try grind
    rw [<- lcAt_iff_LC]
    decide
    unfold openRec openRec openRec
    split <;> grind
