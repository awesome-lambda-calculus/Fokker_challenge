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
