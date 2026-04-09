import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import Mathlib.Data.Set.Card
import FokkerChallenge.EnhancedCslib.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

@[scoped grind]
def r_preserves_fvar_subset (R : Term String → Term String → Prop) : Prop :=
  ∀ M N, R M N → N.fv ⊆ M.fv

theorem beta_preserves_fvar_subset: r_preserves_fvar_subset FullBeta := by grind [FullBeta.step_not_fv]

theorem eta_preserves_fvar_subset: r_preserves_fvar_subset FullEta := by grind [FullEta.step_not_fv]
