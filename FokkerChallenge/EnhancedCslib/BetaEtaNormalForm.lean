import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Congruence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import FokkerChallenge.EnhancedCslib.CountBvar
import FokkerChallenge.EnhancedCslib.BetaNormalForm
import FokkerChallenge.EnhancedCslib.EtaNormalForm
import Mathlib.Data.Finset.Lattice.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

theorem normal_fullBetaEta_iff_no_beta_eta_redex_inner {N} : (N.has_beta_redex = false \/ ¬ N.LC) /\ (N.has_eta_redex = false \/ ¬ N.LC) <-> Relation.Normal FullBetaEta N := by
  rw [normal_fullEta_iff_no_eta_redex, normal_fullBeta_iff_no_beta_redex]
  unfold FullBetaEta
  constructor <;> simp_all

theorem normal_fullBetaEta_iff_no_beta_eta_redex {N} : (N.has_beta_redex = false /\ N.has_eta_redex = false) \/ ¬ N.LC <-> Relation.Normal FullBetaEta N := by
  rw [<- normal_fullBetaEta_iff_no_beta_eta_redex_inner]
  tauto


/--
If `N.abs` has no β-redex and no η-redex anywhere, then `M` reaches `N.abs` by
forward `FullBetaEta` reductions iff they are merely `EqvGen`-related.

The previous `FullBeta`-only version is the special case where `has_eta_redex` is
ignored. Both `has_beta_redex` and `has_eta_redex` are required because either
kind of redex makes `N.abs` non-normal under `FullBetaEta`. In particular, just
asking for `N.fv = ∅` is not enough — e.g. `N := abs (app (bvar 1) (bvar 0))`
satisfies `N.fv = ∅` and `has_beta_redex N = false`, yet
`N.abs = abs (abs (app (bvar 1) (bvar 0)))` reduces by η to `abs (bvar 0)` after
opening the outer binder. The `has_eta_redex` check rules this out.
-/
theorem reflTransGen_iff_eqvGen_of_normal {M N : Term String}
    (hb : N.has_beta_redex = false) (he : N.has_eta_redex = false) :
    Relation.ReflTransGen FullBetaEta M N ↔ Relation.EqvGen FullBetaEta M N := by
  refine ⟨Relation.ReflTransGen.to_eqvGen, ?_⟩
  intro h
  have norm : Relation.Normal FullBetaEta N := by
    rintro ⟨Y, hY⟩
    rcases hY with hbeta | heta
    · have h1 : has_beta_redex N = true := has_beta_redex_of_full_beta hbeta
      rw [hb] at h1
      exact absurd h1 (by decide)
    · have h1 : has_eta_redex N = true := has_eta_redex_of_full_eta heta
      rw [he] at h1
      exact absurd h1 (by decide)
  exact Relation.ChurchRosser.normal_eqvGen_reflTransGen
    (Relation.Confluent.toChurchRosser confluent_beta_eta) norm h

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
