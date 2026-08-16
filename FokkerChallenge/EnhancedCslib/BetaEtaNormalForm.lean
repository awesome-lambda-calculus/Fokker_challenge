import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Congruence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.EtaPostpone
import FokkerChallenge.EnhancedCslib.CountBvar
import FokkerChallenge.EnhancedCslib.BetaNormalForm
import FokkerChallenge.EnhancedCslib.EtaNormalForm
import FokkerChallenge.EnhancedCslib.Closedunderapp
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

theorem exists_beta_normal_fvar_app_of_beta_eta {Y: Term String} {x} :
  Relation.Normal FullBetaEta ((fvar x).app Y) ↔ Relation.Normal FullBetaEta Y := by
  constructor <;> intros h g <;> apply h <;> obtain ⟨M, g⟩ := g
  . exact ⟨(fvar x).app M, FullBetaEta.step_app_r_cong g (by grind)⟩
  . cases g <;> rename_i g <;> cases g <;> try grind
    . rename_i N _ _
      refine ⟨N, ?_⟩
      left
      grind
    . rename_i g _
      cases g with | base g => cases g
    . rename_i N _ _
      refine ⟨N, ?_⟩
      right
      grind
    . rename_i g _
      cases g with | base g => cases g

theorem betaeta_nf_fvar {x : String} :
  Relation.Normal FullBetaEta (fvar x) := by
  rintro ⟨y, h⟩
  cases h with
  | inl h => cases h with | base h => cases h
  | inr h => cases h with | base h => cases h


theorem beta_eta_star_of_beta_normal {M N : Term String} (h : Relation.Normal FullBeta M) (steps : M ↠βηᶠ N) :
    M ↠ηᶠ N := by
  induction steps using Relation.ReflTransGen.head_induction_on with
  | refl => grind
  | head h' h ih => cases h' with
    | inl h' => grind
    | inr h' => exact .head h' (ih (Etastar_normal (.single h') h))

theorem betaeta_nf_app {M N : Term String}
  (h : ¬ M.IsAbs)
  (hm : Relation.Normal FullBetaEta M)
  (hn : Relation.Normal FullBetaEta N) :
  Relation.Normal FullBetaEta (M.app N) := by
  rintro ⟨y, h⟩
  cases h with
  | inl h => cases h with
    | base h => cases h with | beta _ _ => grind
    | appL _ h => apply hn
                  refine ⟨_, by left; exact h⟩
    | appR _ h => apply hm
                  refine ⟨_, by left; exact h⟩
  | inr h => cases h with
    | base h => cases h
    | appL _ h => apply hn
                  refine ⟨_, by right; exact h⟩
    | appR _ h => apply hm
                  refine ⟨_, by right; exact h⟩


theorem betaeta_nf_bfvar {M : Term String} (h : M.IsFvar \/ M.IsBvar) :
  Relation.Normal FullBetaEta M /\ ¬ M.IsAbs := by
  cases h with
  | inl h =>  cases h
              refine ⟨?_, by grind⟩
              rintro ⟨y, h⟩
              cases h with
              | inl h => cases h with | base h => cases h
              | inr h => cases h with | base h => cases h
  | inr h =>  cases h
              refine ⟨?_, by grind⟩
              rintro ⟨y, h⟩
              cases h with
              | inl h => cases h with | base h => cases h
              | inr h => cases h with | base h => cases h

theorem app_betaeta_nf_bfvar {M : Term String}
  (h :  ClosedUnderApp (fun t => t.IsFvar \/ t.IsBvar) M) :
  Relation.Normal FullBetaEta M /\ ¬ M.IsAbs := by
  induction h with
  | base _ => grind [betaeta_nf_bfvar]
  | app _ _ _ _ => exact ⟨betaeta_nf_app (by grind) (by grind) (by grind), by grind⟩


end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
