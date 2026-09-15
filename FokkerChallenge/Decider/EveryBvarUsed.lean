import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import Mathlib.Data.Set.Card
import FokkerChallenge.EnhancedCslib.CountBvar
import FokkerChallenge.Basic
import FokkerChallenge.FamousCombinator
import FokkerChallenge.EnhancedCslib.GenFinset

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

@[grind]
def every_bvar_used: Term String → Bool
  | Term.bvar _ => true
  | Term.fvar _ => true
  | Term.abs t => every_bvar_used t && count_bvar 0 t > 0
  | Term.app t1 t2 => every_bvar_used t1 && every_bvar_used t2

/-
  K is not every_bvar_used
-/
theorem K_not_every_bvar_used : every_bvar_used K = false := by
  unfold K every_bvar_used count_bvar every_bvar_used every_bvar_used count_bvar
  simp

/-
  Closure under application
-/
theorem every_bvar_used_app {M N : Term String} :
  every_bvar_used M → every_bvar_used N → every_bvar_used (app M N) := by
  intro hM hN
  grind

/-
  All generated terms are every_bvar_used
-/
theorem Gen_every_bvar_used {Y M : Term String} :
  Gen Y M → every_bvar_used Y -> every_bvar_used M := by
  intro h
  induction h with
  | base => simp_all
  | app hM hN ihM ihN =>  intro h
                          specialize ihM h
                          specialize ihN h
                          grind

theorem open_every_bvar_used {M} :
  (i: Nat) ->
  (N: Term String) ->
  every_bvar_used M →
  every_bvar_used N →
  LC N ->
  every_bvar_used (openRec i N M) := by
  induction M with
  | fvar x => grind
  | bvar n => grind
  | app M1 M2 ih1 ih2 => grind
  | abs M ih =>
      intro i N hM hN h
      unfold every_bvar_used at hM
      simp at hM
      unfold openRec every_bvar_used
      simp
      apply And.intro
      . apply ih <;> tauto
      . rw [<- count_bvar_preserved_under_open] <;> omega

theorem open_every_bvar_used_of_fvar (M : Term String) :
  (x : String) →
  (i : Nat) →
  (openRec i (fvar x) M).every_bvar_used →
  M.every_bvar_used := by
  induction M with
  | bvar _ => grind
  | fvar _ => grind
  | app a b ha hb => grind
  | abs _ ih =>   intros x i g
                  unfold openRec at g
                  unfold every_bvar_used at g
                  simp at g
                  obtain ⟨_, _⟩ := g
                  unfold every_bvar_used
                  simp
                  refine ⟨ih _ _ (by assumption), ?_⟩
                  rwa [<- count_bvar_openRec_fvar]
                  omega


/-
  β preserves every_bvar_used
-/
theorem beta_preserves_every_bvar_used: r_preserves every_bvar_used Beta := by
  intro M N h g
  cases h
  rename_i m n hm hn
  unfold every_bvar_used at g
  simp at g
  obtain ⟨h1, _⟩ := g
  unfold every_bvar_used at h1
  simp at h1
  apply open_every_bvar_used <;> tauto

theorem eta_preserves_every_bvar_used: r_preserves every_bvar_used Eta := by
  intro M N h g
  grind


def r_preserves_free_vars (R : Term String → Term String → Prop) : Prop :=
  ∀ M N, R M N → every_bvar_used M → M.fv = N.fv

theorem xi_preserves_free_vars {R}: r_preserves_free_vars R -> r_preserves_free_vars (Xi R) := by
  intro h9 M N h g
  induction h with
  | base h => apply h9 <;> assumption
  | appL _ _ _ => grind
  | appR _ _ _ => grind
  | abs xs h ih =>  rename_i M N
                    have h4 : ∃ x: String, x ∉ xs ∪ N.fv ∪ M.fv := by apply Finset.exists_not_mem_of_card_lt_enatCard; simp
                    obtain ⟨x, hx⟩ := h4
                    unfold fv
                    have : (M ^ fvar x).every_bvar_used := by apply open_every_bvar_used <;> grind
                    specialize ih x (by grind) (by assumption)
                    unfold every_bvar_used at g
                    simp at g
                    rw [openRec_fv_union, openRec_fv_union] at ih
                    simp at ih
                    any_goals omega
                    apply subset_antisymm
                    . rw [<- Finset.insert_subset_insert_iff]
                      apply superset_of_eq
                      rw [ih]
                      grind
                    . rw [<- Finset.insert_subset_insert_iff]
                      apply superset_of_eq
                      rw [ih]
                      grind
                    have h: count_bvar 0 N = 0 \/ count_bvar 0 N > 0 := by omega
                    cases h <;> grind

theorem beta_preserves_free_vars: r_preserves_free_vars Beta := by
  intro M N h g
  cases h
  rw [openRec_fv_union] <;> grind

theorem eta_preserves_free_vars: r_preserves_free_vars Eta := by
  intro M N h g
  grind

theorem xi_preserves_every_bvar_used {R: Term String → Term String → Prop} :
  r_preserves every_bvar_used R -> r_preserves_free_vars R → r_preserves every_bvar_used (Xi R) := by
  intro h8 h9 M N h g
  induction h with
  | base h => apply h8 <;> assumption
  | appL a b ha => grind
  | appR a b hb => grind
  | abs s h h1 =>   unfold every_bvar_used at g
                    simp at g
                    rename_i M N
                    have h4 : ∃ x : String, x ∉ s ∪ M.fv := by apply Finset.exists_not_mem_of_card_lt_enatCard; simp
                    obtain ⟨x, hx⟩ := h4
                    unfold every_bvar_used
                    simp
                    refine ⟨open_every_bvar_used_of_fvar _ x 0 (h1 _ (by grind) ?_), ?_⟩
                    . apply open_every_bvar_used <;> grind
                    . have g : count_bvar 0 N > 0 \/ count_bvar 0 N = 0 := by omega
                      cases g
                      any_goals assumption
                      exfalso
                      have h4 : ∃ y : String, y ∉ insert x s ∪ M.fv := by apply Finset.exists_not_mem_of_card_lt_enatCard; simp
                      obtain ⟨y, hy⟩ := h4
                      have h4 := h x (by grind)
                      have h5 := h y (by grind)
                      unfold open' at h4 h5
                      rw [@openRec_noop_of_count_bvar_zero N] at h4 h5
                      any_goals assumption
                      apply xi_preserves_free_vars at h9
                      apply h9 at h4
                      apply h9 at h5
                      have : (M ^ fvar x).every_bvar_used := by apply open_every_bvar_used <;> tauto
                      specialize h4 this
                      have : (M ^ fvar y).every_bvar_used := by apply open_every_bvar_used <;> tauto
                      specialize h5 this
                      rw [<- h5, openRec_fv_union, openRec_fv_union] at h4
                      any_goals tauto
                      have h : y ∈ insert x M.fv := by grind
                      grind

theorem fullbeta_preserves_every_bvar_used {M N} :
  FullBeta M N → every_bvar_used M → every_bvar_used N := by
  apply xi_preserves_every_bvar_used beta_preserves_every_bvar_used beta_preserves_free_vars

theorem fullbetastar_preserves_every_bvar_used {M N} :
  Relation.ReflTransGen FullBeta M N → every_bvar_used M → every_bvar_used N := by
  intro h
  induction h with
  | refl => intro hlin; exact hlin
  | tail hβ hstar ih => intro hlin
                        specialize ih hlin
                        apply fullbeta_preserves_every_bvar_used <;> assumption

theorem fulleta_preserves_every_bvar_used {M N} :
  FullEta M N → every_bvar_used M → every_bvar_used N := by
  apply xi_preserves_every_bvar_used eta_preserves_every_bvar_used eta_preserves_free_vars

theorem fulletastar_preserves_every_bvar_used {M N} :
  Relation.ReflTransGen FullEta M N → every_bvar_used M → every_bvar_used N := by
  intro h
  induction h with
  | refl => intro hlin; exact hlin
  | tail hβ hstar ih => intro hlin
                        specialize ih hlin
                        apply fulleta_preserves_every_bvar_used <;> assumption

theorem fullBetaEtastar_preserves_every_bvar_used {M N} :
  Relation.ReflTransGen FullBetaEta M N → every_bvar_used M → every_bvar_used N := by
  intro h
  induction h with
  | refl => intro hlin; exact hlin
  | tail hβ hstar ih => intro hlin
                        specialize ih hlin
                        cases hstar with
                        | inl h =>  apply fullbeta_preserves_every_bvar_used at h
                                    apply h ih
                        | inr h =>  apply fulleta_preserves_every_bvar_used at h
                                    apply h ih

theorem not_reaches_K {X} (h: every_bvar_used X) : not_basis X := by
  exists K
  refine ⟨?_, by grind [K], ?_⟩
  . rw [← lcAt_iff_LC]
    decide
  . intros Y hgen hred
    have hlin := Gen_every_bvar_used hgen
    have hlinK := fullBetaEtastar_preserves_every_bvar_used hred (hlin h)
    rw [K_not_every_bvar_used] at hlinK
    tauto
