import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import Mathlib.Data.Set.Card
import FokkerChallenge.Basic
import FokkerChallenge.EnhancedCslib.Basic
import FokkerChallenge.EnhancedCslib.CountFvar
import FokkerChallenge.EnhancedCslib.FvarSubset
import FokkerChallenge.FamousCombinator

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

def no_duplicate: Term String → Bool
  | Term.bvar _ => true
  | Term.fvar _ => true
  | Term.abs t => no_duplicate t && count_bvar 0 t < 2
  | Term.app t1 t2 => no_duplicate t1 && no_duplicate t2

theorem open_no_duplicate_2 {M N} :
  (i j: Nat) ->
  ¬ i = j →
  count_bvar j M < 2 →
  N.LC →
  count_bvar j (openRec i N M) <= 1 := by
  induction M with
  | bvar _ => intros _ _ _ _ lcn
              unfold openRec
              split
              . rw [count_bvar_0_of_locally_closed lcn]
                omega
              . unfold count_bvar
                split <;> omega
  | fvar _ => intros _ _ _ _ _
              unfold openRec
              unfold count_bvar
              omega
  | abs M ih => intros i j _ hm _
                unfold openRec
                simp only [count_bvar]
                unfold count_bvar at hm
                simp at hm
                apply ih
                all_goals omega
  | app a b ha hb =>  intros i j _ hndm lcn
                      unfold openRec
                      simp only [count_bvar]
                      unfold count_bvar at hndm
                      simp at hndm
                      specialize ha i j (by tauto) (by omega) lcn
                      specialize hb i j (by tauto) (by omega) lcn
                      rw [<- count_bvar_preserved_under_open]
                      rw [<- count_bvar_preserved_under_open]
                      all_goals omega

theorem open_no_duplicate {M N} :
  (i: Nat) ->
  no_duplicate M →
  no_duplicate N →
  LC N ->
  no_duplicate (openRec i N M) := by
  induction M with
  | bvar _ => intros hnd _ _
              unfold openRec
              split <;> tauto
  | fvar _ => intros hnd _ _ _
              unfold openRec
              trivial
  | abs M ih => intros i hndM hndN _
                unfold openRec
                simp only [no_duplicate]
                unfold no_duplicate at hndM
                simp at hndM
                simp
                apply And.intro
                · apply ih <;> tauto
                · apply open_no_duplicate_2 <;> omega
  | app a b ha hb =>  intros i hndM hndN lcn
                      unfold openRec
                      simp only [no_duplicate]
                      simp
                      unfold no_duplicate at hndM
                      simp at hndM
                      specialize ha i (by tauto) (by tauto) lcn
                      specialize hb i (by tauto) (by tauto) lcn
                      tauto

theorem open_no_duplicate_fvar (M : Term String) :
  (x : String) →
  (i : Nat) →
  (openRec i (fvar x) M).no_duplicate →
  M.no_duplicate := by
  induction M with
  | bvar _ => tauto
  | fvar _ => tauto
  | abs M ih => intros x i hnd
                unfold openRec at hnd
                simp only [no_duplicate] at hnd
                simp only [no_duplicate]
                simp at hnd
                simp
                apply And.intro
                · apply ih <;> tauto
                · rw [<- count_bvar_openRec_fvar]
                  tauto
                  omega
  | app a b ha hb =>  intros x i hnd
                      unfold openRec at hnd
                      simp only [no_duplicate] at hnd
                      simp only [no_duplicate]
                      simp at hnd
                      simp
                      specialize ha x i (by tauto)
                      specialize hb x i (by tauto)
                      tauto

theorem beta_preserves_no_duplicate: r_preserves no_duplicate Beta := by
  intros M N hmn hnd
  cases hmn
  rename_i M N h lcn
  unfold no_duplicate at hnd
  simp at hnd
  obtain ⟨g, _⟩ := hnd
  unfold no_duplicate at g
  simp at g
  apply open_no_duplicate
  all_goals tauto

theorem eta_preserves_no_duplicate: r_preserves no_duplicate Eta := by
  intros M N hmn hnd
  cases hmn
  rename_i lcn
  unfold no_duplicate at hnd
  simp at hnd
  obtain ⟨g, _⟩ := hnd
  unfold no_duplicate at g
  simp at g
  tauto

def r_preserves_fvar (R : Term String → Term String → Prop) : Prop :=
  ∀ M N x, R M N → count_fvar x M <= 1 -> no_duplicate M → count_fvar x N <= 1

theorem beta_preserves_fvar: r_preserves_fvar Beta := by
  intros M N x hmn hcfv hnd
  cases hmn
  rename_i M N h lcn
  unfold count_fvar at hcfv
  unfold no_duplicate at hnd
  simp at hnd
  obtain ⟨g, _⟩ := hnd
  unfold no_duplicate at g
  simp at g
  obtain ⟨_, g⟩ := g
  conv at hcfv =>
    left
    left
    unfold count_fvar
  unfold open'
  rw [count_fvar_openRec_distrib]
  have h : count_fvar x M = 0 \/ count_fvar x M = 1 := by omega
  cases h
  all_goals rename_i h
  all_goals rw [h] at hcfv
  all_goals simp at hcfv
  all_goals rw [h]
  all_goals simp
  any_goals omega
  have h:= Nat.mul_le_mul g hcfv
  simp at h
  omega

theorem eta_preserves_fvar: r_preserves_fvar Eta := by
  intros M N x hmn hcfv hnd
  cases hmn
  unfold count_fvar at hcfv
  unfold no_duplicate at hnd
  simp at hnd
  obtain ⟨g, _⟩ := hnd
  unfold no_duplicate at g
  simp at g
  obtain ⟨g, _⟩ := g
  unfold count_fvar at hcfv
  conv at hcfv =>
    left
    right
    unfold count_fvar
  simp at hcfv
  omega


theorem xi_preserves_fvar {R}:  r_preserves_fvar_subset (Xi R) ->
                                r_preserves_fvar R ->
                                r_preserves_fvar (Xi R) := by
  intros g hR M N x hxi hcfv hnd
  induction hxi with
  | base _ => tauto
  | appL _ _ ih =>  unfold count_fvar at hcfv
                    unfold count_fvar
                    unfold no_duplicate at hnd
                    simp at hnd
                    rename_i Z M N _ _
                    have h: count_fvar x Z = 0 \/ count_fvar x Z = 1 := by omega
                    cases h <;> rename_i h <;> rw [h] at hcfv <;> rw [h] <;> simp
                    . apply ih
                      omega
                      tauto
                    . simp at hcfv
                      rw [<- count_fvar_eq_zero_of_not_in_fv]
                      rw [<- count_fvar_eq_zero_of_not_in_fv] at hcfv
                      intros h
                      apply hcfv
                      apply g <;> assumption
  | appR _ _ ih =>  unfold count_fvar at hcfv
                    unfold count_fvar
                    unfold no_duplicate at hnd
                    simp at hnd
                    rename_i Z M N _ _
                    have h: count_fvar x Z = 0 \/ count_fvar x Z = 1 := by omega
                    cases h <;> rename_i h <;> rw [h] at hcfv <;> rw [h] <;> simp
                    . apply ih
                      omega
                      tauto
                    . simp at hcfv
                      rw [<- count_fvar_eq_zero_of_not_in_fv]
                      rw [<- count_fvar_eq_zero_of_not_in_fv] at hcfv
                      intros h
                      apply hcfv
                      apply g <;> assumption
  | abs xs _ ih =>  rename_i M N _
                    have h4 : ∃ y: String, y ∉ insert x xs ∪ N.fv ∪ M.fv := by apply Finset.exists_not_mem_of_card_lt_enatCard; simp
                    obtain ⟨y, hx⟩ := h4
                    specialize ih y (by grind)
                    unfold count_fvar
                    unfold count_fvar at hcfv
                    unfold no_duplicate at hnd
                    simp at hnd
                    unfold open' at ih
                    rw [count_fvar_openRec_distrib] at ih
                    rw [count_fvar_openRec_distrib] at ih
                    have h: count_fvar x (fvar y) = 0 := by unfold count_fvar
                                                            grind
                    rw [h] at ih
                    simp at ih
                    apply ih
                    assumption
                    apply open_no_duplicate <;> tauto



theorem xi_preserves_no_duplicate {R: Term String → Term String → Prop} :
  r_preserves_fvar R ->
  r_preserves_fvar_subset (Xi R) ->
  r_preserves no_duplicate R →
  r_preserves no_duplicate (Xi R) := by
  intros _ g hR M N hxi hnd
  induction hxi with
  | base _ => tauto
  | appL _ _ ih =>  unfold no_duplicate at hnd
                    simp at hnd
                    specialize ih (by tauto)
                    unfold no_duplicate
                    simp
                    tauto
  | appR _ _ ih =>  unfold no_duplicate at hnd
                    simp at hnd
                    specialize ih (by tauto)
                    unfold no_duplicate
                    simp
                    tauto
  | abs s h ih =>   rename_i M N
                    unfold no_duplicate at hnd
                    simp at hnd
                    unfold no_duplicate
                    simp
                    have h4 : ∃ x : String, x ∉ s := by apply Finset.exists_not_mem_of_card_lt_enatCard; simp
                    obtain ⟨x, hx⟩ := h4
                    apply And.intro
                    . apply open_no_duplicate_fvar
                      apply ih _ hx
                      apply open_no_duplicate <;> tauto
                    . have h4 : ∃ y: String, y ∉ insert x s ∪ N.fv ∪ M.fv := by apply Finset.exists_not_mem_of_card_lt_enatCard; simp
                      obtain ⟨y, hy⟩ := h4
                      specialize h y (by grind)
                      apply xi_preserves_fvar at h
                      any_goals assumption
                      unfold open' at h
                      rw [count_fvar_openRec_distrib] at h
                      rw [count_fvar_openRec_distrib] at h
                      conv at h =>
                        lhs
                        left
                        left
                        right
                        unfold count_fvar
                        simp
                      conv at h =>
                        right
                        right
                        left
                        left
                        right
                        unfold count_fvar
                        simp
                      simp at h
                      have g: count_fvar y M = 0 := by rw [<- count_fvar_eq_zero_of_not_in_fv]; grind
                      rw [g] at h
                      have g: count_fvar y N = 0 := by rw [<- count_fvar_eq_zero_of_not_in_fv]; grind
                      rw [g] at h
                      simp at h
                      apply h
                      tauto
                      apply open_no_duplicate <;> tauto

theorem fullbeta_preserves_no_duplicate {M N} :
  FullBeta M N → no_duplicate M → no_duplicate N := by
  apply xi_preserves_no_duplicate beta_preserves_fvar beta_preserves_fvar_subset beta_preserves_no_duplicate

theorem fullbetastar_preserves_no_duplicate {M N} :
  Relation.ReflTransGen FullBeta M N → no_duplicate M → no_duplicate N := by
  intro h
  induction h with
  | refl => intro hlin; exact hlin
  | tail hβ hstar ih => intro hlin
                        specialize ih hlin
                        apply fullbeta_preserves_no_duplicate <;> assumption

theorem fulleta_preserves_no_duplicate {M N} :
  FullEta M N → no_duplicate M → no_duplicate N := by
  apply xi_preserves_no_duplicate eta_preserves_fvar eta_preserves_fvar_subset eta_preserves_no_duplicate

theorem fulletastar_preserves_no_duplicate {M N} :
  Relation.ReflTransGen FullEta M N → no_duplicate M → no_duplicate N := by
  intro h
  induction h with
  | refl => intro hlin; exact hlin
  | tail hβ hstar ih => intro hlin
                        specialize ih hlin
                        apply fulleta_preserves_no_duplicate <;> assumption

theorem fullBetaEtastar_preserves_no_duplicate {M N} :
  Relation.ReflTransGen FullBetaEta M N → no_duplicate M → no_duplicate N := by
  intro h
  induction h with
  | refl => intro hlin; exact hlin
  | tail hβ hstar ih => intro hlin
                        specialize ih hlin
                        cases hstar with
                        | inl h =>  apply fullbeta_preserves_no_duplicate at h
                                    apply h ih
                        | inr h =>  apply fulleta_preserves_no_duplicate at h
                                    apply h ih


theorem omega_not_no_duplicate: no_duplicate M = false := by
  simp [M, no_duplicate, count_bvar]


theorem Gen_no_duplicate {Y M : Term String} :
  Gen Y M → no_duplicate Y -> no_duplicate M := by
  intro h
  induction h with
  | base => simp
  | app hM hN ihM ihN =>  intro h
                          specialize ihM h
                          specialize ihN h
                          unfold no_duplicate
                          simp_all

theorem not_reaches_omega {X} (h : no_duplicate X) : not_basis X := by
  exists M
  refine ⟨?_, ?_, ?_⟩
  . rw [← lcAt_iff_LC]
    decide
  . grind [M]
  . intros Y hgen hred
    have hlin := Gen_no_duplicate hgen
    have hlinK := fullBetaEtastar_preserves_no_duplicate hred (hlin h)
    rw [omega_not_no_duplicate] at hlinK
    tauto
