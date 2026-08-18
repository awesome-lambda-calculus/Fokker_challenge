import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import Mathlib.Data.Set.Card
import FokkerChallenge.EnhancedCslib.CountBvar
import FokkerChallenge.EnhancedCslib.FvarSubset
import FokkerChallenge.Basic
import FokkerChallenge.FamousCombinator
import FokkerChallenge.EnhancedCslib.GenFinset

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

@[simp, scoped grind =]
def only_one_var_used: Term String → Bool
| bvar _ => true
| fvar _ => true
| app t1 t2 => only_one_var_used t1 && only_one_var_used t2
| abs t => (count_bvar 0 t = count_bvar_all t) || (only_one_var_used t && count_bvar 0 t = 0)

theorem openrec_only_one_var_used {M N} (n_lc: N.LC) (hn: only_one_var_used N) :
  (i: Nat) ->
  count_bvar i M = M.count_bvar_all ->
  only_one_var_used (openRec i N M) := by
  induction M with
  | bvar _ => grind
  | fvar _ => grind
  | app a b ha hb =>  intros i h
                      have := @count_bvar_le_count_bvar_all a i
                      have := @count_bvar_le_count_bvar_all b i
                      grind
  | abs M ih => intros i h
                simp [openRec, only_one_var_used] at *
                right
                simp_all
                apply count_bvar_j_zero_after_openrec_i <;> assumption

theorem beta_preserves_only_one_var_used: r_preserves only_one_var_used Beta := by
  intro M N h g
  cases h
  rename_i m n hm hn
  simp [only_one_var_used] at g
  cases g
  rename_i g _
  cases g
  . apply openrec_only_one_var_used <;> assumption
  . grind

theorem eta_preserves_only_one_var_used: r_preserves only_one_var_used Eta := by
  intro M N h g
  cases h
  unfold only_one_var_used at g
  simp at g
  rw [count_bvar_0_of_locally_closed] at g <;> try assumption
  rename_i h
  clear h
  induction N with
  | bvar _ => grind
  | fvar _ => grind
  | app _ _ _ _ => grind
  | abs N _ =>  unfold only_one_var_used
                simp_all
                rw [<- g]
                have := @count_bvar_le_count_bvar_all N 0
                omega

theorem xi_preserves_only_one_var_used {R: Term String → Term String → Prop} :
  r_preserves_fvar_subset (Xi R) ->
  r_preserves (fun x => count_bvar_all x = 0) R ->
  r_preserves only_one_var_used R ->
  r_preserves only_one_var_used (Xi R) := by
  intro h9 h7 h8 M N h
  induction h with
  | base _ => tauto
  | appL _ _ _ => grind
  | appR _ _ _ => grind
  | abs xs h ih =>  rename_i M N
                    have h4 : ∃ x: String, x ∉ xs ∪ N.fv ∪ M.fv := by apply Finset.exists_not_mem_of_card_lt_enatCard; simp
                    obtain ⟨y, h4⟩ := h4
                    specialize ih y (by grind)
                    specialize h y (by grind)
                    intros hm
                    unfold only_one_var_used at hm
                    simp at hm
                    cases hm with
                    | inl hm => simp [only_one_var_used]
                                left
                                rw [@openRec_bvar_all_eq_zero_of_count_bvar_eq_total y] at hm
                                have g := xi_preserves_count_bvar_all_eq_0 h9 h7 _ _ h
                                simp at g
                                specialize g hm
                                rw [<- openRec_bvar_all_eq_zero_of_count_bvar_eq_total] at g
                                assumption
                    | inr hm => obtain ⟨_, hm⟩ := hm
                                apply openRec_noop_of_count_bvar_zero at hm
                                pick_goal 2
                                exact (fvar y)
                                unfold open' at h ih
                                rw [hm] at h ih
                                simp [only_one_var_used]
                                right
                                specialize h9 _ _ h
                                have g: count_bvar 0 N = 0 \/ count_bvar 0 N > 0 := by omega
                                cases g with
                                | inl g => grind
                                | inr g =>  apply openRec_fv_union at g
                                            pick_goal 2
                                            exact (fvar y)
                                            grind


theorem fullbeta_preserves_only_one_var_used {M N} :
  FullBeta M N → only_one_var_used M → only_one_var_used N := by
  apply xi_preserves_only_one_var_used beta_preserves_fvar_subset beta_preserves_count_bvar_all_eq_0 beta_preserves_only_one_var_used

theorem fullbetastar_preserves_only_one_var_used {M N} :
  Relation.ReflTransGen FullBeta M N → only_one_var_used M → only_one_var_used N := by
  intro h
  induction h with
  | refl => intro hlin; exact hlin
  | tail hβ hstar ih => intro hlin
                        specialize ih hlin
                        apply fullbeta_preserves_only_one_var_used <;> assumption

theorem fulleta_preserves_only_one_var_used {M N} :
  FullEta M N → only_one_var_used M → only_one_var_used N := by
  apply xi_preserves_only_one_var_used eta_preserves_fvar_subset eta_preserves_count_bvar_all_eq_0 eta_preserves_only_one_var_used

theorem fulletastar_preserves_only_one_var_used {M N} :
  Relation.ReflTransGen FullEta M N → only_one_var_used M → only_one_var_used N := by
  intro h
  induction h with
  | refl => intro hlin; exact hlin
  | tail hβ hstar ih => intro hlin
                        specialize ih hlin
                        apply fulleta_preserves_only_one_var_used <;> assumption

theorem fullBetaEtastar_preserves_only_one_var_used {M N} :
  Relation.ReflTransGen FullBetaEta M N → only_one_var_used M → only_one_var_used N := by
  intro h
  induction h with
  | refl => intro hlin; exact hlin
  | tail hβ hstar ih => intro hlin
                        specialize ih hlin
                        cases hstar with
                        | inl h =>  apply fullbeta_preserves_only_one_var_used at h
                                    apply h ih
                        | inr h =>  apply fulleta_preserves_only_one_var_used at h
                                    apply h ih


theorem omega_not_only_one_var_used: only_one_var_used S = false := by
  simp [S, only_one_var_used, count_bvar]


theorem Gen_only_one_var_used {Y M : Term String} :
  Gen Y M → only_one_var_used Y -> only_one_var_used M := by
  intro h
  induction h with
  | base => simp_all
  | app hM hN ihM ihN =>  intro h
                          specialize ihM h
                          specialize ihN h
                          unfold only_one_var_used
                          simp_all

theorem only_one_var_used_not_reaches_S {X} (h : only_one_var_used X) : not_basis X := by
  exists S
  refine ⟨?_, ?_, ?_⟩
  . rw [← lcAt_iff_LC]
    decide
  . grind [S]
  . intros Y hgen hred
    have hlin := Gen_only_one_var_used hgen
    have hlinK := fullBetaEtastar_preserves_only_one_var_used hred (hlin h)
    rw [omega_not_only_one_var_used] at hlinK
    tauto

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
