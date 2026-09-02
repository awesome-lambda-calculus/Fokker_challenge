import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.MultiApp
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LeftmostReduction
import Cslib.Foundations.Data.HasFresh
import FokkerChallenge.TwoVarsAreNotEnough.Basic
import FokkerChallenge.TwoVarsAreNotEnough.Head2
import FokkerChallenge.TwoVarsAreNotEnough.Unroll
import FokkerChallenge.TwoVarsAreNotEnough.Q
import FokkerChallenge.TwoVarsAreNotEnough.U
import FokkerChallenge.TwoVarsAreNotEnough.Subterms
import FokkerChallenge.TwoVarsAreNotEnough.TwoVarBlocks

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

theorem exists_head_reduction_to_fvar_app {M N x}
  (hm : ClosedUnderApp fvar_or_combinator M)
  (hn :  Relation.Normal FullBetaEta N)
  (steps : M ↠βηᶠ (fvar x).app N) :
  ∃ l i Z, (List.replicate i (fvar "y")).foldl app M ↠𝒽 List.foldl app (fvar x) (Z::l) /\ Z ↠βηᶠ N := by
  have h_betaeta_nf : Relation.Normal FullBetaEta ((fvar x).app N) := by
    rw [exists_beta_normal_fvar_app_of_beta_eta]
    grind
  have h : Relation.Normalizable FullBetaEta M := ⟨_, steps, h_betaeta_nf⟩
  have h_beta_nf := h
  rw [<- hasBetaEtaNF_iff_hasBetaNF] at h_beta_nf
  obtain ⟨beta_nf, beta_steps, h_beta_nf⟩ := h_beta_nf
  obtain ⟨Z, hz1, hz2⟩ := confluent_beta_eta steps (Relation.ReflTransGen.mono le_sup_left _ _ beta_steps)
  have := Relation.Normal.reflTransGen_eq h_betaeta_nf hz1
  subst Z
  have eta_steps : beta_nf ↠ηᶠ List.foldl app (fvar x) [N] := beta_eta_star_of_beta_normal h_beta_nf hz2
  have : M.LC := closedunderapp_lc (by grind) hm
  have beta_nf_lc : beta_nf.LC := by cases FullBeta.steps_lc_or_rfl beta_steps <;> grind
  obtain ⟨i, E, l, beta_nf_eq, _, he, _, _, _, _⟩ := betaNF_etaStar_shape_len_one_openDown_fv beta_nf_lc h_beta_nf eta_steps
  have h1 := steps_multiApp_l (Ns := List.replicate i (fvar "y")) beta_steps (by grind)
  rw [beta_nf_eq] at h1
  obtain h2 := redex_n_apps_n_abs_of_apps "y" (List.foldl app (fvar x) (E :: l)) i (by grind)
  rw [openDown_multiapp, openDown_fvar] at h2
  have recursive_app_lc : (List.foldl app (fvar x) (List.map (openDown i (fvar "y")) (E :: l))).LC := by
    cases FullBeta.steps_lc_or_rfl (h1.trans h2) with
    | inl h => grind
    | inr h =>  rw [<- h, multiApp_lc]
                grind
  have hnf : HasHNF _ := ⟨_, h1.trans h2, .neutral ((multiapp_headneutral (by grind)))⟩
  rw [hasHNF_iff_headStepStar_headNF] at hnf
  obtain ⟨P, hsteps, hnf⟩ := hnf
  obtain ⟨Z, hz1, hz2⟩ := confluent_fullBeta (h1.trans h2) (HeadStepStar.toFullBetaStar hsteps)
  obtain ⟨l', _, hl'⟩ := beta_steps_preserve_fvar_apps hz1
  subst Z
  obtain ⟨l'', _, hl''⟩:= steps_headnf_preserve_multiapp hnf hz2
  subst P
  have hm2 : ClosedUnderApp fvar_or_combinator M := closedunderapp_derive (by grind) _ hm
  have h2steps := HeadReduction2.headneutral_exists (closedunderapp_multiapp_cons (by grind) (by grind)) (HeadNF.of_not_isAbs hnf (by cases l'' using List.reverseRecOn <;> grind)) hsteps
  cases hl' with | cons hl' _ =>
  cases hl'' with | cons hl'' _ =>
  rw [openDown_lc (by assumption)] at hl'
  obtain ⟨Z, hz1, hz2⟩ := confluent_beta_eta (Relation.ReflTransGen.mono le_sup_right _ _ he) (Relation.ReflTransGen.mono le_sup_left _ _ hl')
  have := Relation.Normal.reflTransGen_eq (by grind) hz1
  subst Z
  exact ⟨_, _, _, h2steps, .trans (Relation.ReflTransGen.mono le_sup_left _ _ hl'') hz2⟩



theorem no_reduction_to_Hn_with_depth_bound_U {n M}
  (hm : ClosedUnderApp (U n "y" "x") M)
  (steps : M ↠βηᶠ (fvar "x").app ((fvar "y").app (H n))) : False := by
  induction n using Nat.strong_induction_on generalizing M with | h n ih =>
  obtain ⟨l, i, N, h, steps⟩ := exists_head_reduction_to_fvar_app (closedunderapp_derive2 U_le_fvar_or_combinator _ hm) (by rw [exists_beta_normal_fvar_app_of_beta_eta]; apply normal_H) steps
  have hn := HeadReduction2_steps_preserve_closedUnderApp_U h (U_replicate hm)
  apply U_foldl_z at hn
  obtain ⟨l, i, Z, h, steps⟩ := exists_head_reduction_to_fvar_app (closedunderapp_derive2 U_le_fvar_or_combinator _ hn) normal_H steps
  have hz := HeadReduction2_steps_preserve_closedUnderApp_U h (U_replicate hn)
  apply U_foldl_x at hz
  have steps := FullBetaEta.steps_subst_cong_l _ _ _ "y" (FullBetaEta.steps_subst_cong_l _ _ _ "x" steps (LC.fvar "z")) (LC.fvar "z")
  rw [subst_fresh "x" (H n) _ (by grind), subst_fresh "y" (H n) _ (by grind)] at steps
  have steps := FullBetaEta.steps_app_l_cong (FullBetaEta.steps_app_l_cong steps (LC.fvar "x")) (LC.fvar "y")
  have hz := U_subst_x_closedunderapp "z" (by grind) (U_subst_z_closedunderapp "z" (by grind) hz)
  cases n with
  | zero => have steps := steps.trans (Relation.ReflTransGen.mono le_sup_left _ _ H_0_reduce)
            obtain ⟨l, i, _, h2steps, hw⟩ := exists_head_reduction_to_fvar_app (.app (.app (closedunderapp_derive2 U_le_fvar_or_combinator _ hz) (by grind)) (by grind)) (by rw [exists_beta_normal_fvar_app_of_beta_eta]; apply betaeta_nf_fvar) steps
            have g := steps_multiApp_l_union (Ns := List.replicate i (fvar "y")) steps (by grind)
            have heq : (List.foldl app ((fvar "x").app ((fvar "y").app (fvar "y"))) (List.replicate i (fvar "y"))) = (List.foldl app (fvar "x") (((fvar "y").app (fvar "y")) :: List.replicate i (fvar "y"))) := by grind
            unfold multiApp at g
            rw [heq] at g
            obtain ⟨_, hq, _⟩ := steps_closedUnderApp_unroll_q (M := Z["x" := fvar "z"]["y" := fvar "z"]) (closedunderapp_derive2 U_le_fvar_or_combinator _ hz) ⟨beta_eta_spline_contain_x g, closedunderapp_multiapp_cons (by grind) (by grind), closedunderapp_multiapp_cons (by grind) (.app (.app (closedunderapp_derive2 U_le_fvar_or_combinator _ (by assumption)) (by grind)) (by grind))⟩ _ h2steps
            apply FullBetaEta.steps_fv at hw
            apply (app_U_transform "x") at hz
            have hq := closedUnderApp_q_of_foldl_app "y" (by grind) (by grind [app_U_fv (by assumption)]) hq
            cases hq with | base hq =>
            rcases hq with _|hq|_ <;> try grind
            have g : ClosedUnderApp (U 0 "x" "z") (Z["x" := fvar "z"]["y" := fvar "z"].app (fvar "x")) := by grind
            obtain ⟨l, steps, hl⟩ := closedUnderApp_reduce_to_head_apps "x" "z" 0 (by grind) g (by grind) hq
            cases l with
            | cons head tail => specialize hl head (by grind)
                                grind
            | nil =>  simp at steps
                      apply app_U0 at g
                      apply app_betaeta_nf_bfvar at g
                      rw [FullBetaEta.normal_fullbeta_iff] at g
                      have g := Relation.Normal.reflTransGen_eq (by grind) steps
                      cases g
  | succ n =>
      have steps := steps.trans (Relation.ReflTransGen.mono le_sup_left _ _ H_succ_reduce)
      obtain ⟨l, i, _, h2steps, hw⟩ := exists_head_reduction_to_fvar_app (.app (.app (closedunderapp_derive2 U_le_fvar_or_combinator _ hz) (by grind)) (by grind)) (by rw [exists_beta_normal_fvar_app_of_beta_eta]; apply normal_H) steps
      have g := steps_multiApp_l_union (Ns := List.replicate i (fvar "y")) steps (by grind)
      have heq : (List.foldl app ((fvar "x").app ((fvar "y").app (H n))) (List.replicate i (fvar "y"))) = (List.foldl app (fvar "x") ( ((fvar "y").app (H n)) :: List.replicate i (fvar "y"))) := by grind
      unfold multiApp at g
      rw [heq] at g
      obtain ⟨_, hq, _⟩ := steps_closedUnderApp_unroll_q (M := Z["x" := fvar "z"]["y" := fvar "z"]) (closedunderapp_derive2 U_le_fvar_or_combinator _ hz) ⟨beta_eta_spline_contain_x g, closedunderapp_multiapp_cons (by grind) (by grind), closedunderapp_multiapp_cons (by grind) (.app (.app (closedunderapp_derive2 U_le_fvar_or_combinator _ (by assumption)) (by grind)) (by grind))⟩ _ h2steps
      apply FullBetaEta.steps_fv at hw
      apply (app_U_transform "x") at hz
      have hq := closedUnderApp_q_of_foldl_app "y" (by grind) (by grind [app_U_fv (by assumption)]) hq
      cases hq with | base hq =>
      rcases hq with _|hq|_ <;> try grind
      have g : ClosedUnderApp (U (n+1) "x" "z") (Z["x" := fvar "z"]["y" := fvar "z"].app (fvar "x")) := by grind
      obtain ⟨l, g, hl⟩ := closedUnderApp_reduce_to_head_apps "x" "z" (n+1) (by grind) g (by grind) hq
      have g := FullBeta.redex_app_l_cong g (LC.fvar "y")
      obtain ⟨Z, hz1, hz2⟩ := confluent_beta_eta steps (Relation.ReflTransGen.mono le_sup_left _ _ g)
      have := Relation.Normal.reflTransGen_eq (by rw [exists_beta_normal_fvar_app_of_beta_eta, exists_beta_normal_fvar_app_of_beta_eta]; apply normal_H) hz1
      subst Z
      apply ih n (by grind) (.app (.base ?_) (by grind)) hz2
      right
      right
      grind

theorem no_reduction_to_Hn_with_depth_bound_nf (fs)
  (hl : ∀ t ∈ fs, t.abs_two_vars_are_enough) : not_basises_nf fs := by
  refine ⟨H ((((fs.map depth).max?).getD 0) + 1), H.LC, H_fv, normal_H, ?_⟩
  intros M hm steps
  generalize hi : ((fs.map depth).max?).getD 0 = n
  rw [hi] at steps
  have steps := FullBetaEta.steps_app_l_cong (FullBetaEta.steps_app_l_cong steps (LC.fvar "x")) (LC.fvar "y")
  have steps := steps.trans (Relation.ReflTransGen.mono le_sup_left _ _ H_succ_reduce)
  obtain ⟨l, i, N, h, hn⟩ := exists_head_reduction_to_fvar_app (.app (.app (closedunderapp_derive (fun t h => by grind [hl _ h]) _ hm) (by grind)) (by grind)) (by rw [exists_beta_normal_fvar_app_of_beta_eta]; apply normal_H) steps
  have : ClosedUnderApp fvar_or_combinator M := closedunderapp_derive (fun t h => by grind [hl _ h]) _ hm
  have g := steps_multiApp_l_union (Ns := List.replicate i (fvar "y")) steps (by grind)
  have heq : (List.foldl app ((fvar "x").app ((fvar "y").app (H n))) (List.replicate i (fvar "y"))) = (List.foldl app (fvar "x") ( ((fvar "y").app (H n)) :: List.replicate i (fvar "y"))) := by grind
  unfold multiApp at g
  rw [heq] at g
  obtain ⟨_, hq, _⟩ := steps_closedUnderApp_unroll_q (M := M) (by grind) ⟨beta_eta_spline_contain_x g, closedunderapp_multiapp_cons (by grind) (by grind), closedunderapp_multiapp_cons (by grind) (.app (.app (by grind) (by grind)) (by grind))⟩ _ h
  apply FullBetaEta.steps_fv at hn
  have hq := closedUnderApp_q_of_foldl_app "y" (by grind) (by grind [closedunderapp_fv (by grind) hm]) hq
  cases hq with | base hq =>
  rcases hq with _|hq|_ <;> try grind
  obtain ⟨l, beta_steps, _⟩ := unroll_2_vars_are_enough_foldl (by grind) hq
  obtain ⟨Z, hz1, hz2⟩ := confluent_beta_eta steps (Relation.ReflTransGen.mono le_sup_left _ _ (FullBeta.redex_app_l_cong  beta_steps (LC.fvar "y")))
  have h_betaeta_nf : Relation.Normal FullBetaEta ((fvar "x").app ((fvar "y").app (H n))) := by
    rw [exists_beta_normal_fvar_app_of_beta_eta, exists_beta_normal_fvar_app_of_beta_eta]
    apply normal_H
  have := Relation.Normal.reflTransGen_eq h_betaeta_nf hz1
  subst Z
  apply no_reduction_to_Hn_with_depth_bound_U (.app (.base ?_) (by grind)) hz2
  right
  right
  refine ⟨_, rfl, ?_⟩
  apply genfinset_depth at hm
  rw [hi] at *
  grind

theorem no_reduction_to_Hn_with_depth_bound (fs)
  (hl : ∀ t ∈ fs, t.abs_two_vars_are_enough) : not_basises fs :=
  not_basises_of_nf (no_reduction_to_Hn_with_depth_bound_nf fs hl)

theorem no_reduction_to_Hn_with_depth_bound_closedunderapp_nf (fs)
  (hl : ∀ t ∈ fs, ClosedUnderAppBool abs_two_vars_are_enough t) : not_basises_nf fs := by
  obtain ⟨M, hlc, hfv, hnf, h⟩ := no_reduction_to_Hn_with_depth_bound_nf (fs.flatMap subterms) (by grind [subterms_closedunderappbool])
  refine ⟨M, hlc, hfv, hnf, ?_⟩
  intros t g steps
  apply h t ?_ steps
  clear steps h hlc hfv hnf
  induction g with
  | app _ _ _ _ => grind
  | base g => specialize hl _ g
              apply closedUnderAppBool_genfinset_subterms at hl
              apply genfinset_subset ?_ hl
              grind

theorem no_reduction_to_Hn_with_depth_bound_closedunderapp (fs)
  (hl : ∀ t ∈ fs, ClosedUnderAppBool abs_two_vars_are_enough t) : not_basises fs :=
  not_basises_of_nf (no_reduction_to_Hn_with_depth_bound_closedunderapp_nf fs hl)

theorem isNamedOfXY_not_basises_nf (fs)
  (hl : ∀ t ∈ fs, isNamedOfXY t) : not_basises_nf fs := by
  have h : ∃ l : List _, List.Forall₂ (Relation.ReflTransGen FullBeta) l fs /\
                         ∀ t ∈ l, ClosedUnderAppBool abs_two_vars_are_enough t := by
    induction fs with
    | nil => exact ⟨[], by simp, by grind⟩
    | cons head tail ih =>
        obtain ⟨l, _, _⟩ := ih (by grind)
        obtain ⟨s, _, _⟩ := exists_block_combination_betaStar head (by grind)
        refine ⟨s :: l, .cons (by assumption) (by assumption), by grind⟩
  obtain ⟨l, hl, _⟩ := h
  obtain ⟨y, hlc, hfv, hnf, h⟩ := no_reduction_to_Hn_with_depth_bound_closedunderapp_nf l (by grind)
  refine ⟨y, hlc, hfv, hnf, ?_⟩
  intros t ht steps
  obtain ⟨M, h1, h2⟩ := genfinset_forall2 hl (by grind) _ ht
  exact h M h1 (.trans (Relation.ReflTransGen.mono le_sup_left _ _ h2) steps)

theorem isNamedOfXY_not_basises (fs)
  (hl : ∀ t ∈ fs, isNamedOfXY t) : not_basises fs :=
  not_basises_of_nf (isNamedOfXY_not_basises_nf fs hl)

theorem isNamedOfXY_not_basis_nf {t} (ht : isNamedOfXY t) : not_basises_nf [t] := by
  apply isNamedOfXY_not_basises_nf
  grind

theorem isNamedOfXY_not_basis {t} (ht : isNamedOfXY t) : not_basis t := by
  apply isNamedOfXY_not_basises
  grind

theorem namableXY_not_basis {t} (ht : namableXY t) : not_basis t := by
  apply isNamedOfXY_not_basis
  rw [<- isNamedOfXY_eq_namableXY] at ht
  grind
