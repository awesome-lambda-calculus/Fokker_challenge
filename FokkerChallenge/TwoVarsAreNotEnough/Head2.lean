import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.MultiApp
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LeftmostReduction
import Cslib.Foundations.Data.HasFresh
import FokkerChallenge.Basic
import FokkerChallenge.FamousCombinator
import FokkerChallenge.EnhancedCslib.Basic
import FokkerChallenge.EnhancedCslib.FlipApp
import FokkerChallenge.EnhancedCslib.LeftMost
import FokkerChallenge.EnhancedCslib.BetaNormalForm
import FokkerChallenge.EnhancedCslib.Closedunderapp
import FokkerChallenge.EnhancedCslib.List
import FokkerChallenge.EnhancedCslib.ReflTransGenWithSteps
import FokkerChallenge.EnhancedCslib.HeadRed
import FokkerChallenge.TwoVarsAreNotEnough.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term


@[reduction_sys "𝒽"]
inductive HeadReduction2 : Term String → Term String → Prop
  | base {M N1 N2: Term String} : HeadReduction2 ((M.abs.abs.app N1).app N2) (M⟦1 ↝ N1⟧⟦0 ↝ N2⟧)
  | appL {N M1 M2: Term String} : HeadReduction2 M1 M2 -> HeadReduction2 (M1.app N) (M2.app N)

theorem HeadReduction2.fv {M N : Term String} (h : HeadReduction2 M N) : N.fv ⊆ M.fv := by
  induction h with grind [open_preserve_not_fvar]

theorem HeadReduction2.step_2_leftmost {M N : Term String} (h : HeadReduction2 M N)
  (m_lc : M.LC) : ∃ Z, M ⭢ℓ Z /\ Z ⭢ℓ N /\ ¬ Z.IsAbs:= by
  induction h with
  | base => cases m_lc with | app m_lc _ => cases m_lc with | app _ n_lc =>
            refine ⟨_, BetaAt.appNoAbsL (.outer (by grind) (by grind)) (by grind), .outer ?_ (by grind), by grind⟩
            rw [<- lcAt_iff_LC] at *
            unfold LcAt
            rw [lcAt_openRec_iff_lcAt]
            grind
            apply lcAt_le _ _ _ (by omega) n_lc
  | appL h ih =>  cases m_lc with | app m_lc _ =>
                  obtain ⟨Z, h1, h2, h3⟩ := ih (by grind)
                  rename_i N M _ _
                  refine ⟨Z.app N, BetaAt.appNoAbsL h1 ?_, BetaAt.appNoAbsL h2 h3, by grind⟩
                  induction h with grind

theorem HeadReduction2.step_2_beta {M N : Term String} (h : HeadReduction2 M N) (m_lc : M.LC) : M ↠βᶠ N := by
  obtain ⟨_, h1, h2, _⟩:= HeadReduction2.step_2_leftmost h m_lc
  have h3 := BetaAt.to_step h1 m_lc
  have h4 := BetaAt.to_step h2 (FullBeta.step_lc_r h3)
  exact .head h3 (.single h4)

theorem HeadReduction2.steps_2_beta {M N : Term String} (h : Relation.ReflTransGen HeadReduction2 M N) (m_lc : M.LC) : M ↠βᶠ N := by
  induction h with
  | refl => grind
  | tail _ h ih =>
      apply HeadReduction2.step_2_beta at h
      cases FullBeta.steps_lc_or_rfl ih with
      | inl h => exact .trans ih (by grind)
      | inr h => grind

theorem HeadReduction2.unique {M N Z : Term String}
  (m_lc : M.LC)
  (h1 : HeadReduction2 M N)
  (h2 : HeadReduction2 M Z): N = Z := by
  have := HeadReduction2.step_2_leftmost h1 m_lc
  have := HeadReduction2.step_2_leftmost h2 m_lc
  grind [BetaAt.unique]

theorem HeadReduction2.step_lc_r {M N : Term String}
  (h : HeadReduction2 M N)
  (m_lc : M.LC) : N.LC := by
  grind [HeadReduction2.steps_2_beta, FullBeta.steps_lc_or_rfl]

theorem head_multiapp (f a b: Term String) (l) :
  (a :: b :: l).foldl Term.app f.abs.abs ⭢𝒽 l.foldl Term.app (f⟦1 ↝ a⟧⟦0 ↝ b⟧) := by
  induction l using List.reverseRecOn generalizing f a with simp
  | nil => refine .base
  | append_singleton l a _ => refine .appL (by grind)

theorem head_fvar {l : List (Term String)} {M : Term String} {x : String} :
  l.foldl Term.app (fvar x) ⭢𝒽 M -> False := by
  induction h : l.length using Nat.strong_induction_on generalizing M l with | h n ih =>
  intros g
  cases (List.eq_nil_or_concat' l) with
  | inl h =>  subst_vars
              cases g
  | inr h =>  obtain ⟨l, b, h⟩ := h
              subst_vars
              rw [List.foldl_concat] at g
              cases (List.eq_nil_or_concat' l) with
              | inl h =>  subst_vars
                          simp at g
                          cases g
                          rename_i g
                          cases g
              | inr h =>  obtain ⟨l, a, h⟩ := h
                          subst_vars
                          rw [List.foldl_concat] at g
                          generalize heq : l.foldl Term.app (fvar x) = Y
                          rw [heq] at g
                          cases g with
                          | base => cases (List.eq_nil_or_concat' l) with subst_vars
                            | inl h =>  simp at heq
                            | inr h =>  obtain ⟨l, b, h⟩ := h
                                        subst_vars
                                        rw [List.foldl_concat] at heq
                                        cases heq
                          | appL g => cases g with
                            | base => cases (List.eq_nil_or_concat' l) with subst_vars
                              | inl h =>  simp at heq
                              | inr h =>  obtain ⟨l, b, h⟩ := h
                                          subst_vars
                                          rw [List.foldl_concat] at heq
                                          generalize heq2 : l.foldl Term.app (fvar x) = Z
                                          rw [heq2] at heq
                                          cases heq
                                          cases (List.eq_nil_or_concat' l) with subst_vars
                                          | inl h =>  simp at heq2
                                          | inr h =>  obtain ⟨l, b, h⟩ := h
                                                      subst_vars
                                                      rw [List.foldl_concat] at heq2
                                                      cases heq2
                            | appL g => rw [<- heq] at g
                                        apply ih _ _ rfl g
                                        simp

theorem foldl_multiapp_cases {f M : Term String} {l : List (Term String)}
  (g : HeadReduction2 (l.foldl app f) M):
  (∃ f', HeadReduction2 f f' /\ M = l.foldl app f') \/
  (∃ a b l' f', l = b :: l'      /\ f = f'.abs.abs.app a /\ M = l'.foldl app (f'⟦1 ↝ a⟧⟦0 ↝ b⟧)) \/
  (∃ a b l' f', l = a :: b :: l' /\ f = f'.abs.abs       /\ M = l'.foldl app (f'⟦1 ↝ a⟧⟦0 ↝ b⟧))
  := by
  induction h : l.length using Nat.strong_induction_on generalizing M l f with | h n ih =>
  cases l with
  | nil => grind
  | cons head l =>
      simp at g
      cases l with simp at g
      | nil => cases g <;> grind
      | cons head tail =>
        specialize ih _ ?_ g rfl
        . simp at h
          omega
        . rcases ih with ⟨f, ih, _⟩|ih|ih
          . cases ih with
          | base => grind
          | appL ih => cases ih <;> grind
          . grind
          . grind

theorem HeadReduction2_preserver_fvar_or_combinator {M N : Term String}
  (hm : ClosedUnderApp fvar_or_combinator M)
  (hmn : HeadReduction2 M N):
  ClosedUnderApp fvar_or_combinator N := by
  induction hmn with
  | appL _ _ => grind
  | base => cases hm with
  | base _ => grind
  | app hm _ => cases hm with
  | base _ => grind
  | app hm _ => cases hm with
  | base hm => cases hm with
  | inl h => grind
  | inr h =>  unfold abs_two_vars_are_enough at h
              split at h <;> try grind
              rename_i heq
              cases heq
              apply two_vars_are_enough_openRec <;> assumption

theorem steps_HeadReduction2_fvar_or_combinator {M N : Term String}
  (hm : ClosedUnderApp fvar_or_combinator M)
  (steps : Relation.ReflTransGen HeadReduction2 M N):
  ClosedUnderApp fvar_or_combinator N := by
  induction steps with
  | refl => grind
  | tail _ _ _ => grind [HeadReduction2_preserver_fvar_or_combinator]

theorem HeadReduction2.step_depth {M N : Term String}
  (hm : ClosedUnderApp fvar_or_combinator M)
  (h : HeadReduction2 M N) :
  N.depth <= M.depth := by
  induction h with
  | base =>
    cases hm with
    | base _ => grind
    | app hm _ => cases hm with
    | base _ => grind
    | app hm _ => cases hm with | base hm => cases hm with
    | inl h => grind
    | inr h =>  unfold abs_two_vars_are_enough at h
                split at h <;> try grind
                rename_i heq
                cases heq
                rename_i N1 N2 _ _ _
                have := @two_vars_are_enough_depth _ N1 N2 h (by grind) (by grind)
                simp_all
                grind
  | appL _ ih =>
    cases hm with
    | base _ => grind
    | app _ _ =>
    specialize ih (by assumption)
    simp_all
    grind

theorem HeadReduction2.steps_depth {M N : Term String}
  (hm : ClosedUnderApp fvar_or_combinator M)
  (h : Relation.ReflTransGen HeadReduction2 M N) :
  N.depth <= M.depth := by
  induction h with
  | refl => grind
  | tail steps h => grind [HeadReduction2.step_depth (steps_HeadReduction2_fvar_or_combinator hm steps) h]

theorem HeadReduction2.is_headstep {M M' M'': Term String}
  (hm : ClosedUnderApp fvar_or_combinator M)
  (h: ¬ M'.IsAbs)
  (h1 : HeadStep M M')
  (h2 : HeadStep M' M''):
  HeadReduction2 M M'' := by
  induction h1 generalizing M'' with
  | abs xs _ => cases h2 with | abs xs _ => grind
  | beta _ _ => cases hm with
    | base hm => grind
    | app hm _ => cases hm with | base hm => cases hm with
      | inl hm => cases hm
      | inr hm =>
      unfold abs_two_vars_are_enough at hm
      split at hm <;> grind
  | app h5 h4 h3 ih => cases h2 with
    | app =>  refine .appL ?_
              apply ih <;> grind
    | beta h1 h2 =>
      rename_i M
      generalize heq : M.abs = N
      rw [heq] at h4
      cases h4 with
      | app => grind
      | abs => grind
      | beta _ _ => cases hm with
        | base => grind
        | app hm _ => cases hm with
          | base _ => grind
          | app hm _ => cases hm with | base hm => cases hm with
            | inl => grind
            | inr hm =>
      unfold abs_two_vars_are_enough at hm
      split at hm <;> try grind
      rename_i heq
      cases heq
      cases heq
      exact .base

theorem HeadReduction2.headneutral_exists {M N: Term String}
  (hm : ClosedUnderApp fvar_or_combinator M)
  (hn : N.HeadNeutral)
  (h : Relation.ReflTransGen HeadStep M N) :
  Relation.ReflTransGen HeadReduction2 M N := by
  induction h using Relation.ReflTransGen.head_induction_on₂ with
  | refl => grind
  | single h' =>
    exfalso
    induction h' with
    | abs xs _ => grind
    | app _ _ _ => grind
    | beta _ _ => cases hm with
      | base _ => grind
      | app hm _ => cases hm with | base hm => cases hm with
        | inl => grind
        | inr hm => unfold abs_two_vars_are_enough at hm
                    split at hm <;> grind
  | head₂ h₁ h₂ h ih =>
  have g := HeadReduction2.is_headstep hm ?_ h₁ h₂
  refine .head g (ih (HeadReduction2_preserver_fvar_or_combinator hm g))
  intros _
  apply HeadNeutral.not_isAbs hn
  apply HeadSteps.preserve_isabs h
  cases h₂ with grind
