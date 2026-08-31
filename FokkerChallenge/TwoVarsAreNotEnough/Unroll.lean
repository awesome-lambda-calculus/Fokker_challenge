
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.ListFullBeta
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
import FokkerChallenge.TwoVarsAreNotEnough.Head2

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

@[scoped grind]
inductive unroll_step : Term String → Term String → Prop
  | reflTrans {M N: Term String} : HeadReduction2 M N -> unroll_step M N
  | throughAbsApp {N1 N2: Term String} : unroll_step (N1.abs.app N2) N2

theorem unroll_inner_eq {M N Z : Term String}
  (m_lc : M.LC)
  (hx : unroll_step M N)
  (hy : unroll_step M Z):
  N = Z := by
  cases hx <;> cases hy <;> rename_i h
  . rename_i g
    have := HeadReduction2.unique m_lc h g
    grind
  . cases h with | appL h => cases h
  . cases h with | appL h => cases h
  . grind

theorem unroll_step.fv {M N  : Term String}
  (h : unroll_step M N):
  N.fv ⊆ M.fv := by
  cases h with grind [HeadReduction2.fv]

abbrev unroll : Term String → Term String → Prop := Relation.ReflTransGen unroll_step

theorem unroll.fv {M N  : Term String}
  (h : unroll M N):
  N.fv ⊆ M.fv := by
  induction h with
  | refl => grind
  | tail _ h _ => grind [unroll_step.fv h]

theorem unroll.LC {M N : Term String}
  (hmn : unroll M N) (m_lc: M.LC) : N.LC := by
  induction hmn with
  | refl => grind
  | tail _ h ih => cases h with
  | reflTrans h => apply HeadReduction2.step_lc_r h ih
  | throughAbsApp => cases ih with grind

theorem unroll_fvar_or_combinator {M N : Term String}
  (hm : ClosedUnderApp fvar_or_combinator M)
  (hmn : unroll M N):
  ClosedUnderApp fvar_or_combinator N := by
  induction hmn with
  | refl => grind
  | tail _ h g => cases h with
  | reflTrans h => apply steps_HeadReduction2_fvar_or_combinator g (.single h)
  | throughAbsApp => cases g with grind

theorem unroll.depth {M N : Term String}
  (hm : ClosedUnderApp fvar_or_combinator M)
  (h : unroll M N) :
  N.depth <= M.depth := by
  induction h with
  | refl => grind
  | tail h hbc _ =>
    have hb := unroll_fvar_or_combinator (by grind) h
    cases hbc with
    | reflTrans hbc => grind [HeadReduction2.step_depth hb hbc]
    | throughAbsApp => simp_all

theorem unroll_2_vars_are_enough_foldl {M N : Term String}
  (hm : ClosedUnderApp fvar_or_combinator M)
  (hmn : unroll M N):
  ∃ l: List (Term String), M ↠βᶠ l.foldl (flip app) N /\ ∀ x ∈ l, x.abs_two_vars_are_enough /\ x.depth <= M.depth := by
  induction hmn with
  | refl => exists []
            grind
  | tail g h ih => cases h with
    | reflTrans h =>
    have h := HeadReduction2.step_2_beta h (unroll.LC g (closedunderapp_lc (by grind) hm))
    obtain ⟨l, ih, g⟩ := ih
    exact ⟨l, .trans ih (steps_flip_app_l h (by grind)), g⟩
    | throughAbsApp =>
    rename_i N
    obtain ⟨l, ih, h2⟩ := ih
    refine ⟨N.abs :: l, ih, ?_⟩
    intros x hx
    cases hx with
    | tail => apply h2 _ (by tauto)
    | head as =>
      have h := unroll.depth hm g
      simp at h
      constructor
      . cases unroll_fvar_or_combinator hm g with
      | base g => cases g <;> grind
      | app g _ => cases g with | base g => cases g <;> grind
      . simp
        omega

theorem unroll_iff {M N Z : Term String}
  (m_lc : M.LC)
  (hx : unroll M N)
  (hy : unroll M Z):
  unroll N Z \/ unroll Z N := by
  induction hx with
  | refl => grind
  | tail _ h ih => cases ih with
  | inr hzb =>  right
                exact .tail hzb h
  | inl hbz =>  rcases Relation.ReflTransGen.cases_head hbz with h|⟨_, g, h2⟩
                . subst_vars
                  right
                  refine .single h
                . have := unroll_inner_eq ?_ h g
                  subst_vars
                  left
                  exact h2
                  apply unroll.LC (by assumption) m_lc

/-
theorem unroll_fvar {M : Term String} {x y}
  (m_lc : M.LC)
  (hx : unroll M (fvar x))
  (hy : unroll M (fvar y)): x = y := by
  cases unroll_iff m_lc hx hy with
  | inr h =>  rcases Relation.ReflTransGen.cases_head h with _|⟨_, g, _⟩
              . grind
              . cases g with | reflTrans g => cases g
  | inl h =>  rcases Relation.ReflTransGen.cases_head h with _|⟨_, g, _⟩
              . grind
              . cases g with | reflTrans g => cases g
-/
