
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
import FokkerChallenge.TwoVarsAreNotEnough.Unroll
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Union

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

@[scoped grind]
def Q (mx a: Term String) : Prop := a = (fvar "y") \/
                                    unroll mx a \/
                                    (a.abs_two_vars_are_enough /\ a.depth < mx.depth)

theorem Q_lc {M}
  (hm : ClosedUnderApp fvar_or_combinator M):
  ∀ t, Q M t ->  t.LC := by
  intros x hx
  rcases hx with _|hx|hx
  . grind
  . apply unroll.LC hx
    apply (closedunderapp_lc (by grind) hm)
  . grind

theorem Q_lc_closed {M}
  (hm : ClosedUnderApp fvar_or_combinator M):
  ∀ t, ClosedUnderApp (Q M) t ->  t.LC := by
  intros x hx
  induction hx with grind [Q_lc]

theorem closed_under_app_Q {M t N1 N0}
  (g : two_vars_are_enough t)
  (ht :t.depth < M.depth)
  (h0: ClosedUnderApp (Q M) N0)
  (h1: ClosedUnderApp (Q M) N1)
  (hlc: N1.LC) :
  ClosedUnderApp (Q M) (t⟦1 ↝ N1⟧⟦0 ↝ N0⟧) := by
  induction h : t.fokker_size using Nat.strong_induction_on generalizing t with | h n ih => cases t with
  | fvar => grind
  | bvar a => have h : a = 0 \/ a = 1 := by grind
              cases h <;> subst_vars
              . grind
              . simp [openRec]
                rw [open_lc] <;> grind
  | app _ _ =>
    refine .app ?_ ?_ <;> apply ih
    any_goals rfl
    any_goals grind
    all_goals simp_all
  | abs t => cases t with
    | abs _ => grind
    | bvar _ => unfold two_vars_are_enough at g
                grind
    | fvar _ => unfold two_vars_are_enough at g
                grind
    | app _ _ =>  unfold two_vars_are_enough at g
                  grind

/-
theorem closedUnderApp_unroll {M}
  (h_contain_x : contain_x ((M.app (fvar "x")).app (fvar "y")))
  (hm : ClosedUnderApp fvar_or_combinator M):
  ∀ N, (M.app (fvar "x")).app (fvar "y") ↠𝒽 N ->
       ClosedUnderApp (Q (M.app (fvar "x"))) N := by
  intros N g
  induction g with
  | refl => refine .app (.base ?_) (by grind)
            right
            left
            refine .refl
  | tail h1 h2 ih =>
    obtain ⟨l, f, h3, h4, h5⟩ := closedunderapp_multiapp ih
    rcases h4 with h4|h4|⟨h4, h6⟩
    . subst_vars
      exfalso
      apply head_fvar h2
    . subst_vars
      rcases foldl_multiapp_cases h2 with ⟨f', h2, _⟩|⟨a, b, l', f', _, _, h2⟩|⟨a, b, l', f', _, _, h2⟩
      . subst_vars
        refine closedunderapp_multiapp_cons (by grind) (.base ?_)
        right
        left
        exact .tail h4 (.reflTrans (by grind))
      . subst_vars
        apply closedunderapp_multiapp_cons (by grind)
        cases unroll_fvar_or_combinator (by grind) h4 with
        | base h => grind
        | app h _ => cases h with | base h => cases h with
        | inl h => cases h
        | inr h =>  simp at h5
                    obtain ⟨h5, _⟩ := h5
                    unfold abs_two_vars_are_enough at h
                    split at h <;> try grind
                    rename_i heq
                    cases heq
                    have h7 : (M.app (fvar "x")).Q a := by
                      right
                      left
                      refine .tail h4 (.throughAbsApp)
                    apply closed_under_app_Q h
                    . have := unroll.depth (by grind) h4
                      simp_all
                      grind
                    . grind
                    . grind
                    . apply Q_lc (by grind) _ h7
      . exfalso
        subst_vars
        cases unroll_fvar_or_combinator (by grind) h4 with | base h3 => cases h3 with
        | inl => grind
        | inr =>  obtain ⟨l, h, _⟩ := unroll_2_vars_are_enough_foldl (by grind) h4
                  have h := FullBeta.redex_app_l_cong h (LC.fvar "y")
                  have h1 := h_contain_x _ h
                  unfold fv at h1
                  rw [flip_app_fv] at h1
                  have h5 : ∀ x ∈ l, x.fv = ∅ := by grind
                  rw [<- List.map_eq_replicate_iff] at h5
                  rw [h5] at h1
                  have h5 : f'.abs.abs.fv = ∅ := by grind
                  rw [h5, foldl_union_replicate_empty] at h1
                  simp [fv] at h1
    . unfold abs_two_vars_are_enough at h4
      split at h4 <;> try grind
      subst_vars
      rcases foldl_multiapp_cases h2 with ⟨f', h2, _⟩|⟨a, b, l', f', _, h2, _⟩|⟨a, b, l', f', _, h3, h2⟩
      . cases h2
      . cases h2
      . cases h3
        subst_vars
        apply closedunderapp_multiapp_cons (by grind)
        apply closed_under_app_Q (by assumption) (by grind) (by grind) (by grind)
        exact closedunderapp_lc (Q_lc (by grind)) (h5 a (by grind))
-/

theorem no_x_exists_q {M N}
  (hm : ClosedUnderApp fvar_or_combinator M)
  (steps : unroll M N)
  (hx : "x" ∉ N.fv) :
  ∀ N, ClosedUnderApp (Q M) N -> ∃ N', N ↠βᶠ N' /\ "x" ∉ N'.fv := by
  intros N hN
  induction hN with
  | base hN =>  rcases hN with _|hN|_
                . subst_vars
                  refine ⟨fvar "y", by grind⟩
                . cases unroll_iff (by grind) steps hN with
                | inl h =>  refine ⟨_, .refl, ?_⟩
                            apply unroll.fv at h
                            grind
                | inr h =>
    obtain ⟨l, h, _⟩:= unroll_2_vars_are_enough_foldl (unroll_fvar_or_combinator hm hN) h
    refine ⟨_, h, ?_⟩
    rw [flip_app_fv]
    have h5 : ∀ x ∈ l, x.fv = ∅ := by grind
    rw [<- List.map_eq_replicate_iff] at h5
    rw [h5, foldl_union_replicate_empty]
    grind
                . refine ⟨_, .refl, by grind⟩
  | app h5 h6 iha ihb =>  obtain ⟨c, h1, h2⟩ := iha
                          obtain ⟨d, h3, h4⟩ := ihb
                          refine ⟨c.app d, .trans (FullBeta.redex_app_l_cong h1 ?_) (FullBeta.redex_app_r_cong h3 ?_), by grind⟩
                          . apply Q_lc_closed hm _ h6
                          . have := Q_lc_closed hm _ h5
                            cases FullBeta.steps_lc_or_rfl h1 with grind

theorem step_closedUnderApp_unroll_q {M N}
  (hm : ClosedUnderApp fvar_or_combinator M)
  (h : contain_x N /\ ClosedUnderApp (Q (M.app (fvar "x"))) N /\ ClosedUnderApp fvar_or_combinator N):
  ∀ N', N ⭢𝒽 N' ->
  contain_x N' /\ ClosedUnderApp (Q (M.app (fvar "x"))) N' /\ ClosedUnderApp fvar_or_combinator N' := by
    intros N' step
    obtain ⟨h_contain_x, ih, _⟩ := h
    refine ⟨?_, ?_, HeadReduction2_preserver_fvar_or_combinator (by assumption) step⟩
    . intros _ steps
      apply h_contain_x _ (.trans (FullBetaEta.from_beta _ _ (HeadReduction2.step_2_beta step (Q_lc_closed (by grind) _ ih))) steps)
    . obtain ⟨l, f, h3, h4, h5⟩ := closedunderapp_multiapp ih
      rcases h4 with h4|h4|⟨h4, h6⟩
      . subst_vars
        exfalso
        apply head_fvar step
      . subst_vars
        rcases foldl_multiapp_cases step with ⟨f', h2, _⟩|⟨a, b, l', f', _, _, h2⟩|⟨a, b, l', f', _, _, h2⟩
        . subst_vars
          refine closedunderapp_multiapp_cons (by grind) (.base ?_)
          right
          left
          exact .tail h4 (.reflTrans (by grind))
        . subst_vars
          apply closedunderapp_multiapp_cons (by grind)
          cases unroll_fvar_or_combinator (by grind) h4 with
          | base h => cases h <;> grind
          | app h _ => cases h with | base h => cases h with
            | inl h => cases h
            | inr h =>  simp at h5
                        obtain ⟨h5, _⟩ := h5
                        unfold abs_two_vars_are_enough at h
                        split at h <;> try grind
                        rename_i heq
                        cases heq
                        have h7 : (M.app (fvar "x")).Q a := by
                          right
                          left
                          refine .tail h4 .throughAbsApp
                        apply closed_under_app_Q h
                        . have := unroll.depth (by grind) h4
                          simp_all
                          grind
                        . grind
                        . grind
                        . apply Q_lc (by grind) _ h7
        . exfalso
          subst f
          cases unroll_fvar_or_combinator (by grind) h4 with | base h3 => cases h3 with
          | inl => grind
          | inr =>  have hl := listfullBeta_exists (fun t => "x" ∉ t.fv) l ?_ ?_
                    . obtain ⟨Ns, hl, _⟩ := hl
                      specialize h_contain_x (Ns.foldl app f'.abs.abs) (FullBetaEta.from_beta _ _ (steps_multiApp_r hl (by grind)))
                      have hf : f'.abs.abs.fv = ∅ := by grind
                      rw [multiapp_fv, hf] at h_contain_x
                      generalize heq : (∅ : Finset String) = fs
                      rw [heq] at h_contain_x
                      have : "x" ∉ fs := by grind
                      clear heq hl
                      induction Ns generalizing fs <;> grind
                    . intros t ht
                      specialize h5 t ht
                      apply Q_lc_closed (by grind) _ h5
                    . intros t ht
                      apply no_x_exists_q (by grind) h4 (by grind) _ (by grind)
      . unfold abs_two_vars_are_enough at h4
        split at h4 <;> try grind
        subst_vars
        rcases foldl_multiapp_cases step with ⟨f', h2, _⟩|⟨a, b, l', f', _, h2, _⟩|⟨a, b, l', f', _, h3, h2⟩
        . cases h2
        . cases h2
        . cases h3
          subst_vars
          apply closedunderapp_multiapp_cons (by grind)
          apply closed_under_app_Q (by assumption) (by grind) (by grind) (by grind)
          exact closedunderapp_lc (Q_lc (by grind)) (h5 a (by grind))

theorem steps_closedUnderApp_unroll_q {M N}
  (hm : ClosedUnderApp fvar_or_combinator M)
  (h : contain_x N /\ ClosedUnderApp (Q (M.app (fvar "x"))) N /\ ClosedUnderApp fvar_or_combinator N):
  ∀ N', N ↠𝒽 N' ->
  contain_x N' /\ ClosedUnderApp (Q (M.app (fvar "x"))) N' /\ ClosedUnderApp fvar_or_combinator N' := by
  intros N hN
  induction hN with
  | refl => grind
  | tail _ _ _ => grind [step_closedUnderApp_unroll_q]


theorem closedUnderApp_unroll {M}
  (h_contain_x : contain_x ((M.app (fvar "x")).app (fvar "y")))
  (hm : ClosedUnderApp fvar_or_combinator M):
  ∀ N, (M.app (fvar "x")).app (fvar "y") ↠𝒽 N ->
       ClosedUnderApp (Q (M.app (fvar "x"))) N := by
  have := @steps_closedUnderApp_unroll_q _ (((M.app (fvar "x")).app (fvar "y"))) hm ⟨h_contain_x, (.app (.base ?_) (by grind)) , by grind⟩
  . grind
  . right
    left
    exact .refl

theorem closedUnderApp_q_of_foldl_app (y) {M N a l}
  (h1 : y ∈ a.fv)
  (h2 : y ∉ M.fv)
  (h : ClosedUnderApp (Q M) (List.foldl app N (a :: l))) :
  ClosedUnderApp (Q M) N := by
  induction l using List.reverseRecOn with
  | nil =>  simp_all
            cases h with
            | app _ _ => grind
            | base h => rcases h with _|h|_
                        . grind
                        . apply unroll.fv at h
                          simp at h
                          exfalso
                          apply h2
                          apply h
                          simp
                          right
                          grind
                        . grind
  | append_singleton l a _ =>
      rw [<- List.cons_append, List.foldl_concat] at h
      cases h with
      | app _ _ => grind
      | base h => rcases h with _|h|_
                  . grind
                  . apply unroll.fv at h
                    simp at h
                    exfalso
                    apply h2
                    apply h
                    simp
                    left
                    rw [multiapp_fv]
                    apply union_foldl
                    grind
                  . grind

/-
theorem closedUnderApp_app_y_iterate {i} {M N : Term String} :
  ClosedUnderApp M.Q N ->
  ClosedUnderApp M.Q ((fun a => a.app (fvar "y"))^[i] N) := by
  induction i generalizing N with
  | zero => simp
  | succ n _ => rw [add_comm, Function.iterate_add]
                simp
                grind
-/
