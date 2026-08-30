import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.EtaPostpone
import FokkerChallenge.EnhancedCslib.HeadRed
import FokkerChallenge.EnhancedCslib.InternalPar
import FokkerChallenge.EnhancedCslib.StarSeq

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-!
# The Head Normalization Theorem

The **head normalization theorem** (Barendregt, *The Lambda Calculus*,
Corollary 11.4.8; Takahashi, *Parallel reductions in λ-calculus*, Corollary
2.7): if a term has a head normal form, then its *head reduction* reaches a head
normal form — in particular the head reduction terminates.

The proof follows Takahashi: every parallel β-reduction factors as a head
reduction followed by an *internal* parallel reduction (`parBeta_head_internal`,
the Main Lemma of `RequestProject.StarSeq`), and internal parallel reduction
reflects head normal forms (`IPar.headNF_back`).

Main results:

* `head_normalization`   — `M ↠β N`, `N` a head normal form ⟹ `M ⟶h* P` with
  `P` a head normal form;
* `hasHNF_iff_headStepStar_headNF` — `M` has a head normal form iff head
  reduction from `M` reaches one;
* `HeadStep.deterministic` — head reduction is deterministic;
* `head_normalization_theorem` — for locally closed `M`: `M` has a head normal
  form iff head reduction from `M` terminates;
* `no_infinite_head_reduction` — a term with a head normal form admits no
  infinite head reduction sequence.
-/


universe u

open Term

variable {Var : Type u}

/-- `M` *has a head normal form* if some β-reduct of `M` is a head normal form. -/
def HasHNF (M : Term Var) : Prop := ∃ N, M ↠βᶠ N ∧ HeadNF N

/-- A terminating head reduction admits no infinite head reduction sequence. -/
theorem HeadSn.no_seq {M : Term Var} (h : Relation.SN HeadStep M) :
    ∀ (f : ℕ → Term Var), f 0 = M → (∀ n, HeadStep (f n) (f (n + 1))) → False := by
  induction h with
  | intro A _ ih =>
      intro f hf0 hf
      refine ih (f 1) (by rw [← hf0]; exact hf 0) (fun n => f (n + 1)) rfl ?_
      intro n
      exact hf (n + 1)

variable  [HasFresh Var] [DecidableEq Var]

theorem ParBeta.abs_close (x : Var) {A B : Term Var} (h : Parallel A B) :
    Parallel (Term.abs (closeRec 0 x A)) (Term.abs (closeRec 0 x B)) :=
  Parallel.abs ({x} ∪ fv A ∪ fv B) (by grind)

/-- If `P` reduces internally to `M₁` and `M₁` makes a head step, then `P` makes
a head step to a term that parallel-reduces to the result. -/
theorem IPar.headStep_lift {P M₁ M₂ : Term Var} (h : IPar P M₁) (hs : HeadStep M₁ M₂) :
    ∃ Q, HeadStep P Q ∧ Parallel Q M₂ := by
  induction h generalizing M₂ with
  | fvar x => cases hs
  | @app A A' B B' hA hAA' hB ih =>
      cases hs with
      | @beta A₀ B₀ _ _ => exact absurd (by grind) (hAA'.not_isAbs hA)
      | @app _ A'' _ _ hstep _ =>
          obtain ⟨Q, hQ, hQ'⟩ := ih hstep
          exact ⟨Term.app Q B, HeadStep.app hA hQ (para_lc_l hB), Parallel.app hQ' hB⟩
  | @appAbs xs M M' N N' hbody hN =>
      cases hs with
      | @beta A₀ B₀ _ _ =>
          refine ⟨M ^ N, HeadStep.beta ?_ (para_lc_l hN), ?_⟩
          · exact Term.LC.abs xs M fun x hx => (para_lc_l (hbody x hx))
          · exact para_open_out xs hbody hN
      | @app _ _ _ hnabs _ _ => exact absurd (by grind) hnabs
  | @abs xs M M' hbody ih =>
      cases hs with
      | @abs ys A₀ A' hstep =>
          have ⟨x, hx⟩ := fresh_exists <| free_union [fv] Var
          obtain ⟨Q₀, hQ₀, hQ₀'⟩ := ih x (by grind) (hstep x (by grind))
          refine ⟨Term.abs (closeRec 0 x Q₀), ?_, ?_⟩
          · have h2 := HeadStep.abs_close x hQ₀
            rw [<- open_close_var] at h2
            grind
            grind
          · have h2 := ParBeta.abs_close x hQ₀'
            rw [<- open_close] at h2
            grind
            grind

/-- A head step after a parallel β-step can be pulled back to a head reduction. -/
theorem parBeta_headStep_lift {M M₁ M₂ : Term Var} (h : Parallel M M₁)
    (hs : HeadStep M₁ M₂) : ∃ Q, HeadStepStar M Q ∧ Parallel Q M₂ := by
  obtain ⟨P, hP, hiP⟩ := parBeta_head_internal h
  obtain ⟨Q, hQ, hQ'⟩ := hiP.headStep_lift hs
  exact ⟨Q, hP.tail hQ, hQ'⟩

/-- If `M` parallel-reduces to a term whose head reduction reaches a head normal
form, then so does the head reduction of `M`. -/
theorem headStepStar_headNF_lift {M₁ P : Term Var} (hstar : HeadStepStar M₁ P)
    (hnf : HeadNF P) : ∀ {M : Term Var}, Parallel M M₁ →
      ∃ Q, HeadStepStar M Q ∧ HeadNF Q := by
  induction hstar using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro M h
      obtain ⟨R, hR, hiR⟩ := parBeta_head_internal h
      exact ⟨R, hR, hiR.headNF_back hnf⟩
  | head hstep _ ih =>
      intro M h
      obtain ⟨Q, hQ, hQ'⟩ := parBeta_headStep_lift h hstep
      obtain ⟨R, hR, hnfR⟩ := ih hQ'
      exact ⟨R, hQ.trans hR, hnfR⟩

/-- **Head normalization theorem** (reachability form).  If some β-reduct of `M`
is a head normal form, then the head reduction of `M` reaches a head normal
form. -/
theorem head_normalization {M N : Term Var} (hstar : M ↠βᶠ N)
    (hnf : HeadNF N) : ∃ P, HeadStepStar M P ∧ HeadNF P := by
  induction hstar using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨N, Relation.ReflTransGen.refl, hnf⟩
  | head hstep _ ih =>
      obtain ⟨P, hP, hnfP⟩ := ih
      exact headStepStar_headNF_lift hP hnfP (FullBeta.le_parallel _ _ hstep)

/-- A term has a head normal form iff its head reduction reaches one. -/
theorem hasHNF_iff_headStepStar_headNF {M : Term Var} :
    HasHNF M ↔ ∃ P, HeadStepStar M P ∧ HeadNF P := by
  constructor
  · rintro ⟨N, hstar, hnf⟩
    exact head_normalization hstar hnf
  · rintro ⟨P, hstar, hnf⟩
    exact ⟨P, hstar.toFullBetaStar, hnf⟩

/-! ### Determinism and termination of head reduction -/

theorem headTerminating_of_headNF {M : Term Var} (h : HeadNF M) : Relation.SN HeadStep M :=
  Acc.intro _ fun _ hy => absurd hy (by grind [HeadNF.no_headStep h])

theorem headTerminating_of_headStepStar_headNF {M P : Term Var}
    (hstar : HeadStepStar M P) (hnf : HeadNF P) : Relation.SN HeadStep M := by
  induction hstar using Relation.ReflTransGen.head_induction_on with
  | refl => exact headTerminating_of_headNF hnf
  | head hstep _ ih =>
      refine Acc.intro _ fun y hy => ?_
      rwa [HeadStep.deterministic hy hstep]

theorem exists_headNF_of_headTerminating {M : Term Var} (h : Relation.SN HeadStep M) :
    LC M → ∃ P, HeadStepStar M P ∧ HeadNF P := by
  induction h with
  | intro A _ ih =>
      intro hA
      by_cases hnf : HeadNF A
      · exact ⟨A, Relation.ReflTransGen.refl, hnf⟩
      · obtain ⟨N, hN⟩ := exists_headStep_of_not_headNF hA hnf
        obtain ⟨P, hP, hnfP⟩ := ih N hN (HeadStep.regular hN).2
        exact ⟨P, Relation.ReflTransGen.head hN hP, hnfP⟩

/-- **The Head Normalization Theorem.**  A locally closed term has a head normal
form if and only if its head reduction terminates. -/
theorem head_normalization_theorem {M : Term Var} (hM : LC M) :
    HasHNF M ↔ Relation.SN HeadStep M := by
  constructor
  · intro h
    obtain ⟨P, hP, hnfP⟩ := hasHNF_iff_headStepStar_headNF.mp h
    exact headTerminating_of_headStepStar_headNF hP hnfP
  · intro h
    obtain ⟨P, hP, hnfP⟩ := exists_headNF_of_headTerminating h hM
    exact ⟨P, hP.toFullBetaStar, hnfP⟩

/-- A term with a head normal form admits no infinite head reduction sequence. -/
theorem no_infinite_head_reduction {M : Term Var} (h : HasHNF M)
    (f : ℕ → Term Var) (hf0 : f 0 = M) (hf : ∀ n, HeadStep (f n) (f (n + 1))) :
    False := by
  obtain ⟨P, hP, hnfP⟩ := hasHNF_iff_headStepStar_headNF.mp h
  exact  HeadSn.no_seq (headTerminating_of_headStepStar_headNF hP hnfP) f hf0 hf

/-- A generic divergence criterion: if `P` is a set of terms from each of which head
reduction reaches, in at least one step, another element of `P`, then no term that head
reduces to an element of `P` has a head normal form. -/
theorem not_hasHNF_of_reaches {P : Term String → Prop}
    (hP : ∀ M, P M → ∃ N, Relation.TransGen HeadStep M N ∧ P N)
    {M N : Term String} (h : HeadStepStar M N) (hN : P N) : ¬ HasHNF M := by
  have key : ∀ {A : Term String}, Relation.SN HeadStep A →
      ∀ B, HeadStepStar A B → ¬ P B := by
    intro A hacc
    induction hacc with
    | intro A _ ih =>
        intro B hAB hB
        obtain ⟨B', hstep, hB'⟩ := hP B hB
        obtain ⟨y, hy, hy'⟩ :=
          Relation.TransGen.head'_iff.mp (Relation.TransGen.trans_right hAB hstep)
        exact ih y hy B' hy' hB'
  intro hHNF
  obtain ⟨Q, hQ, hnfQ⟩ := hasHNF_iff_headStepStar_headNF.mp hHNF
  exact key (headTerminating_of_headStepStar_headNF hQ hnfQ) N h hN

theorem headStepStar_to_normal {M N P : Term String} (h1 : HeadStepStar M N) :
    HeadStepStar M P → Relation.Normal HeadStep P → HeadStepStar N P := by
  induction h1 using Relation.ReflTransGen.head_induction_on with
  | refl => intro h _; exact h
  | head hstep _ ih =>
      intro h2 hn
      rcases Relation.ReflTransGen.cases_head h2 with rfl | ⟨y, hy, hy2⟩
      · exact absurd ⟨_, hstep⟩ hn
      · exact ih (by rwa [HeadStep.deterministic hstep hy]) hn

theorem hasHNF_of_headStepStar {M N : Term String} (h : HeadStepStar M N) (hM : HasHNF M) :
    HasHNF N := by
  obtain ⟨P, hP, hnfP⟩ := hasHNF_iff_headStepStar_headNF.mp hM
  exact ⟨P, (headStepStar_to_normal h hP hnfP.no_headStep).toFullBetaStar, hnfP⟩

/-- A term with a βη-normal form has a head normal form. -/
theorem hasHNF_of_normalizable {M : Term String} (hM : LC M)
    (h : Relation.Normalizable FullBetaEta M) : HasHNF M := by
  obtain ⟨W, hW, hnW⟩ := (hasBetaEtaNF_iff_hasBetaNF M).mpr h
  have hlcW : LC W := by
    rcases FullBeta.steps_lc_or_rfl hW with ⟨_, h⟩ | rfl
    exacts [h, hM]
  exact ⟨W, hW, (headNF_iff_no_headStep hlcW).mpr (BetaNF.no_headStep hnW)⟩

theorem not_hasHNF_of_headStepStar {M N : Term String} (h : HeadStepStar M N)
    (hN : ¬ HasHNF N) : ¬ HasHNF M := fun hM => hN (hasHNF_of_headStepStar h hM)
