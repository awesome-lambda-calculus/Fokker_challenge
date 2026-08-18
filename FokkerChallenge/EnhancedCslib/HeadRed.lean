import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LeftmostReduction
import Cslib.Foundations.Data.HasFresh
import FokkerChallenge.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-!
# Head reduction and head normal forms

This file introduces, for the locally nameless untyped λ-calculus:

* `HeadStep`    — one step of *head* reduction, i.e. contraction of the head
  redex of `λx₁ … xₙ. (λy. P) Q R₁ … Rₖ`;
* `HeadNeutral` — terms of the form `x R₁ … Rₖ`;
* `HeadNF`      — head normal forms `λx₁ … xₙ. x R₁ … Rₖ`.

and proves the basic metatheory: regularity, that head reduction is a
β-reduction, substitutivity, congruence under binders (via closing), and the
characterisation of head normal forms as the terms with no head redex.
-/


universe u


open Term

variable {Var : Type u}



/-- One step of **head reduction**: contract the head redex of
`λx₁ … xₙ. (λy. P) Q R₁ … Rₖ`. -/
inductive HeadStep : Term Var → Term Var → Prop
  /-- Contract a redex in head position. -/
  | beta {M N : Term Var} : LC (abs M) → LC N → HeadStep (app (abs M) N) (M ^ N)
  /-- The head redex of `M N` is the head redex of `M`, provided `M` is not an
  abstraction (otherwise `M N` is itself the head redex). -/
  | app {M M' N : Term Var} :
      ¬ M.IsAbs → HeadStep M M' → LC N → HeadStep (app M N) (app M' N)
  /-- The head redex of `λx. M` is the head redex of `M`. -/
  | abs (xs : Finset Var) {M M' : Term Var} :
      (∀ x ∉ xs, HeadStep (M ^ fvar x) (M' ^ fvar x)) → HeadStep (abs M) (abs M')

/-- Reflexive-transitive closure of head reduction. -/
abbrev HeadStepStar : Term Var → Term Var → Prop := Relation.ReflTransGen HeadStep

/-- Terms of the shape `x R₁ … Rₖ` (a free variable applied to arguments). -/
@[scoped grind]
inductive HeadNeutral : Term Var → Prop
  /-- A free variable is neutral. -/
  | fvar (x : Var) : HeadNeutral (fvar x)
  /-- A neutral term applied to a locally closed argument is neutral. -/
  | app {M N : Term Var} : HeadNeutral M → LC N → HeadNeutral (app M N)

/-- **Head normal forms**: terms of the shape `λx₁ … xₙ. y R₁ … Rₖ`. -/
inductive HeadNF : Term Var → Prop
  /-- A neutral term is a head normal form. -/
  | neutral {M : Term Var} : HeadNeutral M → HeadNF M
  /-- An abstraction whose body is a head normal form is a head normal form. -/
  | abs (xs : Finset Var) {M : Term Var} :
      (∀ x ∉ xs, HeadNF (M ^ fvar x)) → HeadNF (abs M)

/-! ### Basic properties -/

theorem HeadNeutral.lc {M : Term Var} (h : HeadNeutral M) : LC M := by
  induction h with
  | fvar x => exact LC.fvar x
  | app _ hN ih => exact LC.app ih hN

theorem HeadNeutral.not_isAbs {M : Term Var} (h : HeadNeutral M) : ¬ M.IsAbs := by
  cases h <;> grind

theorem HeadNeutral.subst [DecidableEq Var] [HasFresh Var] {M : Term Var} {x y: Var}
    (h : HeadNeutral M) :
    HeadNeutral (M[x := (Term.fvar y) ]) := by
    induction h with
    | fvar x => rw [subst_fvar]
                split <;> grind
    | app _ _ _ =>  rw [subst_app]
                    exact .app (by grind) (subst_lc (by grind) (by grind))

theorem HeadNF.lc {M : Term Var} (h : HeadNF M) : LC M := by
  induction h with
  | neutral hn => exact hn.lc
  | abs xs _ ih => exact LC.abs xs _ ih

theorem HeadNF.of_not_isAbs {M : Term Var} (h : HeadNF M) (hM : ¬ M.IsAbs) :
    HeadNeutral M := by
  cases h with
  | neutral hn => exact hn
  | abs => grind

theorem HeadNF.subst [DecidableEq Var] [HasFresh Var] {M : Term Var} (x y: Var)
    (h : HeadNF M) :
    HeadNF M[x:=(Term.fvar y)] := by
    induction h with
    | neutral h =>  exact .neutral (HeadNeutral.subst h)
    | abs xs h ih =>
      rename_i M
      refine .abs (xs ∪ {x} ∪ {y}) ?_
      grind

theorem HeadStep.preserve_isabs {M N : Term Var} (h : HeadStep M N) :
    M.IsAbs -> N.IsAbs := by
    cases h with grind

theorem HeadSteps.preserve_isabs {M N : Term Var} (steps : Relation.ReflTransGen HeadStep M N) :
    M.IsAbs -> N.IsAbs := by
    induction steps with grind [HeadStep.preserve_isabs]

/-- A term admitting a head step is either an abstraction or an application. -/
theorem HeadStep.shape {M N : Term Var} (h : HeadStep M N) :
    M.IsAbs ∨ ∃ A B, M = Term.app A B := by
  cases h with
  | beta => exact Or.inr ⟨_, _, rfl⟩
  | app => exact Or.inr ⟨_, _, rfl⟩
  | abs => grind

theorem HeadStep.toLeftMost {M N : Term Var} (h : HeadStep M N) : Leftmost M N := by
  induction h with
  | beta hM hN => exact .outer (by grind) (by grind)
  | app _ _ hN ih => exact BetaAt.appNoAbsL (by grind) (by grind)
  | abs xs _ ih => exact .abs xs ih

/-- A head step is in particular a β-step. -/
theorem HeadStep.toFullBeta {M N : Term Var} (h : HeadStep M N) : FullBeta M N := by
  induction h with
  | beta hM hN => exact Xi.base (Beta.beta hM hN)
  | app _ _ hN ih => exact Xi.appR hN ih
  | abs xs _ ih => exact Xi.abs xs ih

theorem HeadStepStar.toFullBetaStar {M N : Term Var} (h : HeadStepStar M N) :
    M ↠βᶠ N := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail hstep.toFullBeta

theorem HeadNeutral.no_headStep {M : Term Var} (hM : HeadNeutral M) : Relation.Normal HeadStep M := by
  induction hM with (intros g; obtain ⟨N, g⟩ := g)
  | fvar x => cases g
  | app h _ ih => cases g with
    | beta _ _ => cases h
    | app _ _ _ => grind

/-- A β-normal form has no head redex, since every head step is a β-step. -/
theorem BetaNF.no_headStep {M : Term Var} (h : Relation.Normal FullBeta M) :
                                               Relation.Normal HeadStep M  := by
  rintro ⟨N, hN⟩
  apply h ⟨N, hN.toFullBeta⟩

theorem multiapp_headneutral {l : List (Term Var)} {x} (h_lc : ∀ t ∈ l, t.LC) :
  (List.foldl app (fvar x) l).HeadNeutral := by
  induction l using List.reverseRecOn with
  | nil => simp; grind
  | append_singleton l a ih => simp; grind

lemma step_beta_normal_preserve_multiapp {x M} {l: List (Term Var)}
  (h_normal : Relation.Normal HeadStep M)
  (step : M ⭢βᶠ l.foldl app (fvar x))  :
  ∃ l': List _, M = l'.foldl app (fvar x) := by
   induction l using List.reverseRecOn generalizing M with
   | nil => simp at step
            cases step with | base step =>
            generalize heq : (fvar x) = N
            rw [heq] at step
            cases step
            exfalso
            apply h_normal ⟨_, .beta (by grind) (by grind)⟩
   | append_singleton l a ih =>
    simp at step
    cases step with
    | base step =>  generalize heq : ((List.foldl app (fvar x) l).app a) = N
                    rw [heq] at step
                    cases step
                    exfalso
                    apply h_normal ⟨_, .beta (by grind) (by grind)⟩
    | appL h1 h2 => rename_i M
                    use (l++[M])
                    grind
    | appR h1 step => rename_i M
                      specialize ih ?_ step
                      . rintro ⟨N, h⟩
                        apply h_normal
                        refine ⟨N.app a, ?_⟩
                        by_cases hm : M.IsAbs
                        . cases hm
                          generalize heq : ((List.foldl app (fvar x) l)) = N
                          rw [heq] at step
                          cases step with
                          | base step => cases step
                          | abs xs _ => cases l using List.reverseRecOn <;> grind
                        . exact .app hm h h1
                      . obtain ⟨l, ih⟩ := ih
                        subst M
                        use l ++ [a]
                        grind


variable [HasFresh Var]

theorem HeadStep.regular {M N : Term Var} (h : HeadStep M N) : LC M ∧ LC N := by
  induction h with
  | beta hM hN => refine ⟨LC.app hM hN, ?_⟩
                  rw [<- lcAt_iff_LC] at *
                  rw [lcAt_openRec_iff_lcAt _ _ _ hN]
                  grind
  | app _ _ hN ih => exact ⟨LC.app ih.1 hN, LC.app ih.2 hN⟩
  | abs xs _ ih => exact ⟨LC.abs xs _ fun x hx => (ih x hx).1, LC.abs xs _ fun x hx => (ih x hx).2⟩

variable [DecidableEq Var]

/-- Head reduction is substitutive. -/
theorem HeadStep.subst {M N : Term Var} (h : HeadStep M N) (x : Var) {u : Term Var}
    (hu : LC u) : HeadStep M[x:=u] N[x:=u] := by
  induction h with
  | @beta M N hM hN =>
      have hsub : (M ^ N)[x:=u] = M[x:=u] ^ N[x:=u] := by grind
      rw [hsub]
      exact HeadStep.beta (subst_lc hM hu) (subst_lc hN hu)
  | @app A A' B hA hstep hB ih =>
      obtain ⟨A₁, A₂, rfl⟩ : ∃ A₁ A₂, A = Term.app A₁ A₂ := by
        rcases HeadStep.shape hstep with h | h
        · exact absurd h hA
        · exact h
      exact HeadStep.app (by grind) ih (subst_lc hB hu)
  | @abs xs A A' _ ih =>
      refine HeadStep.abs (xs ∪ {x}) ?_
      intro y hy
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
      grind

/-- Head reduction lifts under a binder, via closing. -/
theorem HeadStep.abs_close (x : Var) {A B : Term Var} (h : HeadStep A B) :
    HeadStep (Term.abs (A ^* x)) (Term.abs (B ^* x)) := by
  refine HeadStep.abs ({x} ∪ fv A ∪ fv B) ?_
  intro y _
  rw [close_open_to_subst, close_open_to_subst]
  exact HeadStep.subst h x (LC.fvar y)
  all_goals grind [HeadStep.regular h]


/-- Head reduction lifts under a binder from a single fresh witness. -/
theorem HeadStep.abs_fresh {M M' : Term Var} (x : Var) (hM : x ∉ M.fv) (hM' : x ∉ fv M')
    (h : HeadStep (M ^ fvar x) (M' ^ fvar x)) : HeadStep (Term.abs M) (Term.abs M') := by
  have h2 := HeadStep.abs_close x h
  rwa [<- open_close_var , <- open_close_var] at h2
  grind
  grind

/-! ### Head normal forms are exactly the terms without a head redex -/

theorem HeadNF.no_headStep {M : Term Var} (hM : HeadNF M) : Relation.Normal HeadStep M := by
  induction hM with
  | neutral h => apply HeadNeutral.no_headStep h
  | abs xs _ ih =>  rintro ⟨M, g⟩
                    cases g
                    have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
                    apply ih x (by grind) (by grind)

theorem exists_headStep_of_not_headNF {M : Term Var} (hM : LC M) (h : ¬ HeadNF M) :
    ∃ N, HeadStep M N := by
  induction hM with
  | fvar x => exact absurd (HeadNF.neutral (HeadNeutral.fvar x)) h
  | @abs xs A hbody ih =>
      have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
      specialize ih x (by grind) ?_
      . intros g
        apply h
        apply HeadNF.abs (∅ ∪ M.fv ∪ xs ∪ A.fv ∪ {x})
        intros y hy
        have := HeadNF.subst x y g
        grind
      . obtain ⟨N, hN⟩ := ih
        refine ⟨Term.abs (closeRec 0 x N), ?_⟩
        have h2 := HeadStep.abs_close x hN
        rwa [<- open_close_var] at h2
        grind
  | @app A B hA hB ihA _ =>
      by_cases hab : A.IsAbs
      · cases hab
        exact ⟨_, HeadStep.beta hA hB⟩
      · by_cases hnfA : HeadNF A
        · exact absurd (HeadNF.neutral (HeadNeutral.app (HeadNF.of_not_isAbs hnfA hab) hB)) h
        · obtain ⟨A', hA'⟩ := ihA hnfA
          exact ⟨Term.app A' B, HeadStep.app hab hA' hB⟩

/-- A locally closed term is a head normal form iff it has no head redex. -/
theorem headNF_iff_no_headStep {M : Term Var} (hM : LC M) :
    HeadNF M ↔ Relation.Normal HeadStep M := by
  constructor
  · rintro h ⟨N, hN⟩; exact h.no_headStep (by grind)
  · intro h
    by_contra hc
    exact h (exists_headStep_of_not_headNF hM hc)

/-- Head reduction is deterministic. -/
theorem HeadStep.deterministic {M N N' : Term Var} (h : HeadStep M N)
    (h' : HeadStep M N') : N = N' := by
  induction h generalizing N' with
  | @beta A B hA hB =>
      cases h' with
      | beta => rfl
      | @app _ _ _ hnabs _ _ => exact absurd (by grind) hnabs
  | @app A A' B hA hstep hB ih =>
      cases h' with
      | beta => exact absurd (by grind) hA
      | @app _ A'' _ _ hstep' _ => rw [ih hstep']
  | @abs xs A A' hbody ih =>
      cases h' with | @abs ys A₀ A'' hbody' =>
      have ⟨x, hx⟩ := fresh_exists <| free_union [fv] Var
      have hEq : A' ^ Term.fvar x = A'' ^ Term.fvar x := ih x (by grind) (hbody' x (by grind))
      have hclose : closeRec 0 x (A' ^ Term.fvar x) = closeRec 0 x (A'' ^ Term.fvar x) := by
        rw [hEq]
      rw [<- open_close, <- open_close] at hclose <;> grind

/-- A β-step out of a head neutral term `y R₁ … Rₖ` reduces one of the arguments,
so the reduct is again head neutral. -/
theorem HeadNeutral.of_fullBeta {M N : Term Var} (hM : HeadNeutral M)
    (step : M ⭢βᶠ N) : HeadNeutral N := by
  induction hM generalizing N with
  | fvar x =>
      cases step with
      | base h => cases h
  | @app A B hA hB ih =>
      cases step with
      | base h =>
          cases h with
          | beta _ _ => exact absurd (by grind) hA.not_isAbs
      | appL _ hstep => exact HeadNeutral.app hA (FullBeta.step_lc_r hstep)
      | appR _ hstep => exact HeadNeutral.app (ih hstep) hB

/-- **A β-step out of a head normal form yields a head normal form.** -/
theorem step_beta_preserve_headnf {M N : Term Var} (step : M ⭢βᶠ N)
    (hm : HeadNF M) : HeadNF N := by
  induction hm generalizing N with
  | neutral hn => exact HeadNF.neutral (hn.of_fullBeta step)
  | @abs xs A _ ih =>
      cases step with
      | base h => cases h
      | abs ys hstep =>
          refine HeadNF.abs (xs ∪ ys) fun x hx => ?_
          simp only [Finset.mem_union, not_or] at hx
          exact ih x hx.1 (hstep x hx.2)

/-- Head normal forms are preserved by arbitrarily many β-steps. -/
theorem HeadNF.of_fullBetaStar {M N : Term Var} (step : M ↠βᶠ N)
    (hm : HeadNF M) : HeadNF N := by
  induction step with
  | refl => exact hm
  | tail _ hstep ih => exact step_beta_preserve_headnf hstep ih

theorem steps_beta_preserve_normal_headstep {M N : Term Var}
  (steps : M ↠βᶠ N)
  (hm : Relation.Normal HeadStep M) :
        Relation.Normal HeadStep N := by
    cases FullBeta.steps_lc_or_rfl steps with
    | inr => grind
    | inl h =>  rw [<- headNF_iff_no_headStep]
                apply HeadNF.of_fullBetaStar steps
                rw [headNF_iff_no_headStep] <;> grind
                grind
