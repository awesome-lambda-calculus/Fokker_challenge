import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.EtaPostpone
import FokkerChallenge.EnhancedCslib.HeadSN

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-!
# β-normal forms that η-reduce to a variable-headed spine

This file analyses the shape of a β-normal form `M` which η-reduces to an
application spine `x N₁ … Nₖ` headed by a *free* variable `x`.

The requested statement was

```
lemma beta_normal_of_eta_to_fvar_apps {x M} {l : List (Term String)}
  (hM : Normal FullBeta M) (steps : M ↠ηᶠ l.foldl app (fvar x)) :
  ∃ l', M = l'.foldl app (fvar x) ∨ ∃ l', M = ((l'.foldl app (fvar x)).app (bvar 0)).abs
```

i.e. such an `M` is either itself a spine, or a *single* η-expansion
`λz. (x N₁ … Nₖ) z` of one.  **This is false**: η-expansions can be nested and
can also occur inside the arguments of the spine, and both phenomena survive
β-normality.  A machine-checked counterexample is
`LambdaLN.Counterexample.beta_normal_of_eta_to_fvar_apps_false`, using

  `M = λy. x (λz. y z)`     (locally nameless: `abs (app (fvar x) (abs (app (bvar 1) (bvar 0))))`)

which is β-normal and η-reduces to `x` (first contract the inner redex
`λz. y z ⟶η y` under the binder, giving `λy. x y`, then the outer redex), but is
neither a spine nor of the form `λz. (spine) z`.

The corrected statement is `LambdaLN.betaNF_etaStar_absN_spine`: `M` is a spine
headed by `x` under some number `n` of abstractions,
`M = λ…λ. x N₁ … Nₖ` (`absN n (spine x l')`).  For `n = 0` this is the first
disjunct above; the second disjunct above is the special case `n = 1`,
`l' = l`, `N_last = bvar 0`.
-/


universe u


open Term

variable {Var : Type u}

/-! ## Spines and iterated abstractions -/

/-- The application spine `x N₁ … Nₖ`, i.e. `l.foldl app (fvar x)`. -/
def spine (x : Var) (l : List (Term Var)) : Term Var := l.foldl app (fvar x)

@[simp] theorem spine_nil (x : Var) : spine x ([] : List (Term Var)) = fvar x := rfl

@[simp] theorem spine_concat (x : Var) (l : List (Term Var)) (b : Term Var) :
    spine x (l ++ [b]) = app (spine x l) b :=
  List.foldl_concat _ _ _ _

/-- A spine is either the head variable (empty argument list) or an application. -/
theorem spine_cases (x : Var) (l : List (Term Var)) :
    (l = [] ∧ spine x l = fvar x) ∨
      ∃ l₀ b, l = l₀ ++ [b] ∧ spine x l = app (spine x l₀) b := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l₀, b, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · refine Or.inr ⟨l₀, b, by simp, ?_⟩
    simp [spine, List.concat_eq_append]

/-- A spine is never an abstraction. -/
theorem spine_ne_abs {x : Var} {l : List (Term Var)} {C : Term Var} : spine x l ≠ abs C := by
  rcases spine_cases x l with ⟨_, h⟩ | ⟨l₀, b, _, h⟩ <;> rw [h] <;> exact fun h => by cases h

/-- A spine is never a bound variable. -/
theorem spine_ne_bvar {x : Var} {l : List (Term Var)} {i : ℕ} : spine x l ≠ bvar i := by
  rcases spine_cases x l with ⟨_, h⟩ | ⟨l₀, b, _, h⟩ <;> rw [h] <;> exact fun h => by cases h

/-- If a spine is a free variable, it is the head and the argument list is empty. -/
theorem spine_eq_fvar {x y : Var} {l : List (Term Var)} (h : spine x l = fvar y) :
    x = y ∧ l = [] := by
  rcases spine_cases x l with ⟨hl, h'⟩ | ⟨l₀, b, _, h'⟩
  · rw [h'] at h; exact ⟨by cases h; rfl, hl⟩
  · rw [h'] at h; cases h

/-- Inversion for a spine that is an application. -/
theorem spine_eq_app {x : Var} {l : List (Term Var)} {P Q : Term Var}
    (h : spine x l = app P Q) : ∃ l₀, l = l₀ ++ [Q] ∧ P = spine x l₀ := by
  rcases spine_cases x l with ⟨_, h'⟩ | ⟨l₀, b, hl, h'⟩
  · rw [h'] at h; cases h
  · rw [h'] at h
    cases h
    exact ⟨l₀, hl, rfl⟩

/-- The head variable and the argument list of a spine are uniquely determined. -/
theorem spine_inj {x y : Var} {l₁ l₂ : List (Term Var)}
    (h : spine x l₁ = spine y l₂) : x = y ∧ l₁ = l₂ := by
  induction l₁ using List.reverseRecOn generalizing l₂ with
  | nil =>
      rcases List.eq_nil_or_concat l₂ with rfl | ⟨l₀, b, rfl⟩
      · exact ⟨by cases h; rfl, rfl⟩
      · rw [List.concat_eq_append, spine_concat, spine_nil] at h; cases h
  | append_singleton l₀ a ih =>
      rcases List.eq_nil_or_concat l₂ with rfl | ⟨l₀', b, rfl⟩
      · rw [spine_concat, spine_nil] at h; cases h
      · rw [List.concat_eq_append, spine_concat, spine_concat] at h
        injection h with h₁ h₂
        obtain ⟨hxy, rfl⟩ := ih h₁
        subst h₂
        exact ⟨hxy, by simp⟩

/-- A head neutral term is a spine headed by a free variable. -/
theorem HeadNeutral.exists_spine {M : Term Var} (h : HeadNeutral M) :
    ∃ (x : Var) (l : List (Term Var)), M = spine x l := by
  induction h with
  | fvar x => exact ⟨x, [], rfl⟩
  | @app A B _ _ ih =>
      obtain ⟨x, l, rfl⟩ := ih
      exact ⟨x, l ++ [B], by rw [spine_concat]⟩

/-! ## Inversion lemmas for η-reduction -/

theorem fullEtaStar_fvar_inv {y : Var} {U : Term Var} (h : (fvar y) ↠ηᶠ  U) :
    U = fvar y := by
  rcases h.cases_head with h | ⟨c, hc, _⟩
  · exact h.symm
  · cases hc with | base hc => cases hc

theorem fullEta_app_inv {A B U : Term Var} (h : FullEta (app A B) U) :
    ∃ A' B', U = app A' B' ∧ A ↠ηᶠ A' ∧ B ↠ηᶠ  B' := by
  cases h with
  | base hb => cases hb
  | appL hZ hstep =>
      exact ⟨_, _, rfl, Relation.ReflTransGen.refl, Relation.ReflTransGen.single hstep⟩
  | appR hZ hstep =>
      exact ⟨_, _, rfl, Relation.ReflTransGen.single hstep, Relation.ReflTransGen.refl⟩

theorem fullEtaStar_app_inv {A B U : Term Var} (h : (app A B) ↠ηᶠ  U) :
    ∃ A' B', U = app A' B' ∧ A ↠ηᶠ A' ∧ B ↠ηᶠ  B' := by
  induction h with
  | refl => exact ⟨A, B, rfl, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
      obtain ⟨A', B', rfl, hA, hB⟩ := ih
      obtain ⟨A'', B'', rfl, hA', hB'⟩ := fullEta_app_inv hstep
      exact ⟨A'', B'', rfl, hA.trans hA', hB.trans hB'⟩

theorem fullEta_abs_inv {T U : Term Var} (h : FullEta (abs T) U) :
    (LC U ∧ T = app U (bvar 0)) ∨
      ∃ (T' : Term Var) (xs : Finset Var), U = abs T' ∧
        ∀ y ∉ xs, FullEta (T ^ fvar y) (T' ^ fvar y) := by
  cases h with
  | base hb => cases hb with
    | eta hM => exact Or.inl ⟨hM, rfl⟩
  | abs xs hs => exact Or.inr ⟨_, xs, rfl, hs⟩

theorem openRec_absN_spine {T : Term Var} {k n : ℕ} {x y : Var} {l : List (Term Var)}
    (hxy : x ≠ y) (h : openRec k (fvar y) T = abs^[n] (spine x l)) :
    ∃ l', T = abs^[n] (spine x l') := by
  induction T generalizing k n l with
  | bvar i =>
      cases n with
      | zero =>
          simp_all
          simp only [openRec] at h
          split_ifs at h
          · exact absurd (spine_eq_fvar h.symm).1 hxy
          · exact absurd h.symm spine_ne_bvar
      | succ m =>
          simp only [openRec] at h
          split_ifs at h <;> rw [add_comm, Function.iterate_add] at h <;> simp at h
  | fvar z =>
      cases n with
      | zero =>
          simp_all
          simp only [openRec] at h
          obtain ⟨hx, hl⟩ := spine_eq_fvar h.symm
          grind
      | succ m =>
          rw [add_comm, Function.iterate_add] at h
          simp at h
          cases h
  | abs S ih =>
      cases n with
      | zero =>
          simp only [openRec] at h
          exact absurd h.symm spine_ne_abs
      | succ m =>
          rw [add_comm, Function.iterate_add] at h
          simp at h
          simp only [openRec] at h
          obtain ⟨l', hS⟩ := ih (by injection h)
          rw [add_comm, Function.iterate_add]
          simp
          exact ⟨l', by grind⟩
  | app P Q ihP _ =>
      cases n with
      | zero =>
          simp only [openRec] at h
          obtain ⟨l₀, _, hP'⟩ := spine_eq_app h.symm
          obtain ⟨l₀', hP⟩ := ihP (n := 0) (l := l₀) (by exact hP')
          refine ⟨l₀' ++ [Q], ?_⟩
          rw [spine_concat]
          rw [hP]
          simp
      | succ m =>
          rw [add_comm, Function.iterate_add] at h
          simp at h
          cases h


variable [HasFresh Var] [DecidableEq Var]

/-- **Escaping an abstraction.**  If `abs T` η-reduces to a term `U` that is not
an abstraction, the reduction must contract a top-level η-redex: there is a
locally closed `W` with `W ↠η U` and, for all sufficiently fresh `y`,
`T ^ y ↠η W y`. -/
theorem abs_escape {T U : Term Var} (h : (abs T) ↠ηᶠ U)
    (hU : ∀ C, U ≠ abs C) :
    ∃ (W : Term Var) (ys : Finset Var), LC W ∧ W ↠ηᶠ U ∧
      ∀ y ∉ ys, (T ^ fvar y) ↠ηᶠ (app W (fvar y)) := by
  have key : ∀ {A : Term Var}, A ↠ηᶠ U → ∀ T : Term Var, A = abs T →
      ∃ (W : Term Var) (ys : Finset Var), LC W ∧ W ↠ηᶠ U ∧
        ∀ y ∉ ys, (T ^ fvar y) ↠ηᶠ (app W (fvar y)) := by
    intro A hA
    induction hA using Relation.ReflTransGen.head_induction_on with
    | refl => intro T hT; exact absurd hT (hU T)
    | head hstep hrest ih =>
        intro T hT
        subst hT
        rcases fullEta_abs_inv hstep with ⟨hlc, rfl⟩ | ⟨T', xs, rfl, hs⟩
        · refine ⟨_, ∅, hlc, hrest, ?_⟩
          intro y _
          grind
        · obtain ⟨W, ys, hW, hWU, hopen⟩ := ih T' rfl
          refine ⟨W, ys ∪ xs, hW, hWU, ?_⟩
          intro y hy
          simp only [Finset.mem_union, not_or] at hy
          exact .head (hs y hy.2) (hopen y hy.1)
  exact key h T rfl

/-! ## The main result -/

/-- A normal term that η-reduces to a spine headed by the free variable `x` is
itself a spine headed by `x`, under some number of abstractions. -/
theorem Normal.etaStar_absN_spine {M : Term Var} (h : Normal M) :
    ∀ (x : Var) (l : List (Term Var)), M ↠ηᶠ (spine x l) →
      ∃ n l', M = (Term.abs)^[n] (spine x l') := by
  induction h with
  | fvar z =>
      intro x l hred
      obtain ⟨hx, _⟩ := spine_eq_fvar (fullEtaStar_fvar_inv hred)
      subst_vars
      exact ⟨0, [], by simp⟩
  | @app A B _ hAnotabs _ ihA _ =>
      intro x l hred
      obtain ⟨A', B', hEq, hAred, _⟩ := fullEtaStar_app_inv hred
      obtain ⟨l₀, _, hA'⟩ := spine_eq_app hEq
      subst hA'
      obtain ⟨n, l', hAeq⟩ := ihA x l₀ hAred
      cases n with
      | zero =>
          simp_all
          refine ⟨0, l' ++ [B], by simp⟩
      | succ m => exfalso
                  apply hAnotabs
                  rw [add_comm, Function.iterate_add] at hAeq
                  simp at hAeq
                  grind
  | @abs xs T _ ih =>
      intro x l hred
      obtain ⟨W, ys, _, hWred, hopen⟩ := abs_escape hred (fun _ => spine_ne_abs)
      have ⟨y, hy⟩ := fresh_exists <| free_union [fv] Var
      have h1 : (T ^ Term.fvar y) ↠ηᶠ (Term.app W (Term.fvar y)) := hopen y (by grind)
      have h2 : (Term.app W (Term.fvar y)) ↠ηᶠ (spine x (l ++ [Term.fvar y])) := by
        rw [spine_concat]
        exact FullEta.redex_app_l_cong hWred (LC.fvar y)
      obtain ⟨n, l', hEq⟩ := ih y (by grind) x (l ++ [Term.fvar y]) (h1.trans h2)
      obtain ⟨l'', hT⟩ := openRec_absN_spine (Ne.symm (by grind)) hEq
      exact ⟨n + 1, l'', by rw [add_comm, Function.iterate_add]; simp; grind⟩

/-- **Corrected form of the requested lemma.**  If `M` is a β-normal form which
η-reduces to a spine `x N₁ … Nₖ` headed by a free variable, then `M` is a spine
headed by the same free variable, placed under some number `n` of abstractions:
`M = λ…λ. x N'₁ … N'ⱼ`.

(The requested statement claimed `n ≤ 1` with a last argument `bvar 0`, which is
false; see `Counterexample.beta_normal_of_eta_to_fvar_apps_false`.) -/
theorem betaNF_etaStar_absN_spine (M : Term Var) (x : Var) (l : List (Term Var))
    (hM : Relation.Normal FullBeta M) (steps : M ↠ηᶠ (l.foldl app (fvar x))) :
    ∃ (n : ℕ) (l' : List (Term Var)), M = abs^[n] (l'.foldl app (fvar x)) := by
  have steps' : M ↠ηᶠ (spine x l) := steps
  rcases steps'.cases_head with h | ⟨c, hc, _⟩
  · exact ⟨0, l, h⟩
  · exact (betaNF_normal (FullEta.step_lc_l hc) hM).etaStar_absN_spine x l steps'


/-
useless theorem
/-- If, in addition, `M` is not an abstraction, then `M` is literally a spine
headed by `x`. -/
theorem betaNF_etaStar_spine_of_not_abs {M : Term Var} {x : Var} {l : List (Term Var)}
    (hM : BetaNF M) (hnotabs : ∀ C, M ≠ abs C)
    (steps : M ↠ηᶠ (l.foldl app (fvar x))) :
    ∃ l' : List (Term Var), M = l'.foldl app (fvar x) := by
  obtain ⟨n, l', hEq⟩ := betaNF_etaStar_absN_spine hM steps
  cases n with
  | zero => exact ⟨l', hEq⟩
  | succ m => exact absurd hEq (hnotabs _)
-/
