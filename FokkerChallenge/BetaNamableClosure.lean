import FokkerChallenge.BetaCheck
import FokkerChallenge.EnhancedCslib.GenFinset

/-!
# The class of β-reducts of two-name-nameable terms

`BetaReductOfNamable T` says that `T` is a β-reduct of a term that can be named
with only the two variable names `x` and `y`.

This file proves the two structural facts that make the class useful for the
"one-point basis" question:

* `namableXY_app` / `BetaReductOfNamable.app`: nameability, and hence the class,
  is closed under application;
* `not_betaConv_of_betaReductOfNamable`: if `A` belongs to the class, then no
  applicative combination of `A` is β-convertible to a term that is not
  β-convertible to any nameable term.

Consequently, if some closed term is not β-convertible to any two-name term
(Statman, *Two variables are not enough*), then no term of the class can be a
one-point basis.
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term


/-! ## Closed terms carry no naming constraints -/

theorem constraints_mem_lt : ∀ (t : Term String) (d : ℕ) (L : List (ℕ × Bool)),
    constraints t d = some L → ∀ p ∈ L, p.1 + 1 < d := by
  intro t
  induction t with
  | bvar i =>
      intro d L h p hp
      simp only [constraints] at h
      split at h
      · rename_i hlt
        simp only [Option.some.injEq] at h
        subst h
        rcases mem_bvarConstr (m := p.1) (b := p.2) (by simpa using hp) with ⟨_, he⟩ | ⟨_, he⟩ <;>
          omega
      · simp at h
  | fvar x => intro d L h; simp [constraints] at h
  | abs t ih =>
      intro d L h p hp
      simp only [constraints, Option.map_eq_some_iff] at h
      obtain ⟨L', hL', rfl⟩ := h
      have : (p.1 + 1, p.2) ∈ L' := mem_shiftConstr.1 (by simpa using hp)
      have := ih (d + 1) L' hL' _ this
      simpa using by omega
  | app a b iha ihb =>
      intro d L h p hp
      simp only [constraints] at h
      split at h
      · rename_i L₁ L₂ h₁ h₂
        split at h
        · simp only [Option.some.injEq] at h
          subst h
          rcases List.mem_append.1 hp with hp | hp
          · exact iha d L₁ h₁ p hp
          · exact ihb d L₂ h₂ p hp
        · simp at h
      · simp at h

/-- A term that is nameable with two names carries no constraint at the top
level. -/
theorem constraints_zero_nil {t : Term String} {L : List (ℕ × Bool)}
    (h : constraints t 0 = some L) : L = [] := by
  match L with
  | [] => rfl
  | p :: r => exact absurd (constraints_mem_lt t 0 _ h p (by simp)) (by omega)

/-- Nameability with two names is closed under application. -/
theorem namableXY_app {a b : Term String} (ha : namableXY a = true) (hb : namableXY b = true) :
    namableXY (app a b) = true := by
  simp only [namableXY, Option.isSome_iff_exists] at ha hb ⊢
  obtain ⟨L₁, h₁⟩ := ha
  obtain ⟨L₂, h₂⟩ := hb
  have e₁ := constraints_zero_nil h₁
  have e₂ := constraints_zero_nil h₂
  subst e₁; subst e₂
  exact ⟨[], by simp [constraints, h₁, h₂, compatible]⟩

/-! ## Nameable terms are locally closed -/

theorem lcAt_of_constraints : ∀ (t : Term String) (d : ℕ) (L : List (ℕ × Bool)),
    constraints t d = some L → LcAt d t = true := by
  intro t
  induction t with
  | bvar i =>
      intro d L h
      simp only [constraints] at h
      split at h
      · simpa [LcAt] using by assumption
      · simp at h
  | fvar x => intro d L h; simp [constraints] at h
  | abs t ih =>
      intro d L h
      simp only [constraints, Option.map_eq_some_iff] at h
      obtain ⟨L', hL', _⟩ := h
      simpa [LcAt] using ih (d + 1) L' hL'
  | app a b iha ihb =>
      intro d L h
      simp only [constraints] at h
      split at h
      · rename_i L₁ L₂ h₁ h₂
        simp only [LcAt, Bool.and_eq_true]
        exact ⟨iha d L₁ h₁, ihb d L₂ h₂⟩
      · simp at h

theorem lc_of_namableXY {t : Term String} (h : namableXY t = true) : LC t := by
  simp only [namableXY, Option.isSome_iff_exists] at h
  obtain ⟨L, hL⟩ := h
  rw [<- lcAt_iff_LC]
  grind [lcAt_of_constraints t 0 L hL]

/-! ## The class is closed under application -/

theorem BetaReductOfNamable.lc {T : Term String} (h : BetaReductOfNamable T) : LC T := by
  obtain ⟨S, hS, hred⟩ := h
  cases FullBeta.steps_lc_or_rfl hred <;> grind [lc_of_namableXY hS]

theorem BetaReductOfNamable.app {A B : Term String}
    (hA : BetaReductOfNamable A) (hB : BetaReductOfNamable B) :
    BetaReductOfNamable (Term.app A B) := by
  obtain ⟨SA, hSA, hA'⟩ := hA
  obtain ⟨SB, hSB, hB'⟩ := hB
  refine ⟨Term.app SA SB, namableXY_app hSA hSB, ?_⟩
  have hLCA : LC A := by cases FullBeta.steps_lc_or_rfl hA' <;> grind [lc_of_namableXY hSA]
  have step₁ : (Term.app SA SB) ↠βᶠ (Term.app A SB) := FullBeta.redex_app_l_cong hA' (lc_of_namableXY hSB)
  have step₂ : (Term.app A SB) ↠βᶠ (Term.app A B) := FullBeta.redex_app_r_cong hB' hLCA
  exact step₁.trans step₂

/-- Every applicative combination of terms of the class stays in the class. -/
theorem BetaReductOfNamable.closedUnderApp {t : Term String}
    (h : ClosedUnderApp BetaReductOfNamable t) : BetaReductOfNamable t := by
  induction h with
  | base hb => exact hb
  | app _ _ iha ihb => exact iha.app ihb

/-! ## Consequence for one-point bases -/

/-- β-conversion. -/
abbrev BetaConv : Term String → Term String → Prop := Relation.EqvGen FullBeta

theorem betaConv_of_betaStar {M N : Term String} (h : M ↠βᶠ N) : BetaConv M N := by
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | tail _ hstep ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hstep)

/-- Every term of the class is β-convertible to a term nameable with two names. -/
theorem exists_namableXY_betaConv {T : Term String} (h : BetaReductOfNamable T) :
    ∃ S, namableXY S = true ∧ BetaConv S T := by
  obtain ⟨S, hS, hred⟩ := h
  exact ⟨S, hS, betaConv_of_betaStar hred⟩

/-- **The criterion.**  Suppose `A` is a β-reduct of a term nameable with the two
names `x`, `y`, and suppose `U` is a closed term that is not β-convertible to any
such nameable term.  Then no applicative combination of `A` is β-convertible to
`U`; in particular `A` is not a one-point basis. -/
theorem not_betaConv_of_betaReductOfNamable
    {A : Term String} (hA : BetaReductOfNamable A)
    {U : Term String} (hU : ∀ S, namableXY S = true → ¬ BetaConv S U)
    {C : Term String} (hC : ClosedUnderApp (fun t => t = A) C) : ¬ BetaConv C U := by
  have hCcl : BetaReductOfNamable C := by
    refine BetaReductOfNamable.closedUnderApp ?_
    induction hC with
    | base hb => exact ClosedUnderApp.base (hb ▸ hA)
    | app _ _ iha ihb => exact ClosedUnderApp.app iha ihb
  obtain ⟨S, hS, hconv⟩ := exists_namableXY_betaConv hCcl
  intro hCU
  exact hU S hS (Relation.EqvGen.trans _ _ _ hconv hCU)
