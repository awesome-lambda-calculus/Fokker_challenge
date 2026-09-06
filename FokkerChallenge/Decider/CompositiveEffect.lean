import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import FokkerChallenge.Basic
import FokkerChallenge.EnhancedCslib.Basic
import FokkerChallenge.EnhancedCslib.GenFinset
import FokkerChallenge.FamousCombinator
import FokkerChallenge.DBNotation
import FokkerChallenge.Decider.TailNotVar

/-!
# The "compositive effect" decider

A *proper combinator* is a closed term `X = λ x₁ … λ x_n . M` whose body `M` is
an applicative combination of the variables `x₁, …, x_n` (no abstraction occurs
inside `M`).  Following Curry, `X` has a **compositive effect** when its body
needs parentheses, i.e. when some argument of an application of `M` is not a
variable; the composition combinator `B = λx.λy.λz. x (y z)` is the basic
example, while `K`, `C`, `W`, `I`, … have no compositive effect.

The theorem formalised here is the classical statement

> Let `X` be a combination of proper combinators none of which has any
> compositive effect, and let `X` be proper.  Then `X` has no compositive
> effect.

(`noParens_of_genFinset`, and `no_compositive_effect_of_combination` for its
reduction-closed form).  Since `B` *is* proper and *does* have a compositive
effect, no combination of compositive-effect-free proper combinators can
βη-reduce to `B`, so such a combinator is not a one-point basis
(`noCompositive_not_basis`).

The invariant that makes all of this work in the full λ-calculus is `noCompositive`:

> in every application, the argument is either a variable or a **closed** term.

* it holds for a proper combinator without compositive effect (a closed proper
  body has no closed proper subterm in argument position, see
  `noCompositive_eq_noParens`);
* it is closed under application of closed terms, because a combination of
  closed terms is closed;
* it is preserved by β: the argument of a redex is, by the invariant itself, a
  variable or a closed term, and substituting such a term for a variable keeps
  every argument a variable or a closed term;
* it is preserved by η: an η-step only deletes the application of a variable;
* and it fails for `B`, whose argument `y z` is neither a variable nor closed.
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-! ## Closed terms -/

/-- `isClosedTerm M`: `M` has no free variable and no dangling bound variable. -/
def isClosedTerm (M : Term String) : Bool := decide (M.fv = ∅) && LcAt 0 M

theorem isClosedTerm_fv {M : Term String} (h : isClosedTerm M) : M.fv = ∅ := by
  simp only [isClosedTerm, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1

theorem isClosedTerm_lcAt {M : Term String} (h : isClosedTerm M) : LcAt 0 M := by
  simp only [isClosedTerm, Bool.and_eq_true] at h; exact h.2

theorem isClosedTerm_lc {M : Term String} (h : isClosedTerm M) : M.LC :=
  (lcAt_iff_LC M).mp (isClosedTerm_lcAt h)

theorem isClosedTerm_of {M : Term String} (hfv : M.fv = ∅) (hlc : M.LC) : isClosedTerm M := by
  simp only [isClosedTerm, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hfv, (lcAt_iff_LC M).mpr hlc⟩

/-- A closed term is unchanged by opening. -/
theorem openRec_of_isClosedTerm {M U : Term String} {i : ℕ} (h : isClosedTerm M) :
    M⟦i ↝ U⟧ = M :=
  lcAt_openRec_above_lcAt M U 0 i (Nat.zero_le i) (isClosedTerm_lcAt h)

/-- If opening with a free variable produces a term without free variables, then the
variable was not inserted at all. -/
theorem openRec_fvar_eq_self_of_fv_empty {M : Term String} {x : String} :
    ∀ i, (M⟦i ↝ Term.fvar x⟧).fv = ∅ → M⟦i ↝ Term.fvar x⟧ = M := by
  intro i h
  induction M generalizing i with
  | bvar j =>
      by_cases hij : i = j
      · simp [openRec, hij] at h
      · simp [openRec, hij]
  | fvar y => rfl
  | abs t ih =>
      simp only [openRec, fv] at h ⊢
      rw [ih _ h]
  | app f a ih₁ ih₂ =>
      simp only [openRec, fv, Finset.union_eq_empty] at h ⊢
      rw [ih₁ _ h.1, ih₂ _ h.2]

/-- Opening with a free variable does not change closedness. -/
theorem isClosedTerm_openRec_fvar {M : Term String} {x : String} (i : ℕ) :
    isClosedTerm (M⟦i ↝ Term.fvar x⟧) = isClosedTerm M := by
  cases hb : isClosedTerm M with
  | true => rw [openRec_of_isClosedTerm hb]; exact hb
  | false =>
      by_contra hc
      simp only [Bool.not_eq_false] at hc
      rw [openRec_fvar_eq_self_of_fv_empty i (isClosedTerm_fv hc)] at hc
      rw [hc] at hb
      exact Bool.noConfusion hb

/-! ## The invariant -/

/-- `argSafe M`: `M` may occur as the argument of an application, i.e. it is a variable
or a closed term. -/
def argSafe (M : Term String) : Bool := isVar M || isClosedTerm M

/-- `noCompositive M`: every argument of every application of `M` is a variable or a
closed term. -/
def noCompositive : Term String → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .abs t => noCompositive t
  | .app f a => noCompositive f && noCompositive a && argSafe a

@[simp] theorem noCompositive_bvar {i} : noCompositive (.bvar i) = true := by rw [noCompositive]
@[simp] theorem noCompositive_fvar {x} : noCompositive (.fvar x) = true := by rw [noCompositive]
@[simp] theorem noCompositive_abs {t} : noCompositive (.abs t) = noCompositive t := by
  rw [noCompositive]
@[simp] theorem noCompositive_app {f a} :
    noCompositive (.app f a) = (noCompositive f && noCompositive a && argSafe a) := by
  rw [noCompositive]

theorem argSafe_of_isVar {M : Term String} (h : isVar M) : argSafe M := by
  simp [argSafe, h]

theorem argSafe_of_isClosedTerm {M : Term String} (h : isClosedTerm M) : argSafe M := by
  simp [argSafe, h]

theorem argSafe_openRec_fvar {M : Term String} {x : String} (i : ℕ) :
    argSafe (M⟦i ↝ Term.fvar x⟧) = argSafe M := by
  simp [argSafe, isVar_openRec_fvar, isClosedTerm_openRec_fvar]

theorem noCompositive_openRec_fvar {M : Term String} {x : String} :
    ∀ i, noCompositive (M⟦i ↝ Term.fvar x⟧) = noCompositive M := by
  intro i
  induction M generalizing i with
  | bvar j => by_cases hij : i = j <;> simp [openRec, hij]
  | fvar y => rfl
  | abs t ih => simpa [openRec] using ih (i + 1)
  | app f a ih₁ ih₂ => simp [openRec, ih₁ i, ih₂ i, argSafe_openRec_fvar (M := a) i]

/-! ## Stability under substitution -/

theorem argSafe_openRec {M U : Term String} (hU : argSafe U) :
    ∀ i, argSafe M → argSafe (M⟦i ↝ U⟧) := by
  intro i hM
  match M with
  | .bvar j =>
      by_cases hij : i = j
      · simpa [openRec, hij] using hU
      · simp [openRec, hij, argSafe, isVar]
  | .fvar y => simpa [openRec] using hM
  | .abs t =>
      have hc : isClosedTerm (Term.abs t) := by
        simpa [argSafe, isVar] using hM
      rw [openRec_of_isClosedTerm hc]; exact hM
  | .app f a =>
      have hc : isClosedTerm (Term.app f a) := by
        simpa [argSafe, isVar] using hM
      rw [openRec_of_isClosedTerm hc]; exact hM

theorem noCompositive_openRec {M U : Term String} (hU : noCompositive U) (hUs : argSafe U) :
    ∀ i, noCompositive M → noCompositive (M⟦i ↝ U⟧) := by
  intro i hM
  induction M generalizing i with
  | bvar j => by_cases hij : i = j <;> simp [openRec, hij, hU]
  | fvar y => simp [openRec]
  | abs t ih => simpa [openRec] using ih (i + 1) (by simpa using hM)
  | app f a ih₁ ih₂ =>
      simp only [noCompositive_app, Bool.and_eq_true] at hM
      simp only [openRec, noCompositive_app, Bool.and_eq_true]
      exact ⟨⟨ih₁ i hM.1.1, ih₂ i hM.1.2⟩, argSafe_openRec hUs i hM.2⟩

/-- Contracting a β-redex whose argument is a variable or a closed term. -/
theorem noCompositive_open {T U : Term String} (hT : noCompositive T) (hU : noCompositive U)
    (hUs : argSafe U) : noCompositive (T ^ U) :=
  noCompositive_openRec hU hUs 0 hT

/-! ## Closedness is preserved by reduction -/

theorem isClosedTerm_fullBeta {M N : Term String} (h : FullBeta M N) (hM : isClosedTerm M) :
    isClosedTerm N := by
  refine isClosedTerm_of ?_ (FullBeta.step_lc_r h)
  have hsub := FullBeta.step_not_fv h
  rw [isClosedTerm_fv hM] at hsub
  exact Finset.subset_empty.mp hsub

theorem isClosedTerm_fullEta {M N : Term String} (h : FullEta M N) (hM : isClosedTerm M) :
    isClosedTerm N := by
  refine isClosedTerm_of ?_ (FullEta.step_lc_r h)
  rw [← FullEta.step_not_fv h]
  exact isClosedTerm_fv hM

theorem isClosedTerm_fullBetaEta {M N : Term String} (h : FullBetaEta M N)
    (hM : isClosedTerm M) : isClosedTerm N := by
  rcases h with h | h
  · exact isClosedTerm_fullBeta h hM
  · exact isClosedTerm_fullEta h hM

/-! ## The invariant is preserved by reduction -/

theorem isVar_eq_false_of_xi {R : Term String → Term String → Prop}
    (hsrc : ∀ {M N}, R M N → isVar M = false) {M N : Term String} (h : Xi R M N) :
    isVar M = false := by
  cases h with
  | base hR => exact hsrc hR
  | appL _ _ => rfl
  | appR _ _ => rfl
  | abs _ _ => rfl

/-- The generic congruence step. -/
theorem noCompositive_xi {R : Term String → Term String → Prop}
    (hnc : ∀ {M N}, R M N → noCompositive M → noCompositive N)
    (hsrc : ∀ {M N}, R M N → isVar M = false)
    (hcl : ∀ {M N}, Xi R M N → isClosedTerm M → isClosedTerm N)
    {M N : Term String} (h : Xi R M N) : noCompositive M → noCompositive N := by
  induction h with
  | base hR => exact hnc hR
  | @appL Z M₀ N₀ _ hstep ih =>
      intro hM
      simp only [noCompositive_app, Bool.and_eq_true] at hM ⊢
      refine ⟨⟨hM.1.1, ih hM.1.2⟩, ?_⟩
      have hv : isVar M₀ = false := isVar_eq_false_of_xi hsrc hstep
      have hc : isClosedTerm M₀ := by
        have := hM.2
        simp only [argSafe, hv, Bool.false_or] at this
        exact this
      exact argSafe_of_isClosedTerm (hcl hstep hc)
  | @appR M₀ N₀ Z _ _ ih =>
      intro hM
      simp only [noCompositive_app, Bool.and_eq_true] at hM ⊢
      exact ⟨⟨ih hM.1.1, hM.1.2⟩, hM.2⟩
  | @abs T T' xs _ ih =>
      intro hM
      obtain ⟨y, hy⟩ : ∃ y : String, y ∉ xs := Finset.exists_notMem _
      have h1 : noCompositive (T ^ Term.fvar y) := by
        rw [open', noCompositive_openRec_fvar]; simpa using hM
      have h2 := ih y hy h1
      rw [open', noCompositive_openRec_fvar] at h2
      simpa using h2

theorem noCompositive_beta {M N : Term String} (h : Beta M N) (hM : noCompositive M) :
    noCompositive N := by
  cases h with
  | @beta T U _ _ =>
      simp only [noCompositive_app, noCompositive_abs, Bool.and_eq_true] at hM
      exact noCompositive_open hM.1.1 hM.1.2 hM.2

theorem noCompositive_eta {M N : Term String} (h : Eta M N) (hM : noCompositive M) :
    noCompositive N := by
  cases h with
  | @eta P _ =>
      simp only [noCompositive_abs, noCompositive_app, Bool.and_eq_true] at hM
      exact hM.1.1

theorem noCompositive_fullBeta {M N : Term String} (h : FullBeta M N) (hM : noCompositive M) :
    noCompositive N :=
  noCompositive_xi (fun hR hM => noCompositive_beta hR hM)
    (fun hR => by cases hR; rfl)
    (fun hstep hc => isClosedTerm_fullBeta hstep hc) h hM

theorem noCompositive_fullEta {M N : Term String} (h : FullEta M N) (hM : noCompositive M) :
    noCompositive N :=
  noCompositive_xi (fun hR hM => noCompositive_eta hR hM)
    (fun hR => by cases hR; rfl)
    (fun hstep hc => isClosedTerm_fullEta hstep hc) h hM

theorem noCompositive_fullBetaEta {M N : Term String} (h : FullBetaEta M N)
    (hM : noCompositive M) : noCompositive N := by
  rcases h with h | h
  · exact noCompositive_fullBeta h hM
  · exact noCompositive_fullEta h hM

theorem noCompositive_fullBetaEta_star {M N : Term String} (h : M ↠βηᶠ N)
    (hM : noCompositive M) : noCompositive N := by
  induction h with
  | refl => exact hM
  | tail _ hstep ih => exact noCompositive_fullBetaEta hstep ih

theorem isClosedTerm_fullBetaEta_star {M N : Term String} (h : M ↠βηᶠ N)
    (hM : isClosedTerm M) : isClosedTerm N := by
  induction h with
  | refl => exact hM
  | tail _ hstep ih => exact isClosedTerm_fullBetaEta hstep ih

/-! ## Closure under application -/

theorem genFinset_isClosedTerm {fs : List (Term String)} {M : Term String}
    (hfs : ∀ t ∈ fs, isClosedTerm t) (h : GenFinset fs M) : isClosedTerm M := by
  induction h with
  | base ht => exact hfs _ ht
  | app _ _ iha ihb =>
      exact isClosedTerm_of (by simp [isClosedTerm_fv iha, isClosedTerm_fv ihb])
        (LC.app (isClosedTerm_lc iha) (isClosedTerm_lc ihb))

theorem genFinset_noCompositive {fs : List (Term String)} {M : Term String}
    (hfs : ∀ t ∈ fs, noCompositive t) (hcl : ∀ t ∈ fs, isClosedTerm t) (h : GenFinset fs M) :
    noCompositive M := by
  induction h with
  | base ht => exact hfs _ ht
  | @app a b ha hb iha ihb =>
      simp only [noCompositive_app, Bool.and_eq_true]
      exact ⟨⟨iha, ihb⟩, argSafe_of_isClosedTerm (genFinset_isClosedTerm hcl hb)⟩

/-! ## The composition combinator -/

/-- `B = λx.λy.λz. x (y z)`, the composition combinator. -/
def Bcomb : Term String := db! "λλλ2(10)"

theorem Bcomb_lc : Bcomb.LC := by rw [← lcAt_iff_LC]; decide

theorem Bcomb_fv : Bcomb.fv = ∅ := by decide

/-- `B` has a compositive effect: its argument `y z` is neither a variable nor closed. -/
theorem noCompositive_Bcomb : noCompositive Bcomb = false := by decide

/-! ## The decider -/

/-- **The compositive-effect decider.**  No applicative combination of closed terms
without compositive effect βη-reduces to the composition combinator `B`; in particular
such a term is not a one-point basis. -/
theorem noCompositive_not_basises (fs : List (Term String))
    (hfs : ∀ t ∈ fs, noCompositive t) (hcl : ∀ t ∈ fs, isClosedTerm t) : not_basises fs := by
  refine ⟨Bcomb, Bcomb_lc, Bcomb_fv, ?_⟩
  intro Y hgen hred
  have h1 := genFinset_noCompositive hfs hcl hgen
  have h2 := noCompositive_fullBetaEta_star hred h1
  rw [noCompositive_Bcomb] at h2
  exact Bool.noConfusion h2

theorem noCompositive_not_basis {X : Term String} (h : noCompositive X)
    (hcl : isClosedTerm X) : not_basis X := by
  apply noCompositive_not_basises <;> grind

/-! ## Proper combinators and parentheses

For a proper combinator the invariant `noCompositive` is exactly Curry's criterion
"the body contains no parentheses". -/

/-- `isCombOfVars M`: `M` is an applicative combination of variables. -/
def isCombOfVars : Term String → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .app f a => isCombOfVars f && isCombOfVars a
  | .abs _ => false

/-- `isProperBody M`: `M` is of the shape `λ x₁ … λ x_n . E` with `E` an applicative
combination of variables; together with closedness this is Curry's notion of a proper
combinator. -/
@[scoped grind]
def isProperBody : Term String → Bool
  | .abs t => isProperBody t
  | .app f a => isCombOfVars f && isCombOfVars a
  | .bvar _ => true
  | .fvar _ => true

/-- `noParens M`: no argument of an application of `M` is parenthesised, i.e. every
argument is a variable.  For a proper combinator, `!noParens M` is Curry's *compositive
effect*. -/
def noParens : Term String → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .abs t => noParens t
  | .app f a => noParens f && isVar a

@[simp] theorem noParens_abs {t} : noParens (.abs t) = noParens t := by rw [noParens]
@[simp] theorem noParens_app {f a} :
    noParens (.app f a) = (noParens f && isVar a) := by rw [noParens]

theorem noParens_of_isVar {M : Term String} (h : isVar M) : noParens M = true := by
  match M with
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .abs _ => simp [isVar] at h
  | .app _ _ => simp [isVar] at h

/-- A combination of variables without free variables always has a dangling bound
variable, so it is never closed. -/
theorem lcAt_eq_false_of_isCombOfVars {M : Term String} (h : isCombOfVars M)
    (hfv : M.fv = ∅) : LcAt 0 M = false := by
  induction M with
  | bvar j => simp
  | fvar y => simp at hfv
  | abs t => simp [isCombOfVars] at h
  | app f a ih₁ ih₂ =>
      simp only [isCombOfVars, Bool.and_eq_true] at h
      simp only [fv, Finset.union_eq_empty] at hfv
      simp [ih₁ h.1 hfv.1]

theorem isClosedTerm_eq_false_of_isCombOfVars {M : Term String} (h : isCombOfVars M)
    (hfv : M.fv = ∅) : isClosedTerm M = false := by
  simp [isClosedTerm, lcAt_eq_false_of_isCombOfVars h hfv]

/-- For a combination of variables without free variables, the invariant and the
absence of parentheses agree. -/
theorem noCompositive_eq_noParens_of_isCombOfVars {M : Term String} (h : isCombOfVars M)
    (hfv : M.fv = ∅) : noCompositive M = noParens M := by
  induction M with
  | bvar j => rfl
  | fvar y => rfl
  | abs t => simp [isCombOfVars] at h
  | app f a ih₁ ih₂ =>
      simp only [isCombOfVars, Bool.and_eq_true] at h
      simp only [fv, Finset.union_eq_empty] at hfv
      have hargs : argSafe a = isVar a := by
        simp [argSafe, isClosedTerm_eq_false_of_isCombOfVars h.2 hfv.2]
      simp only [noCompositive_app, noParens_app, ih₁ h.1 hfv.1, ih₂ h.2 hfv.2, hargs]
      cases hv : isVar a with
      | true => simp [noParens_of_isVar hv]
      | false => simp

/-- **The invariant is Curry's criterion.**  For a closed proper combinator,
`noCompositive` says exactly that the body contains no parentheses. -/
theorem noCompositive_eq_noParens {M : Term String} (h : isProperBody M) (hfv : M.fv = ∅) :
    noCompositive M = noParens M := by
  induction M with
  | bvar j => rfl
  | fvar y => rfl
  | abs t ih => simpa using ih (by simpa [isProperBody] using h) (by simpa using hfv)
  | app f a _ _ =>
      refine noCompositive_eq_noParens_of_isCombOfVars ?_ hfv
      rw [isCombOfVars]
      rwa [isProperBody] at h

/-! ## Curry's theorem -/

/-- **A combination of proper combinators without compositive effect has no compositive
effect.**  If every atom of `fs` is a proper combinator with no compositive effect, if
`X` is an applicative combination of these atoms, if `X` βη-reduces to `Y` and if `Y` is
again proper, then `Y` has no compositive effect either. -/
theorem no_compositive_effect_of_combination {fs : List (Term String)}
    (hproper : ∀ t ∈ fs, isProperBody t) (hcl : ∀ t ∈ fs, isClosedTerm t)
    (hpar : ∀ t ∈ fs, noParens t) {X Y : Term String} (hX : GenFinset fs X) (hXY : X ↠βηᶠ Y)
    (hY : isProperBody Y) : noParens Y := by
  have hfs : ∀ t ∈ fs, noCompositive t := by
    intro t ht
    rw [noCompositive_eq_noParens (hproper t ht) (isClosedTerm_fv (hcl t ht))]
    exact hpar t ht
  have hXc := genFinset_isClosedTerm hcl hX
  have hYc := isClosedTerm_fullBetaEta_star hXY hXc
  have hYn := noCompositive_fullBetaEta_star hXY (genFinset_noCompositive hfs hcl hX)
  rwa [noCompositive_eq_noParens hY (isClosedTerm_fv hYc)] at hYn

/-- The decider in Curry's formulation: a closed proper combinator without compositive
effect is not a one-point basis. -/
theorem noParens_not_basis {X : Term String} (hproper : isProperBody X)
    (hcl : isClosedTerm X) (hpar : noParens X) : not_basis X := by
  refine noCompositive_not_basis ?_ hcl
  rw [noCompositive_eq_noParens hproper (isClosedTerm_fv hcl)]
  exact hpar

@[simp, scoped grind =]
def properClosedNoParens (X : Term String) : Bool :=
  isProperBody X && isClosedTerm X && noParens X

theorem properClosedNoParens_not_basis {X : Term String}
    (h : properClosedNoParens X) : not_basis X := by grind [noParens_not_basis]

end Term

end LambdaCalculus.LocallyNameless.Untyped

end Cslib
