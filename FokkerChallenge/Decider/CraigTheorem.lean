import FokkerChallenge.Decider.ArgNotVar
import FokkerChallenge.Decider.CompositiveEffect

/-!
# Craig's theorem: no proper combinator is a one-point basis

A *proper combinator* is a term

```
X = λ x₁ … λ x_s . E
```

whose body `E` is an applicative combination of variables — no abstraction
occurs inside `E`.  This is exactly the predicate `is_combinator` of
`FokkerChallenge/Combinator.lean`.

The theorem proved here (`is_combinator_lc_not_basis`) is that a locally closed
proper combinator is never a one-point basis.  It is obtained by combining the
two deciders that already exist in this development, according to whether the
body of the combinator needs parentheses:

* if `E` needs **no** parentheses — every argument of every application of `E`
  is a variable — then `X` has no *compositive effect* in Curry's sense and
  `FokkerChallenge/Decider/CompositiveEffect.lean` applies: no combination of
  `X` reduces to the composition combinator `B = λx.λy.λz. x (y z)`;
* if `E` **does** need parentheses, then some argument of the (unique)
  application spine of the body is not a variable, so `X` is argument-safe in
  the sense of `FokkerChallenge/Decider/ArgNotVar.lean` — the λ-calculus form of
  Bellot's proof of Craig's theorem — and no combination of `X` reduces to
  `K = λx.λy.x`.

The decider of `CompositiveEffect.lean` is stated for *closed* terms, while the
statement here only assumes local closedness.  The gap is bridged by
`not_basis_of_subst`: substituting a closed term for a free variable can only
make a term "more of a basis", so it suffices to substitute `I = λx.x` for the
free variables one at a time and to apply the closed-case decider at the end
(`noCompositive_lc_not_basis`).
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

def is_combinator : Term String → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .abs t => is_combinator t
  | .app a b => ClosedUnderAppBool isVar (a.app b)

/-! ## Substituting a closed term for a free variable -/

/-- Substituting a closed term for `x` removes exactly `x` from the free variables. -/
theorem fv_subst_of_fv_empty {M C : Term String} {x : String} (hC : C.fv = ∅) :
    (M[x := C]).fv = M.fv.erase x := by
  induction M with
  | bvar i => simp [subst_bvar]
  | fvar y =>
      by_cases h : x = y
      · subst h; simp [subst_fvar, hC]
      · simp [subst_fvar, h]
  | abs t ih => simpa [subst_abs] using ih
  | app f a ih₁ ih₂ => simp [subst_app, ih₁, ih₂, Finset.erase_union_distrib]

/-- A combination of `X`s maps to a combination of `X[x := C]`s. -/
theorem gen_subst {X C t : Term String} {x : String} (h : Gen X t) :
    Gen (X[x := C]) (t[x := C]) := by
  induction h with
  | base ht =>
      rename_i a
      have hXt : a = X := by simpa using ht
      subst hXt
      exact .base (by simp)
  | app _ _ iha ihb => exact .app iha ihb

/-- **Substitution reflects `not_basis`.**  If some closed term is unreachable from
the combinations of `X[x := C]`, then it is unreachable from the combinations of `X`. -/
theorem not_basis_of_subst {X C : Term String} {x : String} (hC : C.LC)
    (h : not_basis (X[x := C])) : not_basis X := by
  obtain ⟨y, hlc, hfv, hy⟩ := h
  refine ⟨y, hlc, hfv, ?_⟩
  intro t hgen hred
  refine hy (t[x := C]) (gen_subst hgen) ?_
  have hsub := FullBetaEta.steps_subst_cong_l t y C x hred hC
  rwa [subst_fresh x y C (by simp [hfv])] at hsub

/-! ## Closing off the free variables of a term without compositive effect -/

theorem isClosedTerm_I : isClosedTerm I := by decide

theorem noCompositive_I : noCompositive I := by decide

/-- The invariant `noCompositive` survives the substitution of a closed term without
compositive effect. -/
theorem noCompositive_subst {M C : Term String} {x : String} (hC : isClosedTerm C)
    (hCn : noCompositive C) (h : noCompositive M) : noCompositive (M[x := C]) := by
  induction M with
  | bvar i => simp [subst_bvar]
  | fvar y => by_cases hxy : x = y <;> simp [subst_fvar, hxy, hCn]
  | abs t ih => simpa [subst_abs] using ih (by simpa using h)
  | app f a ih₁ ih₂ =>
      simp only [noCompositive_app, Bool.and_eq_true] at h
      simp only [subst_app, noCompositive_app, Bool.and_eq_true]
      refine ⟨⟨ih₁ h.1.1, ih₂ h.1.2⟩, ?_⟩
      rcases Bool.or_eq_true _ _ |>.mp h.2 with hv | hcl
      · match a with
        | .bvar i => simp [subst_bvar, argSafe, isVar]
        | .fvar y =>
            by_cases hxy : x = y
            · simpa [subst_fvar, hxy] using argSafe_of_isClosedTerm hC
            · simp [subst_fvar, hxy, argSafe, isVar]
        | .abs _ => simp [isVar] at hv
        | .app _ _ => simp [isVar] at hv
      · rw [subst_fresh x a C (by simp [isClosedTerm_fv hcl])]
        exact argSafe_of_isClosedTerm hcl

/-- **The compositive-effect decider for locally closed terms.**  Closedness is not
needed: a locally closed term all of whose application arguments are variables or
closed terms is not a one-point basis. -/
theorem noCompositive_lc_not_basis {X : Term String} (h : noCompositive X) (hlc : X.LC) :
    not_basis X := by
  suffices H : ∀ (n : ℕ) (Y : Term String), Y.fv.card ≤ n → noCompositive Y → Y.LC →
      not_basis Y from H X.fv.card X le_rfl h hlc
  intro n
  induction n with
  | zero =>
      intro Y hcard hY hYlc
      exact noCompositive_not_basis hY
        (isClosedTerm_of (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)) hYlc)
  | succ n ih =>
      intro Y hcard hY hYlc
      by_cases hempty : Y.fv = ∅
      · exact noCompositive_not_basis hY (isClosedTerm_of hempty hYlc)
      · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        refine not_basis_of_subst (C := I) (x := x) (isClosedTerm_lc isClosedTerm_I)
          (ih _ ?_ ?_ ?_)
        · rw [fv_subst_of_fv_empty (isClosedTerm_fv isClosedTerm_I)]
          have := Finset.card_erase_of_mem hx
          omega
        · exact noCompositive_subst isClosedTerm_I noCompositive_I hY
        · exact subst_lc hYlc (isClosedTerm_lc isClosedTerm_I)

/-- A term all of whose application arguments are variables satisfies the invariant. -/
theorem noCompositive_of_noParens {M : Term String} (h : noParens M) : noCompositive M := by
  induction M with
  | bvar i => rfl
  | fvar y => rfl
  | abs t ih => simpa using ih (by simpa using h)
  | app f a ih₁ ih₂ =>
      simp only [noParens_app, Bool.and_eq_true] at h
      simp only [noCompositive_app, Bool.and_eq_true]
      exact ⟨⟨ih₁ h.1, ih₂ (noParens_of_isVar h.2)⟩, argSafe_of_isVar h.2⟩

/-- **No parentheses, no basis.**  A locally closed term whose application arguments
are all variables is not a one-point basis. -/
theorem noParens_lc_not_basis {X : Term String} (h : noParens X) (hlc : X.LC) : not_basis X :=
  noCompositive_lc_not_basis (noCompositive_of_noParens h) hlc

/-! ## Proper combinators with parentheses are argument-safe -/

/-- `is_combinator` describes exactly the terms `λ … λ. E` with `E` a combination of
variables. -/
theorem isCombOfVars_of_closedUnderAppBool {M : Term String}
    (h : ClosedUnderAppBool isVar M) : isCombOfVars M := by
  induction M with
  | bvar i => rfl
  | fvar y => rfl
  | abs t => simp [ClosedUnderAppBool, isVar] at h
  | app f a ih₁ ih₂ =>
      simp only [ClosedUnderAppBool, Bool.and_eq_true] at h
      simp only [isCombOfVars, Bool.and_eq_true]
      exact ⟨ih₁ h.1, ih₂ h.2⟩

/-- A combination of variables contains no abstraction, hence is argument-safe. -/
theorem argOk_of_isCombOfVars {M : Term String} (h : isCombOfVars M) : argOk M := by
  induction M with
  | bvar i => rfl
  | fvar y => rfl
  | abs t => simp [isCombOfVars] at h
  | app f a ih₁ ih₂ =>
      simp only [isCombOfVars, Bool.and_eq_true] at h
      simp [ih₁ h.1, ih₂ h.2]

/-- A combination of variables that needs parentheses has a non-variable argument on
its spine, so it is a legitimate block body. -/
theorem spineOk_of_isCombOfVars {M : Term String} (h : isCombOfVars M)
    (hp : noParens M = false) : spineOk M := by
  induction M with
  | bvar i => exact Bool.noConfusion hp
  | fvar y => exact Bool.noConfusion hp
  | abs t => simp [isCombOfVars] at h
  | app f a ih₁ _ =>
      simp only [isCombOfVars, Bool.and_eq_true] at h
      simp only [noParens_app, Bool.and_eq_false_iff] at hp
      simp only [spineOk_app, Bool.and_eq_true, Bool.or_eq_true]
      refine ⟨argOk_of_isCombOfVars h.2, ?_⟩
      rcases hp with hf | ha
      · exact Or.inl (ih₁ h.1 hf)
      · exact Or.inr ⟨argOk_of_isCombOfVars h.1, by simp [ha]⟩

/-- A proper combinator whose body needs parentheses is a legitimate block body. -/
theorem spineOk_of_isProperBody {M : Term String} (h : isProperBody M)
    (hp : noParens M = false) : spineOk M := by
  induction M with
  | bvar i => exact Bool.noConfusion hp
  | fvar y => exact Bool.noConfusion hp
  | abs t ih =>
      rw [isProperBody] at h
      rw [spineOk_abs]
      exact ih h (by simpa using hp)
  | app f a _ _ =>
      rw [isProperBody] at h
      exact spineOk_of_isCombOfVars (by rwa [isCombOfVars]) hp

/-- A proper combinator whose body needs parentheses is argument-safe. -/
theorem argOk_of_isProperBody {M : Term String} (h : isProperBody M)
    (hp : noParens M = false) : argOk M := by
  match M with
  | .bvar i => exact Bool.noConfusion hp
  | .fvar y => exact Bool.noConfusion hp
  | .abs t =>
      rw [argOk_abs]
      exact spineOk_of_isProperBody (by rwa [isProperBody] at h) (by simpa using hp)
  | .app f a =>
      rw [isProperBody] at h
      exact argOk_of_isCombOfVars (by rwa [isCombOfVars])

/-- `is_combinator` terms are proper: they are of the shape `λ … λ. E` with `E` a
combination of variables.  (`isProperBody` is slightly more liberal: it also allows
the body `E` to be a single variable, as in `K = λx.λy.x`.) -/
theorem isProperBody_of_is_combinator {M : Term String} (h : is_combinator M) :
    isProperBody M := by
  induction M with
  | bvar i => grind
  | fvar y => grind
  | abs t ih => rw [isProperBody]; exact ih (by rwa [is_combinator] at h)
  | app f a _ _ =>
      rw [is_combinator] at h
      have := isCombOfVars_of_closedUnderAppBool h
      rwa [isCombOfVars, ← isProperBody] at this

/-! ## Craig's theorem -/

/-- **Craig's theorem.**  A locally closed *proper combinator* — a term
`λ x₁ … λ x_s . E` whose body `E` is an applicative combination of variables — is
never a one-point basis.

The two cases of the proof are the two deciders: if the body needs no parentheses
then `X` has no compositive effect and no combination of `X` reaches the composition
combinator `B`; if it does need parentheses then `X` is argument-safe and no
combination of `X` reaches `K`. -/
theorem isProperBody_lc_not_basis {X : Term String} (h : isProperBody X) (hlc : X.LC) :
    not_basis X := by
  cases hp : noParens X with
  | true => exact noParens_lc_not_basis hp hlc
  | false => exact argOk_not_basis (argOk_of_isProperBody h hp)

/-- **Craig's theorem, for `is_combinator`.**  A locally closed term
`λ x₁ … λ x_s . E` whose body `E` is an *application* of variables is never a
one-point basis. -/
theorem is_combinator_lc_not_basis {X : Term String} (h : is_combinator X) (hlc : X.LC) :
    not_basis X :=
  isProperBody_lc_not_basis (isProperBody_of_is_combinator h) hlc

end Term

end LambdaCalculus.LocallyNameless.Untyped

end Cslib
