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


/-! ## Proper combinators and parentheses

For a proper combinator the invariant `noCompositive` is exactly Curry's criterion
"the body contains no parentheses". -/

/-- `isCombOfVars M`: `M` is an applicative combination of variables. -/
@[scoped grind unfold]
def isCombOfVars := ClosedUnderAppBool isVar

/-- `is_combinator M`: `M` is of the shape `λ x₁ … λ x_n . E` with `E` an applicative
combination of variables; together with closedness this is Curry's notion of a proper
combinator. -/
@[scoped grind]
def is_combinator : Term String → Bool
  | .abs t => is_combinator t
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
  | abs t => grind
  | app f a ih₁ ih₂ =>
      simp only [isCombOfVars] at h
      simp only [fv, Finset.union_eq_empty] at hfv
      grind

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
  | abs t => grind
  | app f a ih₁ ih₂ =>
      simp only [isCombOfVars] at h
      simp only [fv, Finset.union_eq_empty] at hfv
      have hargs : argSafe a = isVar a := by
        simp [argSafe, isClosedTerm_eq_false_of_isCombOfVars (by grind) hfv.2]
      simp only [noCompositive_app, noParens_app, ih₁ (by grind) hfv.1, ih₂ (by grind) hfv.2, hargs]
      cases hv : isVar a with
      | true => simp [noParens_of_isVar hv]
      | false => simp

/-- **The invariant is Curry's criterion.**  For a closed proper combinator,
`noCompositive` says exactly that the body contains no parentheses. -/
theorem noCompositive_eq_noParens {M : Term String} (h : is_combinator M) (hfv : M.fv = ∅) :
    noCompositive M = noParens M := by
  induction M with
  | bvar j => rfl
  | fvar y => rfl
  | abs t ih => simpa using ih (by simpa [is_combinator] using h) (by simpa using hfv)
  | app f a _ _ =>
      refine noCompositive_eq_noParens_of_isCombOfVars ?_ hfv
      rw [isCombOfVars]
      rwa [is_combinator] at h

/-! ## Curry's theorem -/

/-- **A combination of proper combinators without compositive effect has no compositive
effect.**  If every atom of `fs` is a proper combinator with no compositive effect, if
`X` is an applicative combination of these atoms, if `X` βη-reduces to `Y` and if `Y` is
again proper, then `Y` has no compositive effect either. -/
theorem no_compositive_effect_of_combination {fs : List (Term String)}
    (hproper : ∀ t ∈ fs, is_combinator t) (hcl : ∀ t ∈ fs, isClosedTerm t)
    (hpar : ∀ t ∈ fs, noParens t) {X Y : Term String} (hX : GenFinset fs X) (hXY : X ↠βηᶠ Y)
    (hY : is_combinator Y) : noParens Y := by
  have hfs : ∀ t ∈ fs, noCompositive t := by
    intro t ht
    rw [noCompositive_eq_noParens (hproper t ht) (isClosedTerm_fv (hcl t ht))]
    exact hpar t ht
  have hXc := genFinset_isClosedTerm hcl hX
  have hYc := isClosedTerm_fullBetaEta_star hXY hXc
  have hYn := noCompositive_fullBetaEta_star hXY (genFinset_noCompositive hfs hcl hX)
  rwa [noCompositive_eq_noParens hY (isClosedTerm_fv hYc)] at hYn

/-- A combination of variables contains no abstraction, hence is argument-safe. -/
theorem argOk_of_isCombOfVars {M : Term String} (h : isCombOfVars M) : argOk M := by
  induction M with
  | bvar i => rfl
  | fvar y => rfl
  | abs t => grind
  | app f a ih₁ ih₂ =>
      simp only [isCombOfVars] at h
      simp [ih₁ (by grind), ih₂ (by grind)]


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

/-- A combination of variables that needs parentheses has a non-variable argument on
its spine, so it is a legitimate block body. -/
theorem spineOk_of_isCombOfVars {M : Term String} (h : isCombOfVars M)
    (hp : noParens M = false) : spineOk M := by
  induction M with
  | bvar i => exact Bool.noConfusion hp
  | fvar y => exact Bool.noConfusion hp
  | abs t => grind
  | app f a ih₁ _ =>
      simp only [isCombOfVars] at h
      simp only [noParens_app, Bool.and_eq_false_iff] at hp
      simp only [spineOk_app, Bool.and_eq_true, Bool.or_eq_true]
      refine ⟨argOk_of_isCombOfVars (by grind), ?_⟩
      rcases hp with hf | ha
      · exact Or.inl (ih₁ (by grind) hf)
      · exact Or.inr ⟨argOk_of_isCombOfVars (by grind), by simp [ha]⟩

/-- A proper combinator whose body needs parentheses is a legitimate block body. -/
theorem spineOk_of_isProperBody {M : Term String} (h : is_combinator M)
    (hp : noParens M = false) : spineOk M := by
  induction M with
  | bvar i => exact Bool.noConfusion hp
  | fvar y => exact Bool.noConfusion hp
  | abs t ih =>
      rw [is_combinator] at h
      rw [spineOk_abs]
      exact ih h (by simpa using hp)
  | app f a _ _ =>
      rw [is_combinator] at h
      exact spineOk_of_isCombOfVars (by rwa [isCombOfVars]) hp


/-- A proper combinator whose body needs parentheses is argument-safe. -/
theorem argOk_of_isProperBody {M : Term String} (h : is_combinator M)
    (hp : noParens M = false) : argOk M := by
  match M with
  | .bvar i => exact Bool.noConfusion hp
  | .fvar y => exact Bool.noConfusion hp
  | .abs t =>
      rw [argOk_abs]
      exact spineOk_of_isProperBody (by rwa [is_combinator] at h) (by simpa using hp)
  | .app f a =>
      rw [is_combinator] at h
      exact argOk_of_isCombOfVars (by rwa [isCombOfVars])

/-- **Craig's theorem.**  A locally closed *proper combinator* — a term
`λ x₁ … λ x_s . E` whose body `E` is an applicative combination of variables — is
never a one-point basis.

The two cases of the proof are the two deciders: if the body needs no parentheses
then `X` has no compositive effect and no combination of `X` reaches the composition
combinator `B`; if it does need parentheses then `X` is argument-safe and no
combination of `X` reaches `K`. -/
theorem isProperBody_lc_not_basis {X : Term String} (h : is_combinator X) (hlc : X.LC) :
    not_basis X := by
  cases hp : noParens X with
  | true => exact noParens_lc_not_basis hp hlc
  | false => exact argOk_not_basis (argOk_of_isProperBody h hp)

end Term

end LambdaCalculus.LocallyNameless.Untyped

end Cslib
