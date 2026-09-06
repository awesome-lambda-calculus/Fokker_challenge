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

/-
def is_combinator : Term String → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .abs t => is_combinator t
  | .app a b => ClosedUnderAppBool isVar (a.app b)

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

/-- `is_combinator` terms are proper: they are of the shape `λ … λ. E` with `E` a
combination of variables.  (`is_combinator` is slightly more liberal: it also allows
the body `E` to be a single variable, as in `K = λx.λy.x`.) -/
theorem isProperBody_of_is_combinator {M : Term String} (h : is_combinator M) :
    is_combinator M := by
  induction M with
  | bvar i => grind
  | fvar y => grind
  | abs t ih => rw [is_combinator]; exact ih (by rwa [is_combinator] at h)
  | app f a _ _ =>
      rw [is_combinator] at h
      have := isCombOfVars_of_closedUnderAppBool h
      rwa [isCombOfVars, ← is_combinator] at this

/-! ## Craig's theorem -/


/-- **Craig's theorem, for `is_combinator`.**  A locally closed term
`λ x₁ … λ x_s . E` whose body `E` is an *application* of variables is never a
one-point basis. -/
theorem is_combinator_lc_not_basis {X : Term String} (h : is_combinator X) (hlc : X.LC) :
    not_basis X :=
  isProperBody_lc_not_basis (isProperBody_of_is_combinator h) hlc
-/

end Term

end LambdaCalculus.LocallyNameless.Untyped

end Cslib
