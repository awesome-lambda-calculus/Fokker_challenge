import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.MultiApp
import FokkerChallenge.DBNotation
import FokkerChallenge.EnhancedCslib.HeadSN
import FokkerChallenge.EnhancedCslib.GenFinset

/-!
# `λλλ0(λ201)` does **not** always have a head normal form

The term

```
X = λλλ0(λ201) = λx y z. z (λw. y w z)
```

is one of the four terms of `undecided_terms.json` whose one-point-basis status is open.
This file answers the question whether *every applicative combination of `X` has a head
normal form* — equivalently, whether every such combination is solvable — in the
**negative**:

* `hnfDivergeStart = X X (X X) (X X X)` is an applicative combination of `X`
  (`hnfDivergeStart_gen`) whose head reduction never terminates
  (`hnfDivergeStart_not_hasHNF`), so it has no head normal form;
* `exists_gen_not_hasHNF` / `not_forall_gen_hasHNF` are the summary statements.

## The divergence

Write `⟨B,C⟩ := λw. B w C` (`pairT`), `P := X X X` and set

```
T 0       = ⟨X X, P⟩,      T (n+1) = ⟨T n, P⟩.
```

The head reduction of `X` obeys two rules, both proved below:

```
X A B C Γ  ↠h  C ⟨B,C⟩ Γ         (`headStepStar_Xc3`)
⟨B,C⟩ U Γ  ⭢h  B U C Γ           (`headStep_pairT`)
```

(the first one because `X` discards its first argument).  With them, the "state"

```
S n Γ := T n ⟨X, T n⟩ Γ
```

head-reduces to `S (n+1) (Pⁿ Γ)` in `n + 8` steps (`headTransGen_state`), so head
reduction from `S 0 []` never terminates, and `X X (X X) (X X X) ↠h S 0 []`
(`hnfDivergeStart_headStepStar_state`).  By the head normalization theorem of
`FokkerChallenge.EnhancedCslib.HeadSN` a term whose head reduction diverges has no head
normal form.

Note that this is *not* an obstruction to `X` being a one-point basis — on the contrary,
a one-point basis must have unsolvable combinations.  What it does show is that the
"every combination has a head normal form" route to a negative answer is closed for `X`.
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-! ## The terms -/

/-- `⟨B,C⟩ = λw. B w C`. -/
def pairT (B C : Term String) : Term String := .abs (.app (.app B (.bvar 0)) C)

/-! ## Local closure -/

theorem lc_pairT {B C : Term String} (hB : LC B) (hC : LC C) : LC (pairT B C) := by
  refine .abs ∅ _ (fun x _ => ?_)
  simp only [open', openRec]
  rw [open_lc 0 (fvar x) B hB, open_lc 0 (fvar x) C hC]
  exact .app (.app hB (.fvar x)) hC

/-! ## The basic head steps -/

theorem headStep_pairT {B C U : Term String} (hB : LC B) (hC : LC C) (hU : LC U) :
    HeadStep (.app (pairT B C) U) (.app (.app B U) C) := by
  have h := HeadStep.beta (M := (.app (.app B (.bvar 0)) C)) (N := U) (lc_pairT hB hC) hU
  have he : (Term.app (.app B (.bvar 0)) C) ^ U = .app (.app B U) C := by
    simp only [open', openRec]
    rw [open_lc 0 U B hB, open_lc 0 U C hC]
    simp
  rwa [he] at h

/-! ## Lifting a head step through a stack of arguments -/

/-! ## The two machine rules -/

/-- `⟨B,C⟩ U Γ ⭢h B U C Γ`. -/
theorem headStep_pairT_apps {B C U : Term String} (hB : LC B) (hC : LC C) (hU : LC U)
    (Γ : List (Term String)) (hΓ : ∀ t ∈ Γ, LC t) :
    HeadStep (multiApp (pairT B C) (U :: Γ)) (multiApp B (U :: C :: Γ)) :=
  headStep_apps (headStep_pairT hB hC hU) (by rintro ⟨⟩) Γ hΓ


end Term

end LambdaCalculus.LocallyNameless.Untyped

end Cslib
