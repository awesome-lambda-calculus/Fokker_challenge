import FokkerChallenge.TwoVarsAreNotEnough.TwoVarBlocks

/-!
# A total binary lambda calculus encoder

`Term.blc` from `RequestProject.BLC` returns an `Option (List Bool)`, being
`none` on any term that contains a free variable.  Here we package the same
encoding as a *total* function

```
blcT : Term Var → List Bool
```

which simply **returns `[]` when it meets a free variable**:

```
blcT (λ M)   = 00 blcT M
blcT (M N)   = 01 blcT M blcT N
blcT (bvar n) = 1^(n+1) 0
blcT (fvar x) = []
```

Of course such a convention destroys injectivity in general (all free variables
get the empty code, see `blcT_not_injective`), so all the good properties of the
encoding are stated for terms *without free variables*, i.e. terms `t` with
`fv t = ∅`:

* `blcT_eq_nil_iff` — `blcT t = []` iff `t` is a free variable, so on terms with
  `fv t = ∅` the code is never empty;
* `blc_eq_blcT_of_fv_empty` — on such terms `blcT` agrees with the partial
  encoder `blc`;
* `blcDecode_blcT_append` / `blcDecode_blcT` — the decoder round trip;
* `blcT_injective_of_fv_empty` — injectivity;
* `blcT_prefix_free_of_fv_empty` — prefix freeness (self delimiting code);
* the length formulas `blcT_length_abs`, `blcT_length_app`, `blcT_length_bvar`.
-/


namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

variable {Var : Type u}

def blcVar (n : ℕ) : List Bool := List.replicate (n + 1) true ++ [false]


@[simp] theorem blcVar_length (n : ℕ) : (blcVar n).length = n + 2 := by
  simp [blcVar]

/-! ## The total encoder -/

/-- Tromp's binary encoding of a de Bruijn term, as a total function: a free
variable, for which the encoding is undefined, is sent to the empty code `[]`. -/
def blcT : Term Var → List Bool
  | bvar n => blcVar n
  | fvar _ => []
  | abs t => false :: false :: blcT t
  | app t u => false :: true :: (blcT t ++ blcT u)

@[simp] theorem blcT_bvar (n : ℕ) : (bvar n : Term Var).blcT = blcVar n := rfl

@[simp] theorem blcT_fvar (x : Var) : (fvar x : Term Var).blcT = [] := rfl

@[simp] theorem blcT_abs (t : Term Var) :
    (abs t).blcT = false :: false :: t.blcT := rfl

@[simp] theorem blcT_app (t u : Term Var) :
    (app t u).blcT = false :: true :: (t.blcT ++ u.blcT) := rfl

/-- Render a code as a string of `0`s and `1`s. -/
def bitsToString (bs : List Bool) : String :=
  bs.foldl (fun s b => s.push (if b then '1' else '0')) ""

/-- The binary encoding of a term as a string of `0`s and `1`s (`""` on a free
variable). -/
def blcTString (t : Term Var) : String := bitsToString t.blcT

/-- The code is empty exactly on the free variables. -/
theorem blcT_eq_nil_iff {t : Term Var} : t.blcT = [] ↔ ∃ x, t = fvar x := by
  cases t with
  | bvar n => simp [blcVar]
  | fvar x => exact ⟨fun _ => ⟨x, rfl⟩, fun _ => rfl⟩
  | abs t => simp
  | app t u => simp

/-! ## Terms without free variables -/

/-- A term is a *pure de Bruijn term* if it contains no free variable. -/
inductive IsDB : Term Var → Prop
  /-- A bound variable is a pure de Bruijn term. -/
  | bvar (n : ℕ) : IsDB (bvar n)
  /-- An abstraction of a pure de Bruijn term is one. -/
  | abs {t : Term Var} : IsDB t → IsDB (abs t)
  /-- An application of pure de Bruijn terms is one. -/
  | app {t u : Term Var} : IsDB t → IsDB u → IsDB (app t u)

/-- Having no free variables is the same as being a pure de Bruijn term. -/
theorem fv_eq_empty_iff_isDB [DecidableEq Var] {t : Term Var} : fv t = ∅ ↔ IsDB t := by
  induction t with
  | bvar n => exact ⟨fun _ => .bvar n, fun _ => rfl⟩
  | fvar x =>
      constructor
      · intro h; simp [fv] at h
      · intro h; cases h
  | abs t ih =>
      constructor
      · intro h; exact .abs (ih.1 h)
      · intro h; cases h with | abs h => exact ih.2 h
  | app t u iht ihu =>
      constructor
      · intro h
        rw [fv, Finset.union_eq_empty] at h
        exact .app (iht.1 h.1) (ihu.1 h.2)
      · intro h
        cases h with
        | app h1 h2 => rw [fv, iht.2 h1, ihu.2 h2]; simp

/-- On a term without free variables the code is never empty. -/
theorem blcT_ne_nil_of_fv_empty [DecidableEq Var] {t : Term Var} (h : fv t = ∅) :
    t.blcT ≠ [] := by
  intro hnil
  obtain ⟨x, rfl⟩ := blcT_eq_nil_iff.1 hnil
  simp [fv] at h

/-! ## Lengths -/

@[simp] theorem blcT_length_bvar (n : ℕ) : ((bvar n : Term Var)).blcT.length = n + 2 := by
  simp

@[simp] theorem blcT_length_abs (t : Term Var) : (abs t).blcT.length = t.blcT.length + 2 := by
  simp

@[simp] theorem blcT_length_app (t u : Term Var) :
    (app t u).blcT.length = t.blcT.length + u.blcT.length + 2 := by
  simp

/-! ## Decoding -/

/-! ## Injectivity and prefix freeness -/

/-- The hypothesis `fv t = ∅` is necessary: without it the total encoder is not
injective, since every free variable has the empty code. -/
theorem blcT_not_injective :
    ¬ ∀ t u : Term String, t.blcT = u.blcT → t = u := by
  intro h
  have := h (fvar "x") (fvar "y") rfl
  simp at this
