import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.EtaPostpone
import FokkerChallenge.EnhancedCslib.EtaToSpine
import FokkerChallenge.EnhancedCslib.EtaSpineShape

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-!
# Iterated opening of the appended arguments exposes a free variable

The shape theorem `betaNF_etaStar_shape_len_one` produces an appended argument
list `E` with

```
∀ B ∈ E, ∃ k < n, HasBvar k B ∧ ¬ LC B
```

i.e. every entry of `E` has a dangling bound variable of index `< n`, coming
from one of the `n` enclosing abstractions.

This file shows the expected consequence: if one *opens* such a term with the
`n` enclosing abstractions, i.e. performs

```
openRec 0 (fvar y) (openRec 1 (fvar y) (… (openRec (n-1) (fvar y) B) …))
```

(the iteration `openDown n (fvar y)`, applying `openRec (n-1)`, `openRec (n-2)`,
…, `openRec 0` in that order), then the free variable `y` really shows up:
`y ∈ fv (openDown n (fvar y) B)`.
-/


universe u

open Term

variable {Var : Type u}

/-! ## The iterated opening operator -/

/-- `openDown n u t` opens `t` successively at the indices `n-1, n-2, …, 0`,
each time with `u`.  This is the operation performed when the `n` enclosing
abstractions of `absN n t` are opened one after the other, from the innermost
index `n-1` down to the outermost index `0`. -/
@[simp, scoped grind]
def openDown : ℕ → Term Var → Term Var → Term Var
  | 0, _, t => t
  | (n + 1), u, t => openDown n u (openRec n u t)

@[simp] theorem openDown_zero (u t : Term Var) : openDown 0 u t = t := rfl

@[simp] theorem openDown_succ (n : ℕ) (u t : Term Var) :
    openDown (n + 1) u t = openDown n u (openRec n u t) := rfl

theorem openDown_lc [HasFresh Var] {i y} {M : Term Var} (h_lc : M.LC) :
  openDown i y M = M := by induction i with grind

theorem openDown_fvar {i y} {x : Var} : openDown i y (fvar x) = fvar x := by
  induction i <;> grind

theorem openDown_app {i y} {M N : Term Var} : openDown i y (M.app N) = (openDown i y M).app (openDown i y N) := by
  induction i generalizing M N with
  | zero => grind
  | succ n ih =>  unfold openDown
                  rw [openRec_app, ih]

theorem openDown_multiapp {i y M} {l : List (Term Var)} :
  openDown i y (l.foldl app M) =
  (l.map (openDown i y)).foldl app (openDown i y M) := by
  induction l generalizing M with
  | nil => grind
  | cons head tail ih =>  simp
                          rw [@ih (M.app head), openDown_app]

variable  [DecidableEq Var]

/-! ## Free variables survive opening -/

/-- Opening at an index never removes a free variable, so a free variable of `t`
is still free after the whole iteration `openDown n u`. -/
theorem mem_fv_openDown_of_mem_fv {y : Var} :
    ∀ (n : ℕ) (u t : Term Var), y ∈ fv t → y ∈ fv (openDown n u t) := by
  intro n
  induction n with
  | zero => intro u t h; simpa using h
  | succ m ih =>
      intro u t h
      exact ih u (openRec m u t) (by grind[open_preserve_not_fvar])


/-! ## The main statement -/

/-- **Iterated opening of a term with a dangling index `< n` exposes the
variable.**  If `HasBvar k B` for some `k < n`, then opening `B` at the indices
`n-1, n-2, …, 0` with `fvar y` produces a term in which `y` occurs free. -/
theorem mem_fv_openDown_of_hasBvar {n k : ℕ} {B : Term Var}
    (hk : k < n) (h : HasBvar k B) (y : Var) : y ∈ fv (openDown n (fvar y) B) := by
  induction n generalizing B with
  | zero => omega
  | succ m ih =>
      rw [openDown_succ]
      rcases Nat.lt_or_ge k m with hkm | hkm
      · exact ih hkm (hasBvar_openRec_of_ne (by omega) h)
      · have hkm' : k = m := by omega
        subst hkm'
        exact mem_fv_openDown_of_mem_fv _ (fvar y) _ (mem_fv_openRec_of_hasBvar y h)

/-- The statement in the form supplied by the shape theorem: if every entry `B`
of the appended argument list `E` has a dangling bound variable of index `< n`
(and hence is not locally closed), then after opening all `n` enclosing
abstractions with the same free variable `y`, every entry contains `y` free. -/
theorem mem_fv_openDown_of_forall_hasBvar {n : ℕ} {E : List (Term Var)}
    (hE : ∀ B ∈ E, ∃ k < n, HasBvar k B ∧ ¬ LC B) (y : Var) :
    ∀ B ∈ E, y ∈ fv (openDown n (fvar y) B) := by
  intro B hB
  obtain ⟨k, hk, hkB, _⟩ := hE B hB
  exact mem_fv_openDown_of_hasBvar hk hkB y

variable  [HasFresh Var]

/-- Combined with the shape theorem: for a locally closed β-normal `M` with
`M ↠ηᶠ x N`, the appended arguments `E` of `M = absN n (x A E₁ … E_n)` all
contain the variable `y` free once the `n` enclosing abstractions have been
opened with `fvar y`. -/
theorem betaNF_etaStar_shape_len_one_openDown_fv {M N : Term Var} {x : Var}
    (hlc : LC M) (hM : Relation.Normal FullBeta M) (steps : M ↠ηᶠ (app (fvar x) N)) :
    ∃ (n : ℕ) (A : Term Var) (E : List (Term Var)),
      M = abs^[n] ((A :: E).foldl app (fvar x)) ∧ LC A ∧ A ↠ηᶠ N ∧
        E.length = n ∧ EtaExpArgs n E ∧ (∀ B ∈ E, ∃ k < n, HasBvar k B ∧ ¬ LC B) ∧
        ∀ (y : Var), ∀ B ∈ E, y ∈ fv (openDown n (fvar y) B) := by
  obtain ⟨n, A, E, hEq, hA, hAN, hlen, hE, hdangling⟩ :=
    betaNF_etaStar_shape_len_one hlc hM steps
  exact ⟨n, A, E, hEq, hA, hAN, hlen, hE, hdangling,
    fun y => mem_fv_openDown_of_forall_hasBvar hdangling y⟩
