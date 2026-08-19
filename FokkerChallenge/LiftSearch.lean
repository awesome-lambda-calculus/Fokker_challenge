import FokkerChallenge.TwoVarsAreNotEnough.Nameable
import FokkerChallenge.DeBruijnParse
import FokkerChallenge.BetaCheck

/-!
# Searching for a two-name-nameable β-expansion

A closed term `T` may fail to be nameable with the two variable names `x`, `y`
and still be a β-reduct of a nameable term: contracting a β-redex can move a
subterm *inwards*, under additional binders, and that is precisely what creates
the naming conflicts (see `FokkerChallenge.BetaNameable`).

The search implemented here inverts that phenomenon.  A **lift** is the
β-expansion

```
C[λp. B[M]]   ⟵β   C[(λu. λp. B[u]) M]
```

which is legal whenever the subterm `M` does not use the binder `p` nor any
binder of `B` above the hole; it moves `M` one binder further out, and replaces
it, at its old (deep) position, by a single variable occurrence.  Deep
occurrences inside `M` are what generate long chains of naming constraints, so
lifting tends to make a term nameable.

`liftSearch depth T` performs a breadth-first search over at most `depth`
successive lifts and returns, on success, the whole β-reduction chain
`S ⭢βᶠ … ⭢βᶠ T` whose first element `S` satisfies `namableXY S = true`.

Nothing in this file is trusted: the chains it produces are certified
afterwards by `FokkerChallenge.BetaCheck.chainCheck`.
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

open Term

/-! ## de Bruijn manipulation -/

/-- Shift the free de Bruijn indices (those `≥ c`) of `t` by `delta`. -/
def dbShift (delta : Int) : ℕ → Term String → Term String
  | c, .bvar i => if c ≤ i then .bvar ((i + delta).toNat) else .bvar i
  | _, .fvar x => .fvar x
  | c, .abs t => .abs (dbShift delta (c + 1) t)
  | c, .app a b => .app (dbShift delta c a) (dbShift delta c b)

/-- `noIndexBelow d t` checks that every free de Bruijn index of `t` is `> d`. -/
def noIndexBelow : ℕ → Term String → Bool
  | d, .bvar i => decide (d < i)
  | _, .fvar _ => true
  | d, .abs t => noIndexBelow (d + 1) t
  | d, .app a b => noIndexBelow d a && noIndexBelow d b

/-- The marker standing for the hole of a one-hole context. -/
def holeName : String := "#h"

/-- Replace the hole marker by the index of the freshly created binder. -/
def fillHole : ℕ → Term String → Term String
  | _, .bvar i => .bvar i
  | d, .fvar x => if x = holeName then .bvar (d + 1) else .fvar x
  | d, .abs t => .abs (fillHole (d + 1) t)
  | d, .app a b => .app (fillHole d a) (fillHole d b)

/-- Is `t` worth lifting out of `d + 1` binders?  It must be a compound term
(lifting a single variable is useless) and it may not mention any of the `d + 1`
binders it would escape from. -/
def liftable (d : ℕ) : Term String → Bool
  | .bvar _ => false
  | .fvar _ => false
  | t => noIndexBelow d t

/-- All ways of digging a hole in `B` at a subterm that can be lifted out of the
enclosing binder: returns the context (with the hole marked by `holeName`) and
the lifted subterm, re-indexed for its new, shallower position. -/
def liftCands : ℕ → Term String → List (Term String × Term String)
  | d, t =>
    let here : List (Term String × Term String) :=
      if liftable d t then [(.fvar holeName, dbShift (-(d + 1 : ℕ)) 0 t)] else []
    let below : List (Term String × Term String) :=
      match t with
      | .abs b => (liftCands (d + 1) b).map (fun p => (.abs p.1, p.2))
      | .app a b =>
          (liftCands d a).map (fun p => (.app p.1 b, p.2)) ++
          (liftCands d b).map (fun p => (.app a p.1, p.2))
      | _ => []
    here ++ below

/-- All one-step lift β-expansions of `t`. -/
def allLifts : Term String → List (Term String)
  | .bvar _ => []
  | .fvar _ => []
  | .abs B =>
      (liftCands 0 B).map
        (fun p => .app (.abs (.abs (fillHole 0 (dbShift 1 1 p.1)))) p.2) ++
      (allLifts B).map Term.abs
  | .app a b =>
      (allLifts a).map (fun a' => .app a' b) ++ (allLifts b).map (fun b' => .app a b')

/-! ## The search -/

/-- One breadth-first layer: a candidate together with the reduction chain that
takes it back to the original term. -/
abbrev Chain := Term String × List (Term String)

/-- Breadth-first search through `depth` layers of lifts. -/
def liftBFS : ℕ → List Chain → Option (List (Term String))
  | 0, _ => none
  | _, [] => none
  | n + 1, cs =>
      match cs.find? (fun c => namableXY c.1) with
      | some c => some (c.1 :: c.2)
      | none => liftBFS n (cs.flatMap (fun c => (allLifts c.1).map (fun s => (s, c.1 :: c.2))))

/-- `liftSearch depth T` looks for a nameable β-expansion of `T` using at most
`depth` lifts.  On success it returns the reduction chain from the nameable term
found down to `T`. -/
def liftSearch (depth : ℕ) (T : Term String) : Option (List (Term String)) :=
  liftBFS (depth + 1) [(T, [])]

/-! ## The certified front end -/

/-- The complete procedure: search for a nameable β-expansion of `T` using at
most `depth` lifts and keep the answer only if the certificate checker accepts
it.  By `betaReductOfNamable_of_liftDecide`, a returned chain is a proof that
`T` is a β-reduct of a term nameable with the two names `x`, `y`. -/
def liftDecide (depth : ℕ) (T : Term String) : Option (List (Term String)) :=
  match liftSearch depth T with
  | some l => if certifies T l then some l else none
  | none => none

/-- **Soundness of the procedure.** -/
theorem betaReductOfNamable_of_liftDecide {depth : ℕ} {T : Term String}
    {l : List (Term String)} (h : liftDecide depth T = some l) : BetaReductOfNamable T := by
  simp only [liftDecide] at h
  split at h
  · rename_i l' _
    by_cases hc : certifies T l'
    · exact betaReductOfNamable_of_certifies hc
    · simp [hc] at h
  · simp at h

/-! ## Printing -/

/-- Print a term in de Bruijn notation (indices are assumed to be `< 10`). -/
def showDB : Term String → String
  | .bvar i => toString i
  | .fvar x => x
  | .abs t => "λ" ++ showDB t
  | .app a b =>
      let sa := match a with
        | .abs _ => "(" ++ showDB a ++ ")"
        | _ => showDB a
      let sb := match b with
        | .bvar _ => showDB b
        | .fvar _ => showDB b
        | _ => "(" ++ showDB b ++ ")"
      sa ++ sb

