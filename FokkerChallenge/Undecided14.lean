import FokkerChallenge.Decider.ProperCombinator
import FokkerChallenge.Decider.RigidHead
import FokkerChallenge.Decider.TailNotVar
import FokkerChallenge.DBNotation

/-!
# Craig's decider on the 14 terms of `undecided_terms.json`

`FokkerChallenge.Undecided64` applies the deciders `rigid` and `tailOk` to the
64 terms of the original `undecided_terms.json`, leaving 14 terms open.  Those
14 terms are the current content of `undecided_terms.json` and are collected
here as `undecidedTerms14`.

This file applies `craigOk` (`FokkerChallenge.Decider.ProperCombinator`), the
decider extracted from Bellot's proof of Craig's theorem, to them.  Six of the
fourteen are accepted and are therefore proved not to be one-point bases
(`undecided14_craigOk_not_basis` with `undecided14_craigOk_count`); the other
eight are listed in `undecidedTerms14Remaining` and are left open.
-/

set_option maxRecDepth 10000

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- The 14 terms of the current `undecided_terms.json`, i.e. the terms of
`undecidedTerms` that neither `rigid` nor `tailOk` covers. -/
def undecidedTerms14 : List (Term String) :=
[ db! "λλλλ1(00)2"
, db! "λλλλ1002"
, db! "λλλλ2(00)1"
, db! "λλλλ2001"
, db! "λλλλ1(02)0"
, db! "λλλλ1(20)0"
, db! "λλλλ2(01)0"
, db! "λλλλ2(10)0"
, db! "λλλλ1020"
, db! "λλλλ2010"
, db! "λλλ0(λ102)"
, db! "λλλ0(λ201)"
, db! "λλ0(λλ102)"
, db! "λλ0(λλ201)"
]

theorem undecidedTerms14_length : undecidedTerms14.length = 14 := by rfl

/-- **Every term of the current `undecided_terms.json` accepted by Craig's
decider is not a one-point basis.** -/
theorem undecided14_craigOk_not_basis :
    ∀ t ∈ undecidedTerms14, craigOk t = true → not_basis t :=
  fun _ _ h => craigOk_not_basis h

/-- **Six of the fourteen remaining terms are accepted by `craigOk`**, hence
proved not to be one-point bases by `undecided14_craigOk_not_basis`. -/
theorem undecided14_craigOk_count :
    (undecidedTerms14.filter craigOk).length = 6 := by rfl

/-- All fourteen terms of the current `undecided_terms.json` are `λ`-terms of
the form `λ a. R` with `R` closed, so none of them is caught by any of the
earlier deciders. -/
theorem undecided14_not_covered :
    (undecidedTerms14.filter (fun t => rigid t || tailOk t)).length = 0 := by rfl

/-- The eight terms of the current `undecided_terms.json` that `craigOk` does
not accept.  The first four are proper combinators that both erase and
duplicate a binder while all the arguments of their body are variables — the
case of Bellot's Lemma 1 that has no direct λ-calculus counterpart here — and
the last four are not proper combinators at all (their body contains an
abstraction whose own body has only variable arguments).  Whether they are
one-point bases is left open by this development. -/
def undecidedTerms14Remaining : List (Term String) :=
[ db! "λλλλ1002"
, db! "λλλλ2001"
, db! "λλλλ1020"
, db! "λλλλ2010"
, db! "λλλ0(λ102)"
, db! "λλλ0(λ201)"
, db! "λλ0(λλ102)"
, db! "λλ0(λλ201)"
]

/-- There are exactly eight terms of the current `undecided_terms.json` that
`craigOk` leaves open; they are the ones listed in
`undecidedTerms14Remaining`. -/
theorem undecidedTerms14Remaining_length :
    (undecidedTerms14.filter (fun t => !craigOk t)).length
      = undecidedTerms14Remaining.length := by rfl

/-- The first four terms left open are proper combinators; the last four are
not. -/
theorem undecidedTerms14Remaining_properCombinator_count :
    (undecidedTerms14Remaining.filter properCombinator).length = 4 := by rfl

end Term

end LambdaCalculus.LocallyNameless.Untyped

end Cslib
