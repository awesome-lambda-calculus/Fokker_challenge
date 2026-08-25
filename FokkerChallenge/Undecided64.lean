import FokkerChallenge.Decider.RigidHead
import FokkerChallenge.Decider.TailNotVar
import FokkerChallenge.DBNotation

/-!
# The terms of `undecided_terms.json`

This file collects the list of the 64 terms of `undecided_terms.json` and
applies the two deciders `FokkerChallenge.Decider.RigidHead` (rigid-headed
terms) and `FokkerChallenge.Decider.TailNotVar` (tail-applied terms) to them.

50 of the 64 terms are covered by these two deciders and are therefore proved
not to be one-point bases (`undecided_covered_not_basis`, together with
`undecided_covered_count`).  The remaining 14 terms are listed in
`undecidedTermsRemaining`; they are not settled by this development.
-/

set_option maxRecDepth 10000

namespace Cslib
namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- The 64 terms of `undecided_terms.json`. -/
def undecidedTerms : List (Term String) :=
[ db! "λλλλ0(1(02))"
, db! "λλλλ0(1(20))"
, db! "λλλλ0(2(01))"
, db! "λλλλ0(2(10))"
, db! "λλλλ0(012)"
, db! "λλλλ0(102)"
, db! "λλλλ0(021)"
, db! "λλλλ0(201)"
, db! "λλλλ1(0(02))"
, db! "λλλλ1(0(20))"
, db! "λλλλ1(2(00))"
, db! "λλλλ1(002)"
, db! "λλλλ1(020)"
, db! "λλλλ1(200)"
, db! "λλλλ2(0(01))"
, db! "λλλλ2(0(10))"
, db! "λλλλ2(1(00))"
, db! "λλλλ2(001)"
, db! "λλλλ2(010)"
, db! "λλλλ2(100)"
, db! "λλλλ01(02)"
, db! "λλλλ01(20)"
, db! "λλλλ10(02)"
, db! "λλλλ10(20)"
, db! "λλλλ02(01)"
, db! "λλλλ02(10)"
, db! "λλλλ20(01)"
, db! "λλλλ20(10)"
, db! "λλλλ0(01)2"
, db! "λλλλ0(10)2"
, db! "λλλλ1(00)2"
, db! "λλλλ0012"
, db! "λλλλ0102"
, db! "λλλλ1002"
, db! "λλλλ0(02)1"
, db! "λλλλ0(20)1"
, db! "λλλλ2(00)1"
, db! "λλλλ0021"
, db! "λλλλ0201"
, db! "λλλλ2001"
, db! "λλλλ1(02)0"
, db! "λλλλ1(20)0"
, db! "λλλλ2(01)0"
, db! "λλλλ2(10)0"
, db! "λλλλ0120"
, db! "λλλλ1020"
, db! "λλλλ0210"
, db! "λλλλ2010"
, db! "λλλ0(λ1(02))"
, db! "λλλ0(λ1(20))"
, db! "λλλ0(λ2(01))"
, db! "λλλ0(λ2(10))"
, db! "λλλ0(λ012)"
, db! "λλλ0(λ102)"
, db! "λλλ0(λ021)"
, db! "λλλ0(λ201)"
, db! "λλ0(λλ1(02))"
, db! "λλ0(λλ1(20))"
, db! "λλ0(λλ2(01))"
, db! "λλ0(λλ2(10))"
, db! "λλ0(λλ012)"
, db! "λλ0(λλ102)"
, db! "λλ0(λλ021)"
, db! "λλ0(λλ201)"
]


theorem undecidedTerms_length : undecidedTerms.length = 64 := by rfl

/-- A term is *covered* if one of the two deciders of this development applies
to it. -/
def covered (t : Term String) : Bool := rigid t || tailOk t

/-- A covered term is not a one-point basis. -/
theorem covered_not_basis {t : Term String} (h : covered t) : not_basis t := by
  rw [covered, Bool.or_eq_true] at h
  rcases h with h | h
  · exact rigid_not_basis h
  · exact tailOk_not_basis h

/-- **Every covered term of `undecided_terms.json` is not a one-point basis.** -/
theorem undecided_covered_not_basis :
    ∀ t ∈ undecidedTerms, covered t = true → not_basis t :=
  fun _ _ h => covered_not_basis h

/-- **50 of the 64 terms of `undecided_terms.json` are covered**, hence proved
not to be one-point bases by `undecided_covered_not_basis`. -/
theorem undecided_covered_count : (undecidedTerms.filter covered).length = 50 := by rfl

/-- The 14 terms of `undecided_terms.json` that neither `rigid` nor `tailOk`
covers.  Each of them has an abstraction block `λ … λ. z M₁ … M_k` whose last
argument `M_k` is a bound variable and whose head `z` is not the innermost
binder, so both deciders fail; whether they are one-point bases is left open by
this development. -/
def undecidedTermsRemaining : List (Term String) :=
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

/-- There are exactly 14 terms of `undecided_terms.json` that are not covered;
they are the ones listed in `undecidedTermsRemaining`. -/
theorem undecidedTermsRemaining_length :
    (undecidedTerms.filter (fun t => !covered t)).length
      = undecidedTermsRemaining.length := by rfl

end Term
end LambdaCalculus.LocallyNameless.Untyped
end Cslib
