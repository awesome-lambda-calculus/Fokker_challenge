import FokkerChallenge.DBNotation
import FokkerChallenge.Decider.TwoVarsPerNode

/-!
# The certificate lists of the BLC classification

The two explicit lists of certificates used by the binary-lambda-calculus
classification, kept in a module of their own so that they can be imported
without any of the proofs.  This is what lets the statement of the enumeration
lemma `mem_terms_blc_lt_26_iff` (in `FokkerChallenge.NativeEnum`) be phrased in
terms of definitions only.

The theorems checking that the certificates are correct live in
`FokkerChallenge.BLC.BLCResolved`.
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

def fokkerUndecidedCerts : List (Term String × List (Term String)) :=
  [
    (db! "λλλ0(λ120)", [db! "λλλ0((λλ10)(01))", db! "λλλ0(λ120)"])
  , (db! "λλλ0(λ210)", [db! "λλλ0((λλ10)(10))", db! "λλλ0(λ210)"])
  , (db! "λλ0(λλ120)", [db! "λλ0(λ(λλ10)(01))", db! "λλ0(λλ120)"])
  , (db! "λλ0(λλ210)", [db! "λλ0(λ(λλ10)(10))", db! "λλ0(λλ210)"])
   ]

/-- The 402 terms of `undecided_terms.json`. -/
def fokkerUndecidedTerms : List (Term String) := fokkerUndecidedCerts.map Prod.fst

theorem fokkerUndecidedCerts_ok : entriesOK fokkerUndecidedCerts = true := by decide

/-- **Every term of `undecided_terms.json` is a β-reduct of a term that can be
named with the two variable names `x` and `y`.** -/
theorem fokkerUndecided_betaReductOfNamable :
    ∀ T ∈ fokkerUndecidedTerms, BetaReductOfNamable T :=
  betaReductOfNamable_of_entriesOK fokkerUndecidedCerts_ok

/-- In particular all of them are locally closed. -/
theorem fokkerUndecided_lc : ∀ T ∈ fokkerUndecidedTerms, LC T :=
  fun T hT => (fokkerUndecided_betaReductOfNamable T hT).lc

/-- None of these terms is itself nameable with two names, so the classical
"two variables are not enough" test does not apply to any of them directly. -/
theorem fokkerUndecided_not_namableXY : ∀ T ∈ fokkerUndecidedTerms, namableXY T = false := by
  decide

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
