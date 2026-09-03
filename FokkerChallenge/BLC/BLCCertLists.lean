import FokkerChallenge.DBNotation

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

set_option maxRecDepth 100000

/-- The certificates for all 402 terms of `undecided_terms.json`. -/
def fokkerUndecidedCerts : List (Term String × List (Term String)) :=
  [
    (db! "λλλ0(λ120)", [db! "λλλ0((λλ10)(01))", db! "λλλ0(λ120)"])
  , (db! "λλλ0(λ210)", [db! "λλλ0((λλ10)(10))", db! "λλλ0(λ210)"])
  , (db! "λλ(λλ120)0", [db! "λλ(λ(λλ10)(01))0", db! "λλ(λλ120)0"])
  , (db! "λλ0(λλ120)", [db! "λλ0(λ(λλ10)(01))", db! "λλ0(λλ120)"])
  , (db! "λλλ(λ120)0", [db! "λλλ(λλ10)(01)0", db! "λλλ(λ120)0"])
  , (db! "λλλ(λ210)0", [db! "λλλ(λλ10)(10)0", db! "λλλ(λ210)0"])
  , (db! "λλ0(λλ210)", [db! "λλ0(λ(λλ10)(10))", db! "λλ0(λλ210)"])
  , (db! "λλ(λλ210)0", [db! "λλ(λ(λλ10)(10))0", db! "λλ(λλ210)0"])
   ]

/-- The 402 terms of `undecided_terms.json`. -/
def fokkerUndecidedTerms : List (Term String) := fokkerUndecidedCerts.map Prod.fst

/-- Certificates: for each term, a chain of βη-steps ending in a term that is
nameable with the two names `x`, `y`.  A single β-step suffices in each case. -/
def fokkerUpdatedOpenCerts : List (Term String × List (Term String)) :=
  [ (db! "λλλ(λ012)0",   [db! "λλλ(λ012)0",   db! "λλλ001"])
  , (db! "λλλ(λ102)0",   [db! "λλλ(λ102)0",   db! "λλλ001"])
  , (db! "λλλ(λ021)0",   [db! "λλλ(λ021)0",   db! "λλλ010"])
  , (db! "λλλ(λ201)0",   [db! "λλλ(λ201)0",   db! "λλλ100"])
  , (db! "λλ(λλ012)0",   [db! "λλ(λλ012)0",   db! "λλλ011"])
  , (db! "λλ(λλ102)0",   [db! "λλ(λλ102)0",   db! "λλλ101"])
  , (db! "λλ(λλ021)0",   [db! "λλ(λλ021)0",   db! "λλλ011"])
  , (db! "λλ(λλ201)0",   [db! "λλ(λλ201)0",   db! "λλλ101"])
  ]

/-- The 16 terms of `fokkerUpdatedOpen` that βη-reduce to a nameable term. -/
def fokkerUpdatedOpenReduces : List (Term String) := fokkerUpdatedOpenCerts.map Prod.fst

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
