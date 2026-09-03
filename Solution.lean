import FokkerChallenge.FokkerResolved
import FokkerChallenge.BLC.BLCResolved

/-!
# Comparator solution file

Proofs of the two statements of `Challenge.lean`, obtained from the two headline
theorems of the development:

* `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.not_basis_of_closed_lc_small_fokker_size`
  (`FokkerChallenge/FokkerResolved.lean`)
* `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.not_basis_of_closed_lc_small_blc`
  (`FokkerChallenge/BLC/BLCResolved.lean`)

Both use `native_decide` for the enumeration of the search space, so besides
`propext`, `Classical.choice` and `Quot.sound` they depend on `Lean.ofReduceBool`
(and on the compiler-generated `native_decide` axioms of the two enumeration
lemmas).
-/

open Cslib.LambdaCalculus.LocallyNameless.Untyped
open Cslib.LambdaCalculus.LocallyNameless.Untyped.Term

/-- Every closed, locally closed λ-term of Fokker size at most `6` fails to be a
one-point basis. -/
theorem fokker_challenge_size_lt_7 (M : Term String)
    (hm : M.LC ∧ M.fv = ∅ ∧ M.fokker_size < 7) : not_basis M :=
  not_basis_of_closed_lc_small_fokker_size M hm

/-- Every closed, locally closed λ-term whose binary lambda calculus code is
shorter than `26` bits fails to be a one-point basis. -/
theorem fokker_challenge_blc_lt_26 (M : Term String)
    (hm : M.fv = ∅ ∧ M.blcT.length < 26) (h_lc : M.LC) : not_basis M :=
  not_basis_of_closed_lc_small_blc M hm h_lc
