import FokkerChallenge.Basic
import FokkerChallenge.EnhancedCslib.GenFinset
import FokkerChallenge.BLC.BLCTotal
import FokkerChallenge.NativeEnum

/-!
# Comparator challenge file

This file states the two headline results of the development as *unproven*
theorems, for use with [Comparator](https://github.com/leanprover/comparator), a
checker that verifies that a `Solution` module really proves the statements of a
`Challenge` module, using no more than a fixed list of axioms.

## What the statements are made of

Everything the statements below are phrased in terms of comes from modules that
contain **definitions only**:

* `Cslib.LambdaCalculus.LocallyNameless.Untyped.Term`, `.LC`, `.fv` — the
  locally nameless untyped λ-terms of `cslib`;
* `Term.fokker_size` (`FokkerChallenge/Basic.lean`) — the number of abstractions
  and applications of a term;
* `Term.blcT` (`FokkerChallenge/BLC/BLCTotal.lean`) — Tromp's binary lambda
  calculus encoding, as a total function;
* `Term.not_basis` (`FokkerChallenge/EnhancedCslib/GenFinset.lean`) — there is a
  closed, locally closed term `y` such that no applicative combination of the
  given term βη-reduces to `y`; in particular the term is not a one-point basis.

A reader who wants to know what is being claimed only has to read those
definitions.  The proof lives in `Solution.lean` and in the `FokkerChallenge`
library.

## Why `FokkerChallenge.NativeEnum` is imported here

The proofs use `native_decide` in exactly two places, the sweeps of the two
finite search spaces, isolated in `FokkerChallenge/NativeEnum.lean`.  Each such
use creates an axiom of the form `decide <explicit proposition> = true`, and
Comparator requires every permitted axiom to be present, with the same type, in
the challenge environment as well.  Importing `FokkerChallenge.NativeEnum` is
what makes the two axioms listed in `comparator-config.json` available here; the
axioms' types mention definitions only, so they can be read off directly.

See `COMPARATOR.md` for how to run the check.
-/

open Cslib.LambdaCalculus.LocallyNameless.Untyped
open Cslib.LambdaCalculus.LocallyNameless.Untyped.Term

/-- Every closed, locally closed λ-term of Fokker size at most `6` fails to be a
one-point basis. -/
theorem fokker_challenge_size_lt_7 (M : Term String)
    (hm : M.LC ∧ M.fv = ∅ ∧ M.fokker_size < 7) : not_basis M := by
  sorry

/-- Every closed, locally closed λ-term whose binary lambda calculus code is
shorter than `26` bits fails to be a one-point basis. -/
theorem fokker_challenge_blc_lt_26 (M : Term String)
    (hm : M.fv = ∅ ∧ M.blcT.length < 26) (h_lc : M.LC) : not_basis M := by
  sorry
