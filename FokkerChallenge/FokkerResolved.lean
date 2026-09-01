import FokkerChallenge.BetaNamableClosure
import FokkerChallenge.LiftSearch
import FokkerChallenge.GenTerms
import FokkerChallenge.FokkerCerts1
import FokkerChallenge.FokkerCerts2
import FokkerChallenge.FokkerCerts3
import FokkerChallenge.FokkerCerts4
import FokkerChallenge.FokkerCerts5
import FokkerChallenge.FokkerCerts6
import FokkerChallenge.FokkerCerts7
import FokkerChallenge.FokkerCerts8
import FokkerChallenge.FokkerCerts9
import FokkerChallenge.Decider.NoDuplicate
import FokkerChallenge.Decider.EveryBvarUsed
import FokkerChallenge.Decider.OnlyOneVarUsed
import FokkerChallenge.Decider.ArgNotVar
import FokkerChallenge.Decider.RigidHead
import FokkerChallenge.Decider.TailNotVar
import FokkerChallenge.TwoVarsAreNotEnough.Final

/-!
# The undecided terms of the Fokker challenge are β-reducts of nameable terms

`undecided_terms.json` of the `awesome-lambda-calculus/Fokker_challenge`
collection lists 402 closed λ-terms whose status as a one-point basis was still
open.  None of them is nameable with only the two variable names `x` and `y`
(`fokkerUndecided_not_namableXY`).  Nevertheless **every one of them is a
β-reduct of a term that is nameable with two names**
(`fokkerUndecided_betaReductOfNamable`).

The certificates were found by the lift search of `FokkerChallenge.LiftSearch`
(at most two lift β-expansions per term) and are checked by the kernel in
`FokkerChallenge.FokkerCerts1`–`FokkerCerts4`.

Combined with a "two variables are not enough" statement — the existence of a
closed term that is not β-convertible to any term nameable with two names, which
is *assumed*, not proved, here — this shows that none of the 402 terms is a
one-point basis (`fokkerUndecided_not_onePointBasis`).
-/

set_option maxRecDepth 100000

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term


/-- The certificates for all 402 terms of `undecided_terms.json`. -/
def fokkerUndecidedCerts : List (Term String × List (Term String)) :=
  fokkerCerts1 ++ fokkerCerts2 ++ fokkerCerts3 ++ fokkerCerts4 ++
  fokkerCerts5 ++ fokkerCerts6 ++ fokkerCerts7 ++ fokkerCerts8 ++
  fokkerCerts9

/-- The 402 terms of `undecided_terms.json`. -/
def fokkerUndecidedTerms : List (Term String) := fokkerUndecidedCerts.map Prod.fst

/-
theorem fokkerUndecidedTerms_length : fokkerUndecidedTerms.length = 402 := by
  simp only [fokkerUndecidedTerms, fokkerUndecidedCerts, List.length_map, List.length_append]
  rfl
-/

theorem fokkerUndecidedCerts_ok : entriesOK fokkerUndecidedCerts = true := by
  rw [fokkerUndecidedCerts,
    entriesOK_append, entriesOK_append, entriesOK_append, entriesOK_append,
    entriesOK_append, entriesOK_append, entriesOK_append, entriesOK_append,
    fokkerCerts1_ok, fokkerCerts2_ok, fokkerCerts3_ok, fokkerCerts4_ok,
    fokkerCerts5_ok, fokkerCerts6_ok, fokkerCerts7_ok, fokkerCerts8_ok, fokkerCerts9_ok]
  rfl

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

/-- The search is only a *semi*-decision procedure: it may fail.  For the
combinator `S = λλλ 2 0 (1 0)` no chain of at most two lift β-expansions is
nameable with two names — as it must be, since by Statman's theorem `S` is not
β-convertible to any two-name term. -/
theorem liftSearch_sComb_eq_none : liftSearch 2 (db! "λλλ20(10)") = none := by
  decide

/-- **Consequence for the one-point basis question.**  Assume `U` is a closed term
that is not β-convertible to any term nameable with the two names `x`, `y`
(this is Statman's *two variables are not enough*, which is assumed here).  Then
for every term `A` of `undecided_terms.json`, no applicative combination of `A`
is β-convertible to `U`; in particular no such `A` is a one-point basis. -/
theorem fokkerUndecided_not_onePointBasis
    {U : Term String} (hU : ∀ S, namableXY S = true → ¬ BetaConv S U) :
    ∀ A ∈ fokkerUndecidedTerms, ∀ C, ClosedUnderApp (fun t => t = A) C → ¬ BetaConv C U :=
  fun A hA _ hC =>
    not_betaConv_of_betaReductOfNamable (fokkerUndecided_betaReductOfNamable A hA) hU hC

theorem mem_terms_fokker_lt_7_iff (M : Term String)
  (hm : M ∈ terms_fokker_lt_7) :
  M.every_bvar_used \/ M.no_duplicate \/ M.isNamedOfXY \/ M.tailOk \/ M.rigid \/ M.argOk \/ M ∈ fokkerUndecidedTerms := by
     native_decide +revert

theorem not_basis_of_closed_lc_small_fokker_size (M : Term String)
    (hm : M.LC ∧ M.fv = ∅ ∧ M.fokker_size < 7) : not_basis M := by
    rw [closed_lc_iff_mem_gen_terms] at hm
    apply mem_terms_fokker_lt_7_iff at hm
    rcases hm with h|h|h|h|h|h|h
    . exact not_reaches_K h
    . exact not_reaches_omega h
    . exact isNamedOfXY_not_basis h
    . exact tailOk_not_basis h
    . exact rigid_not_basis h
    . exact argOk_not_basis h
    . exact BetaReductOfNamable_not_basis (fokkerUndecided_betaReductOfNamable  _ h)
