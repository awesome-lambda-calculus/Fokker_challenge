import FokkerChallenge.BetaNamableClosure
import FokkerChallenge.LiftSearch
import FokkerChallenge.GenTerms
import FokkerChallenge.Decider.NoDuplicate
import FokkerChallenge.Decider.EveryBvarUsed
import FokkerChallenge.Decider.OnlyOneVarUsed
import FokkerChallenge.Decider.ArgNotVar
import FokkerChallenge.Decider.RigidHead
import FokkerChallenge.Decider.TailNotVar
import FokkerChallenge.Decider.TwoVarsPerNode
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

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

theorem mem_terms_fokker_lt_7_iff (M : Term String)
  (hm : M ∈ terms_fokker_lt_7) :
  M.every_bvar_used \/ M.no_duplicate \/ M.closedNodeTwoVars \/ M.tailOk \/ M.rigid \/ M.argOk := by
     native_decide +revert

theorem not_basis_of_closed_lc_small_fokker_size (M : Term String)
    (hm : M.LC ∧ M.fv = ∅ ∧ M.fokker_size < 7) : not_basis M := by
    rw [closed_lc_iff_mem_gen_terms] at hm
    apply mem_terms_fokker_lt_7_iff at hm
    rcases hm with h|h|h|h|h|h
    . exact not_reaches_K h
    . exact not_reaches_omega h
    . exact closedNodeTwoVars_not_basis h
    . exact tailOk_not_basis h
    . exact rigid_not_basis h
    . exact argOk_not_basis h
