import FokkerChallenge.BLC.BLCTotal
import FokkerChallenge.BLC.BLCEnum
import FokkerChallenge.Decider.NoDuplicate
import FokkerChallenge.Decider.EveryBvarUsed
import FokkerChallenge.Decider.All0
import FokkerChallenge.Decider.OnlyOneVarUsed
import FokkerChallenge.Decider.ArgNotVar
import FokkerChallenge.Decider.RigidHead
import FokkerChallenge.Decider.TailNotVar
import FokkerChallenge.BetaNamableClosure
import FokkerChallenge.LiftSearch
import FokkerChallenge.GenTerms
import FokkerChallenge.FokkerResolved


namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-
theorem mem_terms_blc_lt_26_iff (M : Term String)
     (hm : M ∈ termsUpTo String 26) :
     (M.every_bvar_used || M.no_duplicate || M.isNamedOfXY || M.tailOk || M.rigid || M.argOk || M ∈ fokkerUndecidedTerms) = true := by
     native_decide +revert
-/
