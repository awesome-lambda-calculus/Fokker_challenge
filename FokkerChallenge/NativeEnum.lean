import FokkerChallenge.GenTerms
import FokkerChallenge.DBNotation
import FokkerChallenge.BLC.BLCEnum
import FokkerChallenge.BLC.BLCCertLists
import FokkerChallenge.Decider.NoDuplicate
import FokkerChallenge.Decider.EveryBvarUsed
import FokkerChallenge.Decider.ArgNotVar
import FokkerChallenge.Decider.RigidHead
import FokkerChallenge.Decider.TailNotVar
import FokkerChallenge.Decider.CompositiveEffect
import FokkerChallenge.Decider.TwoVarsPerNode

/-!
# The two enumeration steps, checked by `native_decide`

The whole development uses `native_decide` in exactly two places, collected
here: the sweep of the two finite search spaces

* `terms_fokker_lt_7`, the closed locally closed terms of Fokker size `< 7`;
* `termsUpTo String 26`, the de Bruijn terms with a binary lambda calculus code
  of length `< 26`;

showing that every term in them passes one of the decidable criteria of
`FokkerChallenge.Decider.*` (or is one of the finitely many terms with a
dedicated proof).

Both statements mention definitions only, so the two axioms that `native_decide`
generates for them,

```
mem_terms_fokker_lt_7_iff._native.native_decide.ax_1_1
mem_terms_blc_lt_26_iff._native.native_decide.ax_1_1
```

state that a `decide` of an explicit, purely definitional proposition evaluates
to `true`.  Everything else in the development is checked by the kernel.
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

set_option maxRecDepth 100000

/-- Every closed locally closed term of Fokker size `< 7` passes one of the
decidable criteria. -/
theorem mem_terms_fokker_lt_7_iff (M : Term String)
  (hm : M ∈ terms_fokker_lt_7) :
  M.every_bvar_used \/ M.no_duplicate \/ M.closedNodeTwoVars \/ M.tailOk \/ M.rigid \/ M.argOk := by
     native_decide +revert

/-- Every de Bruijn term with a binary lambda calculus code of length `< 26`
either is not locally closed, or passes one of the decidable criteria, or is one
of the finitely many terms handled by a dedicated proof. -/
theorem mem_terms_blc_lt_26_iff (M : Term String)
  (hm : M ∈ termsUpTo String 26) :
  LcAt 0 M = false \/ M.every_bvar_used \/ M.no_duplicate \/ M.closedNodeTwoVars \/ M.tailOk \/ M.rigid \/ M.argOk \/ M.properClosedNoParens \/ M ∈ fokkerUndecidedTerms \/ M ∈ fokkerUpdatedOpenCerts.map Prod.fst \/ M = db! "λλ0(λλ102)" \/ M = db! "λλ0(λλ201)" \/ M = db! "λλλ0(λ102)" \/ M = db! "λλλ0(λ201)" := by
     native_decide +revert

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
