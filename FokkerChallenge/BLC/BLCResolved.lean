import FokkerChallenge.BLC.BLCTotal
import FokkerChallenge.BLC.BLCEnum
import FokkerChallenge.BLC.BLCCertLists
import FokkerChallenge.NativeEnum
import FokkerChallenge.Decider.NoDuplicate
import FokkerChallenge.Decider.EveryBvarUsed
import FokkerChallenge.Decider.All0
import FokkerChallenge.Decider.ArgNotVar
import FokkerChallenge.Decider.RigidHead
import FokkerChallenge.Decider.TailNotVar
import FokkerChallenge.Decider.CompositiveEffect
import FokkerChallenge.Decider.TwoVarsPerNode
import FokkerChallenge.BetaNamableClosure
import FokkerChallenge.BetaReducesToNamable
import FokkerChallenge.LiftSearch
import FokkerChallenge.GenTerms
import FokkerChallenge.NotBasisLamLam201
import FokkerChallenge.NotBasisLamLam102
import FokkerChallenge.NotBasisLamLamLam0Lam201
import FokkerChallenge.NotBasisLamLamLam0Lam102


namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

set_option maxRecDepth 100000

theorem not_basis_of_closed_lc_small_blc (M : Term String)
    (hm :  M.fv = ∅ ∧ M.blcT.length < 26)
    (h_lc : M.LC) : not_basis M := by
  rw [<- mem_termsUpTo_fv] at hm
  apply mem_terms_blc_lt_26_iff at hm
  rcases hm with h|h|h|h|h|h|h|h|h|h|h|h|h|h
  . rw [<- lcAt_iff_LC] at h_lc
    grind
  . exact not_reaches_K h
  . exact not_reaches_omega h
  . exact closedNodeTwoVars_not_basis h
  . exact tailOk_not_basis h
  . exact rigid_not_basis h
  . exact argOk_not_basis h
  . exact isProperBody_lc_not_basis h h_lc
  . exact noCompositive_lc_not_basis h h_lc
  . exact BetaReductOfNamable_not_basis (fokkerUndecided_betaReductOfNamable  _ h)
  . subst M
    exact LamLam102.not_basis_0_lamlam102
  . subst M
    exact not_basis_0_lamlam201
  . subst M
    exact LamLamLam0Lam102.not_basis_lamlamlam0lam102
  . subst M
    exact LamLamLam0Lam201.not_basis_lamlamlam0lam201
