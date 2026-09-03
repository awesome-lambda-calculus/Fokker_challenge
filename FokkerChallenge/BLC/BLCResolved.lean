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

-- The certificate lists themselves live in `FokkerChallenge.BLC.BLCCertLists`.

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

/-- The search is only a *semi*-decision procedure: it may fail.  For the
combinator `S = λλλ 2 0 (1 0)` no chain of at most two lift β-expansions is
nameable with two names — as it must be, since by Statman's theorem `S` is not
β-convertible to any two-name term. -/
theorem liftSearch_sComb_eq_none : liftSearch 2 (db! "λλλ20(10)") = none := by
  decide

/-
-- Original βη-flavoured version of the two statements below.  It is kept for the
-- record: `reducesEntriesOK` / `BetaEtaReducesToNamable` live in the (currently
-- unused) module `FokkerChallenge.TwoVarsAreNotEnough.BetaEtaToNamable`, which is
-- not part of the build.  Since every certificate above consists of a single
-- *β*-step, the β-version proved right below is enough, and is what the
-- classification theorem uses.
theorem fokkerUpdatedOpenCerts_ok : reducesEntriesOK fokkerUpdatedOpenCerts = true := by decide

/-- **16 of the 80 open terms βη-reduce to a term nameable with the two variable
names `x` and `y`.** -/
theorem fokkerUpdatedOpenReduces_betaEtaReducesToNamable :
    ∀ T ∈ fokkerUpdatedOpenReduces, BetaEtaReducesToNamable T :=
  betaEtaReducesToNamable_of_entriesOK fokkerUpdatedOpenCerts_ok
-/

/-- Every certificate of `fokkerUpdatedOpenCerts` checks out: each of the 16
terms β-reduces in one step to a term nameable with the two variable names `x`
and `y`. -/
theorem fokkerUpdatedOpenCerts_ok :
    reducesToNamableEntriesOK fokkerUpdatedOpenCerts = true := by decide

/-- **The 16 terms of `fokkerUpdatedOpenReduces` are not one-point bases**,
because each of them β-reduces to a term nameable with the two variable names
`x` and `y`. -/
theorem fokkerUpdatedOpenReduces_not_basis :
    ∀ T ∈ fokkerUpdatedOpenReduces, not_basis T :=
  not_basis_of_reducesToNamableEntriesOK fokkerUpdatedOpenCerts_ok

-- `mem_terms_blc_lt_26_iff`, the one `native_decide` step of this
-- classification, now lives in `FokkerChallenge.NativeEnum`.

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
  . exact properClosedNoParens_not_basis h
  . exact BetaReductOfNamable_not_basis (fokkerUndecided_betaReductOfNamable  _ h)
  . exact fokkerUpdatedOpenReduces_not_basis _ h
  . subst M
    exact LamLam102.not_basis_0_lamlam102
  . subst M
    exact not_basis_0_lamlam201
  . subst M
    exact LamLamLam0Lam102.not_basis_lamlamlam0lam102
  . subst M
    exact LamLamLam0Lam201.not_basis_lamlamlam0lam201
