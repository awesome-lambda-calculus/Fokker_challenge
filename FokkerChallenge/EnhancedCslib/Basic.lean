import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Congruence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Foundations.Data.HasFresh
import Mathlib.Data.Finset.Lattice.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

def r_preserves (f: Term String -> Bool) (R : Term String → Term String → Prop) : Prop :=
  ∀ M N, R M N → f M → f N

@[scoped grind]
inductive IsFvar {Var} : Term Var → Prop
| fvar (m : Var) : IsFvar (Term.fvar m)

@[scoped grind]
inductive IsBvar {Var} : Term Var → Prop
| bvar (i : Nat) : IsBvar (Term.bvar i)
