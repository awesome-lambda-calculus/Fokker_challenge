import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Mathlib.Data.Finset.Lattice.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

@[simp, scoped grind =]
def fokker_size : (Term String) -> Nat
| bvar _ => 0
| fvar _ => 0
| abs t => 1 + fokker_size t
| app t1 t2 => 1 + fokker_size t1 + fokker_size t2

@[scoped grind =]
theorem fokker_size_openrec {x M}: (i: Nat) -> (openRec i (fvar x) M).fokker_size = M.fokker_size := by
  induction M <;> grind

end Term

end LambdaCalculus.LocallyNameless.Untyped

end Cslib
