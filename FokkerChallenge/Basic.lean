import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Congruence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Foundations.Data.HasFresh
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
  induction M with (unfold openRec fokker_size; grind)

/-
  Generated terms (application closure)
-/
inductive Gen (atom: Term String) : Term String → Prop where
  | base : Gen atom atom
  | app {M N}  : Gen atom M → Gen atom N → Gen atom (app M N)

theorem gen_lc {atom M} (h: Gen atom M) : atom.LC -> M.LC := by
  induction h with grind

def not_basis (atom : Term String) : Prop :=
  ∃ y, y.LC ∧ y.fv = ∅ ∧ ∀ t, Gen atom t → Relation.ReflTransGen FullBetaEta t y → False


end Term

end LambdaCalculus.LocallyNameless.Untyped

end Cslib
