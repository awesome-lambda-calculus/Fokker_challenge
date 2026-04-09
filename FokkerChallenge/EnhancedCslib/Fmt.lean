import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Congruence
import Mathlib.Data.Finset.Lattice.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term
def toStringTerm {α} [ToString α] : Term α → String
  | bvar n => toString n
  | fvar x => toString x
  | abs t => "λ" ++ toStringTerm t
  | app t1 t2 =>
      let s1 :=
        match t1 with
        | abs _ => "(" ++ toStringTerm t1 ++ ")"
        | _     => toStringTerm t1
      let s2 :=
        match t2 with
        | app _ _ => "(" ++ toStringTerm t2 ++ ")"
        | abs _   => "(" ++ toStringTerm t2 ++ ")"
        | _       => toStringTerm t2
      s1 ++ " " ++ s2

instance {α} [ToString α] : ToString (Term α) := ⟨toStringTerm⟩

end Term

end LambdaCalculus.LocallyNameless.Untyped

end Cslib
