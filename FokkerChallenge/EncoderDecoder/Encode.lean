import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import Mathlib.Data.Set.Card
import FokkerChallenge.Basic
import FokkerChallenge.EnhancedCslib.CountBvar
import FokkerChallenge.EnhancedCslib.Fmt
import FokkerChallenge.EncoderDecoder.Basic
import FokkerChallenge.FamousCombinator

def main : IO Unit :=
  let term := Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.K
  match Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.encode term with
  | some s => do
      let s := String.ofList s
      IO.println s!"{s}"
  | none => do
      IO.println "Fail to encode"
