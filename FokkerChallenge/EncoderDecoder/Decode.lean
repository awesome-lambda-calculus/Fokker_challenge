import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEtaConfluence
import Mathlib.Data.Set.Card
import FokkerChallenge.Basic
import FokkerChallenge.EnhancedCslib.CountBvar
import FokkerChallenge.EnhancedCslib.Fmt
import FokkerChallenge.EncoderDecoder.Basic

def main (args : List String) : IO Unit := do
  for arg in args do
    let arg := arg.toUpper
    let arg := arg.replace "TERM_"  ""
    let arg := arg.replace "NORMAL_" ""
    match Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.decode arg.toList with
    | some t => IO.println s!"decoded: {t}"
    | none => IO.println "invalid BLC bitstring"
