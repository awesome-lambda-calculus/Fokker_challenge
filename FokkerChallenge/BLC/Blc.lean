import FokkerChallenge

def main : IO Unit := do
  let terms := Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.termsUpTo String 26

  let terms := terms.filter (fun t => Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.LcAt 0 t)
  let terms := terms.filter (fun t => !Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.every_bvar_used t)
  let terms := terms.filter (fun t => !Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.only_one_var_used t)
  let terms := terms.filter (fun t => !Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.no_duplicate t)
  let terms := terms.filter (fun t => !Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.isNamedOfXY t)
  let terms := terms.filter (fun t => !Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.tailOk t)
  let terms := terms.filter (fun t => !Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.rigid t)
  let terms := terms.filter (fun t => !Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.argOk t)
  let terms := terms.filter (fun t => !Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.properClosedNoParens t)

  let terms := terms.filter (fun t => t ∉ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fokkerUndecidedTerms)
  let terms := terms.filter (fun t => t ∉ Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.fokkerUpdatedOpenCerts.map Prod.fst)


  let len := terms.length
  IO.println s!"{len} undecided"
  IO.println s!"{terms}"
