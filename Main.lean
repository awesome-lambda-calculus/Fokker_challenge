import FokkerChallenge

def main : IO Unit := do
  let terms := Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.terms_fokker_lt_7

  let terms := terms.filter (fun t => !Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.every_bvar_used t)
  let terms := terms.filter (fun t => !Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.only_one_var_used t)
  let terms := terms.filter (fun t => !Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.no_duplicate t)
  let terms := terms.filter (fun t => !Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.isNamedOfXY t)

  let expected_nil := terms.filter (fun t => Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.all0_no_fvar_inside_abs t)
  if expected_nil ≠ [] then
      IO.eprintln "error"

  let terms := terms.filter (fun t => !Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.tailOk t)
  let terms := terms.filter (fun t => !Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.rigid t)
  let terms := terms.filter (fun t => !Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.argOk t)

  let terms := terms.filter (fun t => !Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.has_beta_redex t)
  let terms := terms.filter (fun t => !Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.has_eta_redex t)

  let len := terms.length
  IO.println s!"{len} undecided"
  IO.println s!"{terms}"
