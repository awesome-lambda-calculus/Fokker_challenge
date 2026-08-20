import FokkerChallenge.DeBruijnParse

/-!
# Notation for de Bruijn terms

`db! "λ(λ12)0"` elaborates to the locally nameless term denoted by the string,
by running the parser `parseDB` at elaboration time.  The elaborated term is a
plain constructor expression, so statements about it can be checked by the
kernel without ever reducing string operations.
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

open Lean Elab Term Meta

/-- Turn a parsed term into the expression denoting it. -/
private def toExprAux : Term String → Expr
  | .bvar n => mkApp2 (mkConst ``Term.bvar [Lean.Level.zero]) (mkConst ``String) (mkNatLit n)
  | .fvar x => mkApp2 (mkConst ``Term.fvar [Lean.Level.zero]) (mkConst ``String) (mkStrLit x)
  | .abs t => mkApp2 (mkConst ``Term.abs [Lean.Level.zero]) (mkConst ``String) (toExprAux t)
  | .app t u =>
      mkApp3 (mkConst ``Term.app [Lean.Level.zero]) (mkConst ``String) (toExprAux t) (toExprAux u)

/-- `db! "λ(λ12)0"` is the locally nameless term written in de Bruijn notation. -/
syntax (name := dbTermStx) "db!" str : term

@[term_elab dbTermStx]
private def elabDbTerm : TermElab := fun stx _ => do
  match stx with
  | `(db! $s:str) =>
      match parseDB s.getString with
      | some t => return toExprAux t
      | none => throwError "db!: cannot parse de Bruijn term {s.getString}"
  | _ => throwUnsupportedSyntax

example : (db! "λ(λ12)0") = Term.abs (Term.app (Term.abs (Term.app (Term.bvar 1)
    (Term.bvar 2))) (Term.bvar 0)) := rfl
