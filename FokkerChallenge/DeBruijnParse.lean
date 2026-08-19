import FokkerChallenge.Basic

/-!
# A parser for de Bruijn notation

Terms such as `λ(λ(λ0)(11))0` are parsed into `Term String`, the locally
nameless representation (which coincides with plain de Bruijn notation as long
as no free variable is involved).  The grammar is

```
term ::= atom atom … atom            (application, left associative)
atom ::= digit | '(' term ')' | 'λ' term
```

where a `λ` extends as far to the right as possible and a digit is a single
de Bruijn index.
-/

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term


/-- The numeric value of a decimal digit character. -/
def digitVal? (c : Char) : Option ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat) else none

mutual

/-- Parse a single atom: a digit, a parenthesised term, or a `λ`-abstraction. -/
def pAtom : ℕ → List Char → Option (Term String × List Char)
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, c :: cs =>
      if c = '(' then
        match pTerm f cs with
        | some (t, ')' :: rest) => some (t, rest)
        | _ => none
      else if c = 'λ' then
        match pTerm f cs with
        | some (t, rest) => some (Term.abs t, rest)
        | none => none
      else
        match digitVal? c with
        | some n => some (Term.bvar n, cs)
        | none => none

/-- Parse a term: a nonempty juxtaposition of atoms. -/
def pTerm : ℕ → List Char → Option (Term String × List Char)
  | 0, _ => none
  | f + 1, cs =>
      match pAtom f cs with
      | none => none
      | some (t, rest) => pApps f t rest

/-- Continue parsing the arguments of an application. -/
def pApps : ℕ → Term String → List Char → Option (Term String × List Char)
  | 0, _, _ => none
  | f + 1, t, cs =>
      match cs with
      | [] => some (t, [])
      | c :: _ =>
          if c = ')' then some (t, cs)
          else
            match pAtom f cs with
            | none => none
            | some (u, rest) => pApps f (Term.app t u) rest

end

/-- Parse a string in de Bruijn notation into a locally nameless term. -/
def parseDB (s : String) : Option (Term String) :=
  match pTerm (2 * s.length + 2) s.toList with
  | some (t, []) => some t
  | _ => none
