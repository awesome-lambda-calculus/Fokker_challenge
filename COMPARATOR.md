# Checking the results with Comparator

[Comparator](https://github.com/leanprover/comparator) checks that a `Solution`
module really proves the statements written down in a `Challenge` module, that
it uses no axioms beyond an explicit permitted list, and that the resulting
environment is accepted by the Lean kernel (replayed from scratch, from an
export file, without loading any `.olean`).

This repository ships the three files that Comparator needs:

| file | contents |
| --- | --- |
| `Challenge.lean` | the two headline statements, as `sorry`ed theorems |
| `Solution.lean` | the same two statements, proved from the library |
| `comparator-config.json` | the Comparator configuration |

The two statements are

```lean
theorem fokker_challenge_size_lt_7 (M : Term String)
    (hm : M.LC ∧ M.fv = ∅ ∧ M.fokker_size < 7) : not_basis M

theorem fokker_challenge_blc_lt_26 (M : Term String)
    (hm : M.fv = ∅ ∧ M.blcT.length < 26) (h_lc : M.LC) : not_basis M
```

i.e. the results of `FokkerChallenge/FokkerResolved.lean` and
`FokkerChallenge/BLC/BLCResolved.lean`, restated at the top level.

## Running it

With `landrun` and a matching `lean4export` in `PATH`, from the root of this
repository:

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory $(pwd) -- \
  bash -c 'lake env /path/to/comparator comparator-config.json'
```

`Solution.lean` (and the library it imports) is built inside the sandbox, so the
run takes as long as a full build of the project.  On success Comparator prints

```
Lean default kernel accepts the solution
Your solution is okay!
```

Other kernels can be added through the `external_kernels` field of
`comparator-config.json`; see the Comparator README.

## The permitted axioms

```json
"permitted_axioms": [
    "propext",
    "Quot.sound",
    "Classical.choice",
    "Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.mem_terms_fokker_lt_7_iff._native.native_decide.ax_1_1",
    "Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.mem_terms_blc_lt_26_iff._native.native_decide.ax_1_1"
]
```

Besides the three standard axioms, the two proofs depend on the two
`native_decide` steps of the development — the sweeps of the two finite search
spaces — and on nothing else.  In the Lean version used here each `native_decide`
call produces one axiom of its own, named after the theorem it occurs in; the two
axioms above are exactly those, and they say

```lean
axiom …mem_terms_fokker_lt_7_iff._native.native_decide.ax_1_1 :
  decide (∀ M ∈ terms_fokker_lt_7,
    M.every_bvar_used = true ∨ M.no_duplicate = true ∨ M.closedNodeTwoVars = true ∨
    M.tailOk = true ∨ M.rigid = true ∨ M.argOk = true) = true
```

and analogously for `termsUpTo String 26`.  Both types mention definitions only,
so what is being trusted is precisely the evaluation of two explicit decision
procedures on two explicit finite lists.  Comparator checks that these axioms
have the *same type* in `Challenge` and in `Solution`, which is why
`Challenge.lean` imports `FokkerChallenge/NativeEnum.lean`, the module that
isolates the two `native_decide` steps.

To check the development without trusting `native_decide` at all, one would have
to replace the two enumeration lemmas of `FokkerChallenge/NativeEnum.lean` by
kernel-checkable proofs; every other step of the development, including all
certificate lists, is already checked by the kernel.

## Trust

Comparator's guarantee is about the `Solution` side: its export is compared
against the `Challenge` statements, its axioms are checked, and the environment
is replayed into the kernel from scratch.  What a reader still has to check by
hand is that the statements of `Challenge.lean` say what they are meant to say —
that is, the definitions listed in the file's module docstring.
