# Summary of changes for run 46456d93-ee03-402c-b1e1-a4a1a89406ba
The project is now set up so that its two headline results can be checked independently with Comparator, and the whole setup was run end to end successfully.

What was added:

- `Challenge.lean` — the two headline statements as `sorry`ed theorems, `fokker_challenge_size_lt_7` (every closed, locally closed term of Fokker size < 7 is not a one-point basis) and `fokker_challenge_blc_lt_26` (every closed, locally closed term with a binary lambda calculus code shorter than 26 bits is not a one-point basis). Its module docstring lists exactly the definitions (`Term`, `LC`, `fv`, `fokker_size`, `blcT`, `not_basis`) a reader must inspect to know what is being claimed.
- `Solution.lean` — the same two statements, proved from the library's `not_basis_of_closed_lc_small_fokker_size` and `not_basis_of_closed_lc_small_blc`. No `sorry`.
- `comparator-config.json` — the configuration listing both theorems and the permitted axioms.
- `COMPARATOR.md` — how to run the check, what the permitted axioms are, and what remains to be trusted.
- `lakefile.toml` — new `Challenge` and `Solution` library targets.

One refactor was needed to make the configuration valid. In this Lean version each `native_decide` call produces its own axiom, named after the enclosing theorem, and Comparator requires every permitted axiom to be present with the same type in the challenge environment too. The two `native_decide` enumeration steps were therefore moved out of the proof files into a dedicated module `FokkerChallenge/NativeEnum.lean` (with the BLC certificate lists factored into `FokkerChallenge/BLC/BLCCertLists.lean`, so that module needs only definitions). `Challenge.lean` imports `FokkerChallenge/NativeEnum.lean`; `FokkerResolved.lean` and `BLC/BLCResolved.lean` now import the enumeration lemmas instead of stating them, and are otherwise unchanged. The permitted axioms are `propext`, `Quot.sound`, `Classical.choice` and the two `native_decide` axioms, whose types are `decide <explicit proposition over the deciders and the two finite enumerations> = true` — i.e. only definitions, as documented in `COMPARATOR.md`.

Verification performed:

- `lake build` of the full project, plus `lake build Challenge Solution`, succeed; the only `sorry`s in the project are the two intended ones in `Challenge.lean`.
- Axiom check of the solution theorems: `propext`, `Classical.choice`, `Quot.sound` and the corresponding `native_decide` axiom, and nothing else.
- Comparator itself was built and run against `comparator-config.json` from the project root; it exported and compared both environments, checked the axioms and replayed the solution environment into the Lean kernel, reporting "Lean default kernel accepts the solution / Your solution is okay!". This run used Comparator's development shim in place of `landrun`, so the export, statement-comparison, axiom and kernel-replay steps were exercised but the sandboxing was not; the command for a properly sandboxed run is given in `COMPARATOR.md`.
- As a negative control, deliberately altering one solution statement made Comparator reject with "Challenge and solution theorem statement do not match"; the original file was restored and rebuilt.

The README gained a short "Independent checking" section pointing at these files. All work is committed.