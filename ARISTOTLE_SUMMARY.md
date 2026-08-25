# Summary of changes for run 9905ac50-f06c-4a90-9de5-10315e9d94de
## Result: 50 of the 64 terms proved not one-point bases; 14 remain open

All work builds cleanly (full `lake build`, no `sorry`/`admit` anywhere in `FokkerChallenge/`), and the main theorems depend only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — they do not rely on the project's pre-existing axioms. Everything is committed and pushed.

### What was added

Two new deciders, each an independently useful, reusable criterion. Both follow the same scheme: a Boolean test that holds of the term, is preserved by β- and η-steps and by application, and fails for `K = λx.λy.x`; hence no applicative combination of a term passing the test can βη-reduce to `K`.

* `FokkerChallenge/Decider/RigidHead.lean` — `rigid`: every abstraction block is `λ x₁ … x_s. z M₁ … M_k` with `k ≥ 1` whose head `z` is the block's innermost binder, all parts rigid again. Theorems `rigid_not_basises`, `rigid_not_basis`. Covers 26 of the 64 terms.
* `FokkerChallenge/Decider/TailNotVar.lean` — `tailOk`: every abstraction block has `k ≥ 1` arguments and a **non-variable** last argument, all parts tail-applied again. Such terms contain no η-redex at all, which is what makes η-preservation work. Theorems `tailOk_not_basises`, `tailOk_not_basis`. Covers 36 of the 64 terms.
* `FokkerChallenge/Undecided64.lean` — the 64 terms of `undecided_terms.json` as `undecidedTerms` (with `undecidedTerms_length = 64`), the combined test `covered t = rigid t || tailOk t`, and
  * `undecided_covered_not_basis` : every covered term of the list is `not_basis`,
  * `undecided_covered_count` : exactly 50 of the 64 are covered (checked by computation),
  * `undecidedTermsRemaining` : the 14 terms that are not covered, with `undecidedTermsRemaining_length` checking that these are exactly the uncovered ones.

`FokkerChallenge.lean` imports the new modules.

### What is not done

The requested statement — *every* term of `undecided_terms.json` is `not_basis` — is **not** fully proved: 14 terms remain open. They are

```
λλλλ1(00)2  λλλλ1002   λλλλ2(00)1  λλλλ2001
λλλλ1(02)0  λλλλ1(20)0 λλλλ2(01)0  λλλλ2(10)0
λλλλ1020    λλλλ2010
λλλ0(λ102)  λλλ0(λ201) λλ0(λλ102)  λλ0(λλ201)
```

Each has a block whose last argument is a bound variable and whose head is not the innermost binder, so both deciders fail. A number of candidate invariants were tried for them and each was refuted by an explicit β- or η-step leaving the class; `REMAINING14.md` records these candidates, the one candidate that survived extensive random testing (a variant evaluated on η-normal forms, which would settle six of the fourteen if its β-preservation were proved), and what a proof of it would require. That file is explicitly marked as exploratory and unverified — none of its claims are machine-checked.
