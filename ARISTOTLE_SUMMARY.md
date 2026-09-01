# Summary of changes for run ebf15766-7d06-4c6c-968f-d2c91ed2f7a0
The single remaining `sorry` in the project is gone: the whole library now builds with `lake build` and contains no `sorry`/`admit`.

**Where it was.** In `FokkerChallenge/BLC/BLCResolved.lean`, the classification theorem `not_basis_of_closed_lc_small_blc` (every closed, locally closed term with a binary-lambda-calculus encoding shorter than 26 bits is not a one-point basis) had one open case: the 16 terms of `fokkerUpdatedOpenCerts`, each of which β-reduces in one step to a term nameable with only the two variable names `x`, `y`. The existing deciders cover the dual situation (terms that are β-*reducts* of nameable terms), so a new criterion was needed.

**What was added.**
* `FokkerChallenge/EnhancedCslib/GenFinset.lean` — `not_basises_nf`, a strengthening of `not_basises` in which the unreachable target term is additionally βη-normal, with `not_basises_of_nf` recovering the original statement.
* `FokkerChallenge/TwoVarsAreNotEnough/Final.lean` — the three existing "not a basis" theorems now come in `_nf` form (`no_reduction_to_Hn_with_depth_bound_nf`, `..._closedunderapp_nf`, `isNamedOfXY_not_basises_nf`, `isNamedOfXY_not_basis_nf`), recording that the witness `H (n+1)` they produce is βη-normal. The previously existing names are kept, now derived from the `_nf` versions, so nothing downstream changed.
* `FokkerChallenge/BetaReducesToNamable.lean` (new module) — the criterion `not_basis_of_betaStar_namableXY`: if `M ↠βᶠ S` and `S` is nameable with two names, then `M` is not a one-point basis. The argument: every applicative combination of `M` β-reduces to the corresponding combination of `S` (`genfinset_single_betaStar`), and confluence of βη together with the normality of the witness turns any reduction of a combination of `M` to the witness into one from a combination of `S`, contradicting the two-names theorem. The module also provides a certificate format (`reducesToNamableCheck`, `reducesToNamableEntriesOK`) built on the project's existing `betaCheck`.
* `FokkerChallenge/BLC/BLCResolved.lean` — `fokkerUpdatedOpenCerts_ok` verifies all 16 certificates by kernel computation (`decide`), giving `fokkerUpdatedOpenReduces_not_basis`, which closes the last case. The pre-existing commented-out βη-flavoured variant of these statements was left in place with an explanatory note.

**Verification.** Full `lake build` succeeds; a search for `sorry`/`admit` over the sources finds none. `not_basis_of_betaStar_namableXY` and `fokkerUpdatedOpenReduces_not_basis` depend only on `propext`, `Classical.choice`, `Quot.sound`; the top-level `not_basis_of_closed_lc_small_blc` additionally depends on the kernel-external computation of the pre-existing enumeration lemma `mem_terms_blc_lt_26_iff`, which was already in the project and was not modified. All work is committed and pushed.

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
