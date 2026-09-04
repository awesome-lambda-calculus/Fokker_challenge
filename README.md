# Fokker_challenge

The currently known smallest one-point bases[^5] for untyped lambda calculus, measured by Fokker size, have size 7.
There are three such one-point bases of Fokker size 7.
The first one (λx.λy.λz. y (λt.z) (x z)) was discovered by Meredith in 1963[^11]. Another two (λx.λy.λz.y z(x(λt.z))) (λx.λy.λz.x z(y(λt.z))) were found in 2022 by John Tromp[^4] and Mtv Europe[^10].

| Lambda term                | De Bruijn index    | Discovered by          | Year | Fokker size | BLC size | Reference  |
| -------------------------- | ------------------ | ---------------------- | ---: | ----------: | -------: | ---------- |
| `λx.λy.λz. y (λt.z) (x z)` | `λλλ 1 (λ1) (2 0)` | Meredith               | 1963 |           7 |       26 | [^11]      |
| `λx.λy.λz. y z (x (λt.z))` | `λλλ 1 0 (2 (λ1))` | John Tromp, Mtv Europe | 2022 |           7 |       26 | [^4] [^10] |
| `λx.λy.λz. x z (y (λt.z))` | `λλλ 2 0 (1 (λ1))` | John Tromp, Mtv Europe | 2022 |           7 |       26 | [^4] [^10] |


Take ɑ for example:

```
α = λλλ2 0 (1 (λ1))
B = λλλ2 (1 0) = α(α(α(α(α α) α))(α α) α)(α(α(α α)))
C = λλλ2 0 1 = α(α α α(α α α)(α α)(α α)) α α
K = λλ1 = α α(α(α α) α α α) α(α α)
W = λλ1 0 0 = α α(α(α(α α) α))
I = λ0 = α(α(α(α α) α))(α(α α) α)
F = λλ0 = α α α(α(α α)(α α)(α α)) α
S = λλλ (2 0) (1 0) = α(α(α α(α α(α α))(α(α(α α(α α))))))α α
```

The Fokker size of a closed term is the number of abstractions and applications it contains when written.

```
def fokker_size : (Term String) -> Nat
| bvar _ => 0
| fvar _ => 0
| abs t => 1 + fokker_size t
| app t1 t2 => 1 + fokker_size t1 + fokker_size t2
```


Our goal:
- Verify the smallest basis have fokker size 7 Or
- Find the smallest basis

We use lean4 to formalize that all smaller closed term can't be basis.

Our proof is based on [cslib](https://github.com/leanprover/cslib).

## Status

**Both search spaces we set out to clear are now completely closed, for arbitrary
terms (not just normal forms).** The library builds with `lake build` and contains
no `sorry` / `admit`, and no `axiom` declarations of its own.

The two headline theorems are

* `not_basis_of_closed_lc_small_fokker_size`
  (`FokkerChallenge/FokkerResolved.lean`)

  ```lean
  theorem not_basis_of_closed_lc_small_fokker_size (M : Term String)
      (hm : M.LC ∧ M.fv = ∅ ∧ M.fokker_size < 7) : not_basis M
  ```

  Every closed, locally closed term of Fokker size at most 6 — the 5420 terms
  enumerated by `terms_fokker_lt_7` — fails to be a one-point basis. Together
  with Meredith's basis this says
  that the minimal Fokker size of a one-point basis is exactly 7 (the fact that
  the size-7 term *is* a basis is not formalized here).

* `not_basis_of_closed_lc_small_blc`
  (`FokkerChallenge/BLC/BLCResolved.lean`)

  ```lean
  theorem not_basis_of_closed_lc_small_blc (M : Term String)
      (hm : M.fv = ∅ ∧ M.blcT.length < 26) (h_lc : M.LC) : not_basis M
  ```

  Every closed, locally closed term whose binary-lambda-calculus code[^9] is
  shorter than 26 bits — 33382 terms, out of the 360965 de Bruijn terms of that
  code length — fails to be a one-point basis.

A third result, general rather than tied to a finite search space, is the
**two-variables-per-node criterion** of `FokkerChallenge/Decider/TwoVarsPerNode.lean`:
any closed term that uses at most two variables at every node of its tree is not
a one-point basis. It has its own section [below](#the-two-variables-per-node-criterion);
it alone settles 5060 of the 5420 terms of the Fokker-size space.

Here `not_basis M` is the strong statement (`FokkerChallenge/EnhancedCslib/GenFinset.lean`)
that there is a closed, locally closed term `y` such that *no* applicative
combination of `M` βη-reduces to `y`:

```lean
def not_basises (atoms : List (Term String)) : Prop :=
  ∃ y, y.LC ∧ y.fv = ∅ ∧ ∀ t, GenFinset atoms t → t ↠βηᶠ y → False

def not_basis (atom : Term String) : Prop := not_basises [atom]
```

Both classification theorems rely on `native_decide` for the one enumeration
step that dispatches the whole search space to the deciders below
(`mem_terms_fokker_lt_7_iff`, `mem_terms_blc_lt_26_iff`, both isolated in
`FokkerChallenge/NativeEnum.lean`); apart from that they use
only `propext`, `Classical.choice` and `Quot.sound`. Every individual decider and
every certificate check is verified by the kernel. The only other `native_decide`
uses are the two coverage statistics over `terms_fokker_lt_7` in
`FokkerCertsTwoVarsPerNode.lean`, which nothing else depends on.

The two executables re-run the corresponding filters outside the kernel:

```
$ lake exe fokker_challenge
0 undecided
[]

$ lake exe blc
4 undecided
[λλλ0 (λ1 0 2), λλλ0 (λ2 0 1), λλ0 (λλ1 0 2), λλ0 (λλ2 0 1)]
```

The four terms reported by `lake exe blc` are the ones with no generic decider;
each has its own dedicated proof file (see below), so the Lean classification
covers them too.

## How it is proved

The classification splits the search space into a handful of decidable classes,
each handled by a reusable criterion, plus a short list of hand-proved terms.

| criterion | file | idea |
| --- | --- | --- |
| `every_bvar_used` → `not_reaches_K` | `Decider/EveryBvarUsed.lean` | free/bound variable use is preserved, so `K` is unreachable |
| `no_duplicate` → `not_reaches_omega` | `Decider/NoDuplicate.lean` | non-duplicating terms cannot build `Ω` |
| `only_one_var_used` → `only_one_var_used_not_reaches_S` | `Decider/OnlyOneVarUsed.lean` | a term using at most one variable per block cannot build `S` |
| `all0_no_fvar_inside_abs` → `all0_no_fvar_inside_abs_not_reaches_S` | `Decider/All0.lean` | degenerate variable usage, `S` unreachable |
| `argOk` → `argOk_not_basis` | `Decider/ArgNotVar.lean` | shape of the arguments along the spine |
| `rigid` → `rigid_not_basis` | `Decider/RigidHead.lean` | every abstraction block `λx₁…x_s. z M₁…M_k` has `k ≥ 1` and head `z` the innermost binder |
| `tailOk` → `tailOk_not_basis` | `Decider/TailNotVar.lean` | every block has `k ≥ 1` arguments with a non-variable last argument (hence no η-redex) |
| `noCompositive`, `properClosedNoParens` | `Decider/CompositiveEffect.lean` | Curry's "no compositive effect": such terms cannot build `B` |
| `isNamedOfXY` → `isNamedOfXY_not_basis` | `TwoVarsAreNotEnough/*` | terms nameable with only two variable names, following Statman's *two variables are not enough*[^3]; proved here without extra hypotheses |
| `closedNodeTwoVars` → `closedNodeTwoVars_not_basis` | `Decider/TwoVarsPerNode.lean` | at most two variables are used at every node of the term tree; the unused binders are then created by β-steps from `K`, so the term is a β-reduct of a two-name term — see [the section below](#the-two-variables-per-node-criterion) |
| `BetaReductOfNamable` → `BetaReductOfNamable_not_basis` | `BetaCheck.lean`, `BetaNamableClosure.lean` | certificate: the term is a β-reduct of a two-name term |
| `not_basis_of_betaStar_namableXY` | `BetaReducesToNamable.lean` | certificate: the term β-reduces *to* a two-name term |

Each decider follows the same scheme: a Boolean test that holds of the term, is
preserved by β- and η-steps and by application, and fails for the target term
(`K`, `Ω`, `B`, …); hence no applicative combination of a term passing the test
can βη-reduce to that target.

The certificate-driven criteria are checked by kernel computation on explicit
lists: 785 terms in `fokkerUndecidedCerts`
(`FokkerCerts1.lean` … `FokkerCerts9.lean`, assembled in `FokkerResolved.lean`)
and 16 terms in `fokkerUpdatedOpenCerts` (`BLC/BLCResolved.lean`).

The first of these two certificate lists is largely superseded by the
two-variables-per-node criterion, described in the next section.

Four terms resist every generic criterion and get individual proofs:

* `λλ0(λλ102)` — `NotBasisLamLam102.lean`
* `λλ0(λλ201)` — `NotBasisLamLam201.lean`
* `λλλ0(λ102)` — `NotBasisLamLamLam0Lam102.lean`
* `λλλ0(λ201)` — `NotBasisLamLamLam0Lam201.lean`

For the first two the reachable βη-normal forms are classified completely — there
are exactly three, and every other applicative combination is unsolvable — so
neither `I` nor `K` is reachable. For the last two an explicit head-reduction
machine shows that no applicative combination βη-reduces to `I`. The supporting
head-reduction and divergence machinery lives in `PairT.lean` and
`EnhancedCslib/Head*.lean`.

`FokkerChallenge/EnhancedCslib/` collects the general λ-calculus theory the proofs
needed and that was not available upstream: βη normal forms, head reduction and
head strong normalization, η-spines, parallel reduction, and the `GenFinset`
closure of a set of atoms under application.

## The two-variables-per-node criterion

This is the most general criterion in the development, and the only one that
replaces a whole search-certificate list by a theorem.

**Files.** `FokkerChallenge/Decider/TwoVarsPerNode.lean` (the criterion and its
proof) and `FokkerChallenge/FokkerCertsTwoVarsPerNode.lean` (its coverage,
checked by computation).

### The test

Read a term as a tree. Every node carries the set of de Bruijn indices that
point outside of the subtree sitting at it — i.e. the enclosing binders whose
variable is used somewhere below that node:

```lean
def fidx : Term String → Finset ℕ
  | .bvar i  => {i}
  | .fvar _  => ∅
  | .app a b => fidx a ∪ fidx b
  | .abs t   => ((fidx t).erase 0).image (· - 1)
```

The test asks that at most **two** variables are used at every node, and that
the term is closed:

```lean
def nodeTwoVars : Term String → Bool
  | .bvar _  => true
  | .fvar _  => false
  | .app a b => nodeTwoVars a && nodeTwoVars b
  | .abs M   => decide ((fidx M).card ≤ 2) && nodeTwoVars M

def closedNodeTwoVars (t : Term String) : Bool :=
  nodeTwoVars t && decide (fidx t = ∅)
```

Both are Boolean and decidable by kernel computation, so applying the criterion
to a concrete term is a `by decide`.

### The theorem

```lean
/-- A closed term using at most two variables at every node is not a one-point basis. -/
theorem closedNodeTwoVars_not_basis {t : Term String} (h : closedNodeTwoVars t = true) :
    not_basis t
```

It is obtained from the sharper statement

```lean
theorem betaReductOfNamable_of_closedNodeTwoVars {t : Term String}
    (h : closedNodeTwoVars t = true) : BetaReductOfNamable t

theorem isNamedOfXY_namify_and_betaStar {t : Term String} (h : closedNodeTwoVars t = true) :
    isNamedOfXY (namify t) = true ∧ namify t ↠βᶠ t
```

— such a `t` is a β-reduct of a term nameable with only the two variable names
`x`, `y` — together with Statman's *two variables are not enough*[^3], which is
proved in `TwoVarsAreNotEnough/` and lifted to β-reducts in
`BetaNamableClosure.lean`.

### Why it is true

A closed term is nameable with two names exactly when at every abstraction node
`λ.M` at most **one** *enclosing* binder is used inside `M` (`nameableNodes`,
`namableXY_of_nameableNodes`); the binder introduced by the abstraction itself
always needs a name of its own. So a term passing the weaker per-node test can
fail to be nameable, but only because of binders that are *unused* in their
body. Each such binder is created by a single β-step from `K = λx.λy.x`:

```
K N  ⭢β  λ_.N
```

`namify t` performs exactly this β-expansion at every unused binder of `t`. The
proof is then constructive and splits in two halves:

* `namify_betaStar` : `namify t ↠βᶠ t` — the expansion reduces back to `t`;
* `nameableNodes_namify` + `namableXY_of_nameableNodes` : `namify t` really is
  nameable with `x` and `y`, via the explicit naming function `nameIt` and its
  correctness lemma `nameIt_spec`.

No search and no certificate is involved.

### Coverage

`FokkerCertsTwoVarsPerNode.lean` measures how much the criterion buys, by
computation:

| statement | content |
| --- | --- |
| `fokkerUndecided_nodeTwoVars_count` | 757 of the 785 search certificates of `FokkerCerts1`–`FokkerCerts9` are subsumed by the criterion |
| `fokkerUndecided_not_basis_of_notMem` | consequently those 757 terms are `not_basis` without their certificates |
| `fokkerUndecided_filter_not_nodeTwoVars` | the 28 exceptions are exactly the terms of `fokkerCertsNotNodeTwoVars` — each has a node using three variables (`λλλλ0(0(12))`, `λλλλ1200`, `λλ0(λλ210)`, …), so the criterion genuinely does not apply and they keep their certificates (`fokkerCertsNotNodeTwoVars_not_basis`) |
| `fokkerUndecided_namify_eq_cert_count` | for 384 of the covered terms `namify` even reproduces literally the term the search had found, e.g. `namify λλλ1(12) = λλ(λλ1)(0(01))` |
| `terms_fokker_lt_7_closedNodeTwoVars_count` | 5060 of the 5420 closed, locally closed terms of Fokker size `< 7` pass the criterion outright |
| `fokkerUpdatedOpenReduces_not_closedNodeTwoVars` | none of the 16 terms of `fokkerUpdatedOpenCerts` does, so the criterion and the "β-reduces *to* a two-name term" criterion of `BetaReducesToNamable.lean` are complementary |

All of these are kernel computations (`decide`) except the two statistics over
`terms_fokker_lt_7` (`terms_fokker_lt_7_length`,
`terms_fokker_lt_7_closedNodeTwoVars_count`), which use `native_decide` because
the enumeration `terms_fokker_lt_7` is defined by a well-founded recursion that
the kernel does not reduce.

## Building

```
lake exe cache get   # Mathlib cache, pulled in via cslib
lake build
lake exe fokker_challenge
lake exe blc
```

The `native_decide` steps in the two classification theorems are memory hungry;
building `FokkerChallenge.NativeEnum` is the slowest part of the build.

## Independent checking

The two headline theorems are packaged for
[Comparator](https://github.com/leanprover/comparator), which checks that a
solution proves the stated theorems, uses only permitted axioms, and is accepted
by the Lean kernel replayed from an export file: see `Challenge.lean`,
`Solution.lean`, `comparator-config.json` and [`COMPARATOR.md`](COMPARATOR.md).

We use `native_decide` because `decide` can cause an OutOfMemoryError (OOM).

## Next step

1. Formalize only 3 basis of fokker size 7
2. Formalize only 3 basis of blc size 26
3. https://github.com/awesome-lambda-calculus/Fokker_challenge/issues/6

### Related papers

Only 3 papers discuss single basis: [^1] [^2] [^3] 

There are also some online discussion: [^6] [^7] [^8]


### References

[^1]: Legrand, Remi. "A basis result in combinatory logic." The Journal of symbolic logic 53.4 (1988): 1224-1226.
[^2]: Statman, Richard. "Combinators hereditarily of order two." (1988).
[^3]: Rick Statman. **Two Variables Are Not Enough**. In *Proceedings of the 9th Italian Conference on Theoretical Computer Science (ICTCS 2005)*, Lecture Notes in Computer Science, vol. 3701, pp. 406–409, Springer, 2005.  [DOI](https://doi.org/10.1007/11560586_32)
[^4]: https://github.com/tromp/AIT/blob/master/Bases.lhs
[^5]: https://en.wikipedia.org/wiki/Combinatory_logic
[^6]: https://esolangs.org/wiki/Closed_lambda_term
[^7]: https://mathoverflow.net/questions/415334/do-combinatory-logic-bases-need-a-function-of-3-variables#
[^8]: https://cstheory.stackexchange.com/questions/36276/incomplete-basis-of-combinators
[^9]: https://tromp.github.io/cl/Binary_lambda_calculus.html
[^10]: http://frox25.no-ip.org/~mtve/wiki/LambdaOnePoint.html 
[^11]: https://github.com/tromp/AIT/blob/master/ait/minbase.lam
