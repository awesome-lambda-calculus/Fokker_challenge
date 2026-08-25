# The 14 terms of `undecided_terms.json` that are still open

`FokkerChallenge/Undecided64.lean` lists the 64 terms of `undecided_terms.json`
as `undecidedTerms` and proves that all of them satisfying the Boolean test
`covered` (namely `rigid t || tailOk t`) are not one-point bases
(`undecided_covered_not_basis`).  Exactly 50 of the 64 pass that test
(`undecided_covered_count`).

The 14 terms that are **not** settled by this development are collected in
`undecidedTermsRemaining`:

```
λλλλ1(00)2   λλλλ1002    λλλλ2(00)1   λλλλ2001
λλλλ1(02)0   λλλλ1(20)0  λλλλ2(01)0   λλλλ2(10)0
λλλλ1020     λλλλ2010
λλλ0(λ102)   λλλ0(λ201)
λλ0(λλ102)   λλ0(λλ201)
```

Nothing below is machine-checked; it is a record of exploratory work, kept only
as a starting point for a future attempt.

## Why the two deciders miss them

Both deciders work the same way: they exhibit a Boolean predicate that

* holds of the term,
* is preserved by β- and η-steps and by application, and
* fails for `K = λx.λy.x`,

so that no applicative combination of the term can βη-reduce to `K`.

`rigid` asks that the head of every abstraction block be that block's innermost
binder; `tailOk` asks that every abstraction block `λ x₁ … x_s. z M₁ … M_k` have
`k ≥ 1` arguments with a **non-variable** last argument `M_k` (which in
particular rules out η-redexes, so that η-preservation is vacuous).

Each of the 14 terms above has a block whose last argument is a bound variable
and whose head is not the innermost binder, so both tests fail.  All 14 also
share the feature that their outermost binder is vacuous: each is of the form
`λw. B` with `B` closed.

## Invariant candidates that were tried and refuted

Exploratory search produced explicit counterexamples (β- or η-steps leaving the
class) for each of the following strengthenings/weakenings of `tailOk`.  In each
case the predicate holds of some of the 14 terms but is not reduction-invariant.

* every binder is used (λI); vacuous abstraction ⇒ closed body; vacuous
  abstraction ⇒ closed or applicative body;
* "no block body is a variable" (β-preserved, but not η-preserved);
* "no η-redex, and every block body is an application";
* "the last argument of each block is a non-variable, or is the innermost binder
  and occurs also in the function part" (η-preserved, but not β-preserved:
  a β-step can erase the occurrence and create an η-redex);
* the same condition relaxed to "the last argument is a non-variable, or a
  binder of the same block" (not β-preserved: substitution can replace such a
  binder by a variable coming from the surrounding context);
* "vacuous binders of a block form an outer prefix" (holds of all 14 terms, and
  fails for `K` and for every η-expansion of `K`, but a β-step that erases the
  last occurrence of an inner binder leaves the class).

The one candidate that survived several hundred thousand random β-steps is

> `G(M)` := the η-normal form of `M` has the property that every abstraction
> block's body is an application whose last argument is either a non-variable or
> the innermost binder occurring also in the function part.

`G` fails for `K` and holds for the six terms of the second row above, so
proving that `G` is preserved by β would settle those six.  Because `G`-terms
are η-normal, η-preservation would come from confluence of η, and the β-case
could be reduced — via the commutation of β and η already available in the
project — to the single statement

> if `M` satisfies the condition above and `M →β N`, then `N` η-reduces to a
> term satisfying it.

This was not attempted here.  The other eight terms are not covered by `G`
either, and no candidate invariant found so far covers them.
