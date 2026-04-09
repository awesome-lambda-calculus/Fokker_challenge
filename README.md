# Fokker_challenge

The currently known smallest one-point bases[^5] for untyped lambda calculus, measured by Fokker size, have size 7.
There are three such one-point bases of Fokker size 7.
The first one (λx.λy.λz. y (λt.z) (x z)) was discovered by Meredith in 1963[^11]. Another two (λx.λy.λz.y z(x(λt.z))) (λx.λy.λz.x z(y(λt.z))) were found in 2022 by John Tromp[^4] and Mtv Europe[^10].

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

Currently we focus on normal forms.
When all normal forms are checked, we will turn to non normal forms.


## What we are going to do 
There are still 886 non-trival cases undecided:

```
$ lake exe fokker_challenge

886 undecided
```

We might prove them one by one, or discover new deciders.

See issues to startup

## Next step

1. Verify "Two vars are not enough", which will cover 78 terms
2. Filter terms always terminate
3. Filter terms always diverge
4. Find more deciders
5. Not sure

See [our website](https://awesome-lambda-calculus.github.io/Fokker_challenge) for details.


## 🤝 Contributing

This is a collaborative proof project — contributions are highly welcome!

Ways to contribute:

- Prove one or more of the undecided terms
- Improve automated deciders (termination, divergence, normalization, etc.)
- Write new tactics or lemmas
- Improve documentation and visualizations
- Review formalizations

See the open issues for starter tasks.
We especially welcome people interested in:

- Lambda calculus / Combinatory logic
- Automated theorem proving
- AI-assisted formal mathematics

### Ai usage

This project is quite suitable for AI-Driven Autonomous Proof.

### Related papers

Only 3 papers discuss single basis: [^1] [^2] [^3] 

There are also some online discussion: [^6] [^7] [^8]


## Encoding

We have thousands of terms that require individual analysis, so an intuitive encoding scheme is necessary.

Based on BLC[^9], our encoding algorithm is

```
encode(λM) = L encode(M)

encode(M N) = A encode(M) encode(N)

encode(i) = i
```

```
cd rust-scripts
cargo run --bin encode "λλ2 (1 2)"                                                                                                                                                     (base)

def Term_LLA2A12: Term String := .abs (.abs (.app (.bvar 2) (.app (.bvar 1) (.bvar 2))))

theorem LLA2A12_is_not_basis : not_basis Term_LLA2A12 := by sorry
```

```
# Well encoded term results []
lake exe decode LA0L1                                                                                                                                                                (base)

decoded: (λ0 (λ1), [])
```

```
# Irrelevant suffixes will be ignored
lake exe decode LA0L1_is_not_basis                                                                                                                                                   (base)

decoded: (λ0 (λ1), [_, I, S, _, N, O, T, _, B, A, S, I, S])
```

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

