# Mean value of the Erdős–Hooley Delta-function

Lean 4 / Mathlib formalization of R. de la Bretèche and
G. Tenenbaum, [*Note on the mean value of the Erdős–Hooley Delta-function*](https://arxiv.org/pdf/2309.03958v14).

The Erdős–Hooley function Δ(n) is the largest number of divisors of n whose
logarithms lie in an interval of length one. The main result, Theorem 1.1, bounds
its average: for sufficiently large x,

$$
\sum_{1\le n\le x}\Delta(n)\ll x(\log\log x)^{5/2}.
$$

**Theorems 1.1 and 1.2, the polynomial consequence (1.7), Propositions 2.1–2.2,
both forms of Lemma 3.1, and the exact Parseval identity (2.6) have Lean proofs.**
The lower bound in Proposition 2.1 requires x to be sufficiently large depending
on the tail parameter T. This dependence is explicit in the formalization;
the unrestricted uniform reading is false. See the
[source corrections](BLUEPRINT.md#source-issues-resolved-explicitly).

[`paper_main_results`](BretecheTenenbaumMean/FullPaper.lean) combines eight
statements: the two main theorems, the polynomial bound, both sides of
Proposition 2.1, Proposition 2.2, and both forms of Lemma 3.1.
[`GlobalParseval.lean`](BretecheTenenbaumMean/GlobalParseval.lean) supplies the
Parseval identity and absolute integrability, giving ten results checked by
Comparator. The proof development has no admitted proofs, new axioms, or
additional analytic hypotheses. The separate [Challenge](Challenge.lean)
contains ten intentional proof holes used to check the [Solution](Solution.lean).

[BLUEPRINT.md](BLUEPRINT.md) maps the paper to the Lean modules and records the
source issues. Provenance and the Tau Ceti reuse survey are in
[paper/SOURCES.md](paper/SOURCES.md).

## Build

With Elan, Git, and Python 3.11 or later installed, run from the repository root:

```sh
lake exe cache get
bash scripts/check.sh
```

The first command downloads Mathlib's compiled cache. The second builds the
project, verifies dependency source hashes, and audits the proof axioms.
The audit checks every declaration in every project and vendored source module and
in the imported Nair–Tenenbaum and Tau Ceti modules, including private and generated
declarations. It does not import the independent Challenge. It permits only
`propext`, `Classical.choice`, and `Quot.sound`, and an omitted source module fails it.

Lean and Mathlib are pinned to **v4.35.0**. Dependencies are recorded in
[lakefile.toml](lakefile.toml) and [lake-manifest.json](lake-manifest.json):

| Library | Use | Integration |
|---|---|---|
| [Nair–Tenenbaum](https://github.com/jasondavies/nair-tenenbaum-short-sums) | Polynomial short sums and the Selberg sieve | Pinned Git commit |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti/releases/tag/v4.35.0) | Dedekind-zeta continuation and nonvanishing | Pinned v4.35.0 release commit |
| [StrongPNT](vendor/strong-pnt/README.md) | Prime number theorem estimates | Vendored subset adapted to Lean's module system |

The root Mathlib pin overrides Tau Ceti's own Mathlib revision; this combination
is checked by the build and axiom audit. Dependency source hashes and provenance
are recorded in [paper/](paper/) and [vendor/strong-pnt/](vendor/strong-pnt/).

## Conventions

`divisorWindow n u` counts divisors with `u < log d ≤ u+1`.
`hooleyDelta n` is its natural-number maximum, proved to be attained.
`delta n u` is the real-valued window count, `tau n` the real-valued divisor
count, and `moment q n` the Lebesgue integral of `delta n u ^ q` over ℝ.
The analytic lemmas use `q ≥ 1`; the value at order zero is not an analytic zeroth moment.
Zero has no divisors and `hooleyDelta 0 = 0`.

The finite probability support comprises all squarefree integers with prime
factors below `x`, including integers larger than `x`. The normalizer and
expectations match §2.1, and normalization is proved by a finite Euler product.

## Proof structure

- **§2, Propositions 2.1 upper and 2.2:** the moment, frequency and good-set
  arguments are proved once in `WeightedModel`, for any multiplicative weight
  satisfying `PrimeEstimates`. `UnitWeight` proves that structure for the constant
  weight, which recovers the paper's model exactly.
- **Theorem 1.1:** `hooleyDelta_expectation_bound` gives `E_x(Δ) ≪ (log log x)^(5/2)`.
  The von Mangoldt identity and Chebyshev estimates remove logarithmic averaging,
  and a square-times-squarefree decomposition reaches all integers.
- **Theorem 1.2:** interval convolution and Cauchy–Schwarz prove
  `Δ(rs)² ≤ 4 M₂(r)M₂(s)` for the upper bound. Multiples and a truncated `3^ω`
  Euler product give `sum τ(n)² ≫ x(log x)³`, and a pigeonhole inequality gives
  the lower bound.
- **Lemma 3.1 and the lower tail:** `lemmaThreeOne` and `lemmaThreeOneCentral` use
  distinct-prime products, Mertens and two-sided Stirling bounds.
  `propositionTwoOneLower_quantitative` gives `c/T ≤ P_x(M₂/τ > T)` for `T≥3` and
  `x≥exp((B*T)^4)`.
- **Parseval (2.6):** `moment_two_parseval_sine` has the exact `1/(2π)` factor,
  with absolute integrability from Fourier inversion of the triangular overlap
  kernel. The literal sine quotient differs from the sinc version only at a null
  singleton.
- **Polynomial consequence (1.7):** `polynomialMeanBound`, in
  `PolynomialPrimeCosine.lean`, applies `WeightedModel` to polynomial root weights
  through the Nair–Tenenbaum short-sum theorem. `polynomialPrimeCosineEstimates`
  supplies the prime estimates using Kummer–Dedekind and Dedekind-zeta bounds.

## Palomar submission

[PALOMAR.md](PALOMAR.md) records the submission instructions and verification results.
The independent [Challenge](Challenge.lean) states all ten compared results using
only Mathlib; [Solution](Solution.lean) imports their proofs.
[formalization.yaml](formalization.yaml) records authorship, AI assistance,
source fidelity, licenses, and the absence of independent human review.
For the complete local submission checks, also install Ruby and bubblewrap, then run:

```sh
ruby scripts/validate-formalization.rb
python3 scripts/check-lean-sources.py
python3 scripts/check-palomar.py
bash scripts/check.sh
bash scripts/verify-comparator.sh
```

Comparator requires Linux with working bubblewrap user/network namespaces and
uses the Lean, NanoDa and con-ron checkers bundled with the pinned Lean toolchain.
The root license is [Apache-2.0](LICENSE);
reused source notices remain in their vendor directories and the pinned
dependency repositories.
After committing and pushing a clean public snapshot, submit its full SHA at
https://submit.palomar-registry.org/ following the
[current instructions](https://palomar-registry.org/how-to-submit).
