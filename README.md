# Mean value of the Erdős–Hooley Delta-function

Lean 4 / Mathlib formalization of R. de la Bretèche and
G. Tenenbaum, [*Note on the mean value of the Erdős–Hooley Delta-function*](https://arxiv.org/pdf/2309.03958v14).

**Theorems 1.1 and 1.2, the polynomial consequence (1.7), Propositions 2.1–2.2,
Lemma 3.1, and the exact Parseval identity (2.6) are proved.**
`paper_main_results` in `FullPaper.lean` assembles all eight named targets (in the
`BretecheTenenbaumMean` namespace). There are no additional analytic hypotheses,
`axiom` declarations, or admitted proofs in the Solution development.
The separate Palomar Challenge contains ten deliberate statement-only proof holes. The lower tail uses the quantified
range justified by the paper’s proof; see the source corrections in
[BLUEPRINT.md](BLUEPRINT.md#source-issues-resolved-explicitly).

The proved main result, `theoremOne : TheoremOne`, is

\[
\sum_{1\le n\le x}\Delta(n)\ll x(\log\log x)^{5/2}.
\]

[BLUEPRINT.md](BLUEPRINT.md) maps the paper to the Lean modules and records the
source issues. Provenance and the Tau Ceti reuse survey are in
[paper/SOURCES.md](paper/SOURCES.md).

## Build

Lean and Mathlib are pinned to **v4.35.0**. The other direct Lake dependencies,
pinned in `lakefile.toml`, are
[Nair–Tenenbaum](https://github.com/jasondavies/nair-tenenbaum-short-sums), which
supplies the short-sum theorem and the Selberg sieve, and
[Tau Ceti v4.35.0](https://github.com/TauCetiProject/TauCeti/releases/tag/v4.35.0),
which supplies Dedekind-zeta continuation and nonvanishing. The root Mathlib pin
overrides Tau Ceti's own Mathlib revision. The selected `StrongPNT` source closure
is vendored; see [its provenance](vendor/strong-pnt/README.md). Dependency file
hashes are recorded in [paper/](paper/).

```sh
lake exe cache get
bash scripts/check.sh
```

The audit checks every declaration in every project and vendored source module and
in the imported Nair–Tenenbaum and Tau Ceti modules, including private and generated
declarations. It does not import the independent Challenge. It permits only
`propext`, `Classical.choice`, and `Quot.sound`, and an omitted source module fails it.

## Conventions

`divisorWindow n u` counts divisors with `u < log d ≤ u+1`.
`hooleyDelta n` is its natural-number maximum, proved to be attained.
`delta n u` is the real-valued window count, `tau n` the real-valued divisor
count, and `moment q n` its Lebesgue integral on ℝ. The analytic lemmas use
`q ≥ 1`; the value at order zero is not an analytic zeroth moment.
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
  `propositionTwoOneLower` gives `c/T ≤ P_x(M₂/τ > T)` for `T≥3` and
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

[PALOMAR.md](PALOMAR.md) records the prepared submission fields and local checks.
The independent [Challenge](Challenge.lean) states all ten compared results using
only Mathlib; [Solution](Solution.lean) imports their proofs.
[formalization.yaml](formalization.yaml) records authorship, AI assistance,
source fidelity, licenses, and the absence of independent human review.

```sh
ruby scripts/validate-formalization.rb
python3 scripts/check-lean-sources.py
python3 scripts/check-palomar.py
bash scripts/check.sh
bash scripts/verify-comparator.sh
```

Comparator requires Linux with working bubblewrap user/network namespaces and
uses the bundled Lean, NanoDa and con-ron checkers. The root license is Apache-2.0;
reused source notices remain in their vendor directories and the pinned
dependency repositories.
After committing and pushing a clean public snapshot, submit its full SHA at
https://submit.palomar-registry.org/ following the
[current instructions](https://palomar-registry.org/how-to-submit).
