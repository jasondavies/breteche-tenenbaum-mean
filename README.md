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

The scope also includes Propositions 2.1–2.2, Lemma 3.1,
the polynomial consequence (1.7), and their necessary analytic inputs.
[BLUEPRINT.md](BLUEPRINT.md) tracks the proof obligations and source issues.

## Build

Lean is pinned to **4.35.0** and Mathlib to **v4.35.0**, commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Other direct Lake dependencies are
[Nair–Tenenbaum](https://github.com/jasondavies/nair-tenenbaum-short-sums), pinned to
`0f778ee8366de1204c118e212264ef096ec82b49`, and
[Tau Ceti v4.35.0](https://github.com/TauCetiProject/TauCeti/releases/tag/v4.35.0),
pinned to `1f9b4414105d86e487a4ac4c3d3397076a44d0d2`. The selected `StrongPNT` source
closure is vendored locally; see [its provenance](vendor/strong-pnt/README.md).
There are no sibling-directory dependencies. The 109-module Tau Ceti
closure used for Dedekind-zeta continuation and nonvanishing is imported
unchanged from the release; see [its provenance](paper/TAU_CETI_SOURCES.json).
The root Mathlib pin takes precedence over the release's own Mathlib revision;
the required closure is verified against our pin. Six Selberg-sieve
source files are adapted locally from the Nair–Tenenbaum project; their
[snapshot hashes](paper/SIEVE_SOURCES.json) are recorded. The 127 modules used
from its proved polynomial short-sum theorem are imported from the pinned Git
dependency; [file hashes](paper/NAIR_TENENBAUM_SOURCES.json) verify that they
match the previously vendored sources exactly.

```sh
lake exe cache get
bash scripts/check.sh
```

The audit checks every proved declaration in every project and vendored source module,
plus all 127 imported Nair–Tenenbaum and 109 Tau Ceti modules, including
private and generated declarations; it does not import the independent Challenge. It permits only `propext`,
`Classical.choice`, and `Quot.sound`. An omitted source module fails the audit.
The completion certificate also checks that each named target has a proof.
The prepared project build comprises 9,534 jobs; the audit checks 7,731 declarations.

During development the example project's cached packages were copied into the
ignored `.lake` directory. The tracked configuration uses pinned Git sources.

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

The checked material includes the full moment recurrence (1.4), the maximum
bound `Δ(n)^q ≤ 2^q M_q(n)`, normalized-moment monotonicity on squarefree
integers, divisor closure of the good sets, and the compact-frequency estimate
(2.7) with explicit constant `π²/2`. The latter has a direct Fejér-kernel proof.
The analytic foundation now also includes strong Mertens estimates, uniform
Euler-product bounds, `E_x(τ^k) ≪_k (log x)^(2^k−1)`, and the uniform prime-sum
estimates (2.9)–(2.12). The initial-frequency mean and the small-prime-weighted
frequency mean used in §2.2 are bounded uniformly, with strict cutoff endpoints
handled explicitly. The intermediate-frequency exceptional bound is proved
with `K = 16 + 1/δ`; the uniform factorial and fixed-prime-count bounds needed
for the high-frequency argument are also checked. The three-range prime
estimate, exact dyadic good-set decomposition, and full good-set two-frequency
integrand bound are proved, including the geometric layer saving and the
regularized diagonal kernel. Both frequency integrations and the resulting
high-frequency second-moment bound are now proved. Together with the initial
frequency estimate, they give `P_x(n ∈ E_T, M₂(n)/τ(n) > T) ≪δ 1/T` uniformly
for `x ≥ 2`, `T > 1`. The independent bound `P_x(E_Tᶜ) ≪δ 1/T` is also
proved for `0 < δ ≤ 10⁻⁶`, using refined Poisson tails, exact small-prime
marginals, a logarithmic grid, and a uniform Gaussian sum. Combining these
bounds proves **Proposition 2.1's upper estimate (2.4)**, implemented as
`propositionTwoOneUpper`. The lower estimate is also proved, as described below.

For Proposition 2.2, the largest-prime recurrence and its finite iteration
(2.15), the product-moment bound (2.17), the exceptional midpoint comparison,
and the penalty integral in (2.19) are proved. The prime-averaging input is
also proved, using a short-interval Selberg sieve and an exact divisor-tuple
expansion. Smoothing and finite prime-tail integration now give the integral
recursion. Its fourth-root error is bounded by `C^q q! T^(q−2)` and absorbed
using the admissible thresholds, proving (2.16). The square-root divisor-count
average proves (2.18) and the `q=3` base case. Strong induction, including the
exceptional `q=4,j=2` term, now proves **Proposition 2.2**, implemented as
`propositionTwoTwo`. The explicit threshold sequence is verified with the
paper’s exact constant `2π²/3`. Summing the moment exceptions, choosing the
floor moment order, and summing the resulting tail now prove
`hooleyDelta_expectation_bound`: `E_x(Δ) ≪ (log log x)^(5/2)` for
`x ≥ exp(exp 4)`. The arithmetic transfer is also proved, completing
**Theorem 1.1** as `theoremOne`. It uses the von Mangoldt identity and
Chebyshev estimates to remove logarithmic averaging, then the decomposition
into a square times a squarefree integer. The square-factor contribution is
bounded explicitly by `(π²/6)³`.

For Theorem 1.2, interval convolution and Cauchy–Schwarz prove
`Δ(rs)² ≤ 4 M₂(r)M₂(s)` without coprimality. Averaging over divisor
factorizations and using the normalized-second-moment bound gives
`E_x(Δ²) ≪ log x · log²(1+log x)`. A squared-divisor Chebyshev bound and
an explicit bound `(π²/6)^16` for the square-factor sum complete the transfer
to all integers. **The upper half of Theorem 1.2**, `theoremTwo_upper`, is
proved on the full printed range `x ≥ 3`. The lower bound is now also proved:
counting multiples and truncating the `3^ω` Euler product gives
`sum τ(n)² ≫ x(log x)³`; the pigeonhole inequality then supplies
`sum Δ(n)² ≫ x log x`. Both bounds are assembled in **`theoremTwo : TheoremTwo`**.
The full introductory moment interpolation and the pair-count comparisons
`M₂(n) ≤ T(n,0) ≤ 4 M₂(n)` are also proved.

**Lemma 3.1 is proved**, including both (3.1) (`lemmaThreeOne`) and its
central-window consequence (3.2) (`lemmaThreeOneCentral`). The proof bounds
products of distinct primes by removing a fixed initial prime segment and
controlling repeated-prime contributions. Mertens' estimate and two-sided
Stirling bounds give constants uniform in the stated ranges. No additional
library dependency is needed.

**The lower tail in Proposition 2.1 is proved** as `propositionTwoOneLower`.
Its quantitative form gives absolute `c,B>0` such that
`c/T ≤ P_x(M₂/τ > T)` for `T≥3` and `x≥exp((B*T)^4)`.
The proof includes exact joint prime-count distributions, geometric decay of
scale overlaps, finite inclusion–exclusion, the tilted size-exception bound,
and integer rounding. It retains the good part of each event locally before
using the second-moment pigeonhole bound.

**The global Parseval identity (2.6) is proved** as `moment_two_parseval_sine`,
with the exact `1/(2π)` factor and absolute integrability. Fourier inversion
of the triangular overlap kernel supplies the cosine identity for each
divisor pair. The continuous sinc version is also proved; the literal sine
quotient differs only at a null singleton.

The polynomial consequence (1.7) is proved as `polynomialMeanBound`, in
`PolynomialPrimeCosine.lean`.
The proved short-sum theorem is connected to the project’s definition of Δ.
For general nonnegative multiplicative weights, normalization, Euler products,
small-prime marginals, Markov’s inequality, and the Fourier comparison are
proved. Polynomial root counts define such a weight by CRT, and their
weighted normalizer cancels against the sieve product. Discriminant bounds
and a convergent divisor-power sum remove square factors. The resulting
`polynomial_short_sum_weighted_bound` bounds short sums directly by the
weighted expectation at `floor(x)+1`, for irreducible polynomials with no
fixed prime divisor. The Fourier estimates have explicit weighted prime-sum
hypotheses. The fixed-prime-divisor reduction is now proved as
`polynomialMeanBound_of_noFixedPrime`: finitely many normalized progression
polynomials have no fixed prime divisors and retain irreducibility. Constant
polynomials and the zero-quotient terms are handled explicitly. The prime-sum input for polynomial root counts is proved below.
`polynomialMeanBound_of_weighted_expectation` now connects the eventual
weighted expectation bound to the full printed polynomial statement, including
short-interval summation and the bounded initial range. Weighted prime-count
tails and the good-set exceptional estimate are also proved under explicit
bounded-prime-weight and weighted Mertens hypotheses; zero prime mean is
handled separately. The explicit `WeightedModel.PrimeEstimates` structure
now supplies the analytic hypotheses for weighted normalizer and divisor-moment
bounds and the complete weighted frequency and moment arguments.
`WeightedModel.hooleyDelta_expectation_bound` now proves
`E_{w,x}(Δ) ≪ (log log x)^(5/2)` from `PrimeEstimates w`.
This includes the high-frequency second moment, weighted Proposition 2.2,
simultaneous moment control, and the final tail summation.
`polynomialMeanBound_of_prime_estimates` connects it to the full printed
polynomial statement. `polynomialPrimeCosineEstimates` proves its arithmetic
input for every irreducible polynomial without a fixed prime divisor.
The proof constructs an integral primitive generator even for nonmonic
polynomials, applies Mathlib’s Kummer–Dedekind correspondence, and bounds
higher residue degrees by a convergent reciprocal-square series. The selected
Dedekind-zeta results give the smoothed logarithmic profile; finite exceptional
primes and removal of smoothing cost bounded amounts. The initial range
`2 ≤ x ≤ e` is handled explicitly. No new Tau Ceti modules were needed for
these arithmetic and unsmoothing steps.

Provenance and the Tau Ceti reuse survey are in [paper/SOURCES.md](paper/SOURCES.md).

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
