# Source snapshot

R. de la Bretèche and G. Tenenbaum, *Note on the mean value of the
Erdős–Hooley Delta-function*, arXiv:2309.03958v14 (13 February 2025).

- [PDF](https://arxiv.org/pdf/2309.03958v14)
- [TeX archive](https://arxiv.org/src/2309.03958v14)
- PDF SHA-256: `7d7f912c2220df8bd84580dfa536adf42a7bfcedb8990506a276fe3d49a478b2`
- TeX archive SHA-256: `4e53b10a986dbc282b18ec8beb52407c94505b016c1452575370a539ac68c49a`

The downloads and extracted TeX are local, ignored working files. The archive
contains `MeanDeltaUp.tex`, `itenn.tex`, and `option_keys.tex`. Consult the TeX
for indices and radicals: PDF text extraction drops the square root in the
definition `ξ = √(log₂ x)` in §3, for example.

The user requested the structure of `../iwaniec-linear-sieve` as an example.
This project follows its Lean module convention and standard-axiom audit.

`BretecheTenenbaumMean/Delta.lean` adapts the local
`../nair-tenenbaum/NairTenenbaum/Hooley.lean` (snapshot SHA-256
`26cc0b7d494c51378b617eca86607114e06ac26504ecac3ccf5ec373a41a32e7`).
Its namespace and documentation were changed. That local development is now
named `../nair-tenenbaum-short-sums`; this project uses its published Git
dependency, not a sibling-directory path. The audit script is adapted from that project,
which in turn follows the Iwaniec project.

## Tau Ceti search

Inspected [Tau Ceti](https://taucetiproject.org/), source commit
[`ea7e54cf967c2ab502c7e69bf69501e5a3ae3130`](https://github.com/TauCetiProject/TauCeti/tree/ea7e54cf967c2ab502c7e69bf69501e5a3ae3130),
on 29 October 2026. Searched actual Lean sources, not just roadmap statements.

Potentially related files:

- `TauCeti/NumberTheory/AbelSummation.lean`: weighted Abel summation and
  convergence under a supplied bound on partial sums.
- `TauCeti/NumberTheory/LSeries/WienerIkehara/Variants.lean`: Tauberian
  conclusions under supplied Dirichlet-series and boundary hypotheses.
- `TauCeti/NumberTheory/TsumDivisorsAntidiagonal.lean`: regrouping convergent
  double series by products.
- `TauCeti/Analysis/Fourier/L2Multiplier.lean`: general Fourier multipliers
  built on Mathlib's Plancherel theorem.
- `TauCeti/NumberTheory/ArithmeticDirichletSeries/EulerProduct/Basic.lean`:
  Euler products for arithmetic functions on ideals in number fields.

No implementation of Hooley's Δ-function, the Montgomery–Wirsing comparison,
or the specific probabilistic estimates needed here was found. The twisted
divisor sums in `ArithmeticFunction/TwistedDivisorSum.lean` involve Dirichlet
characters and integral exponents, so they do not directly supply `τ(n,θ)`.
The snapshot uses Lean 4.36.0-rc1; this project uses 4.35.0.

No Tau Ceti code is used for the unweighted results. The polynomial input
imports the Dedekind-zeta closure, as described below.

## Prime number theorem and Mertens estimates

The user authorized vendoring `StrongPNT` from
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd).
Current upstream HEAD was downloaded on 29 October 2026 and verified to be
`127b50e33f6033e2147921167a117af96d9ba4ea`, with Lean **4.35.0**. This is exactly
the upstream revision used by the Iwaniec example's source snapshot.

The 14 mathematical files and one local blueprint-annotation shim are in
`vendor/strong-pnt`. All original upstream file hashes were checked against
the downloaded checkout. The example's module/import adaptation is retained;
this is not a Lean-version port. No additional remote Lake package is needed.
See [the vendor README](../vendor/strong-pnt/README.md), licenses, and exact
source inventory for the complete provenance.

`PrimeSums/Error.lean` and `PrimeSums/Mertens.lean` adapt the example's proofs,
with source hashes in that inventory. The telescoping reciprocal lemma in
`PrimeSums/Product.lean` also follows its `PrimeSums/Product.lean` proof.
The strict-cutoff, positive Euler-product and cosine-weight specializations
are local proofs, checked against the same standard-axiom allowlist.

## Good-set exceptional estimate input

Inspected Koukoulopoulos–Tao, *An upper bound on the mean value of the
Erdős–Hooley Delta function*, [arXiv:2306.08615v2](https://arxiv.org/html/2306.08615v2),
§4, Proposition 4.1 and its proof, on 29 October 2026. This is the preprint
numbering of the result cited as Proposition 5.1 in the published paper
([DOI](https://doi.org/10.1112/plms.12572)). No Lean code or additional dependency
was imported from this source.

The formalization uses the exact `log(3y)` envelope of the target paper.
A non-strict divisor threshold `tau(n) ≥ R` uses the natural ceiling of
`log R/log 2`; the preprint's displayed equivalence with a floor is not
used. Its subsequent expansion near the critical scale is replaced by a
quantitative entropy remainder valid at the center itself. The logarithmic-grid sum is now proved by comparison with a widened
Gaussian on adjacent square-root intervals. This completes the formal
proof of (2.1) for `0 < δ ≤ 10⁻⁶`, with all rounding and Mertens errors
retained, and hence the upper bound (2.4) of Proposition 2.1.

## Selberg sieve and prime averaging

On 30 October 2026, inspected the prime-averaging argument in
[Koukoulopoulos–Tao, arXiv:2306.08615v2](https://arxiv.org/html/2306.08615v2),
Lemma 3.2 and the proof of (5.8). This corresponds to the published argument
cited in §2.3 of the target paper. The local proof retains the exact tuple
overlap lengths, including endpoint conventions, and proves the short-interval
input by Selberg's sieve.

The Selberg sieve comes from the pinned Nair–Tenenbaum dependency:
`NairTenenbaum.SelbergWeights`, `SelbergDenominator`, `SelbergCoefficientBounds`,
`SelbergRemainder`, `PrimeLogSums` and `PrimeFactorBounds` construct optimized
Selberg coefficients, bound the denominator and remainder, and provide two
elementary prime-factor and prime-sum utilities. A former local copy differed
only in namespace, imports and a provenance comment, so it was removed.

`Sieve/Interval.lean`, `PrimeSums/ShortIntervals.lean`, `TupleWindows.lean`
and `PrimeWindowAverage.lean` are local applications and proofs. They give
an unconditional mixed-moment prime-average bound, including the `2^j`
coherent-tuple error and the full range `y ≥ 1`.

## Follow-up for the polynomial consequence

After completing (2.6), re-inspection of the same Tau Ceti snapshot found
substantial arithmetic input relevant specifically to (1.7):

- `TauCeti/NumberTheory/NumberField/DedekindZeta.lean` proves ideal-count
  asymptotics, meromorphic continuation across `Re s=1`, and nonvanishing
  on that line away from the pole. Its local import cone contains 112
  Tau Ceti modules (approximately 1.23 MB of source).
- `TauCeti/NumberTheory/LFunctions/PrimeIdealBoundary.lean` packages the
  resulting von Mangoldt boundary data. Its local import cone contains
  201 modules (approximately 2.17 MB of source).

These are concrete proof sources rather than roadmap entries. The smaller
Dedekind-zeta closure was initially adapted to Lean 4.35.0 and is now
imported unchanged from Tau Ceti's v4.35.0 release, as described below. Its
application to the full polynomial target is complete. Mathlib supplies
Kummer–Dedekind; local proofs connect general polynomial root counts to
prime-norm ideals and remove the exponential smoothing. The argument uses
Dedekind-zeta bounds and smoothed reciprocal-prime sums, avoiding a new
strong prime ideal theorem. `polynomialPrimeCosineEstimates` proves the
arithmetic input and `polynomialMeanBound` establishes (1.7).
The earlier no-reuse decision for the unweighted main
theorems remains unchanged. Only the selected number-field closure is imported.

At the time of the original snapshot, the sibling `../nair-tenenbaum` tree proved
`exists_hooleyPolynomialSum_root_bound`, reducing polynomial short sums to
a sieve product and a root-weighted Hooley mean. Its hypotheses include a
nonconstant polynomial with no fixed prime divisor; its dependency cone is
127 local modules (approximately 0.79 MB). This updates the earlier observation
that its main short-sum theorem was unfinished. The weighted mean and
polynomial Euler-product inputs were unfinished in that snapshot.
The 127-file dependency cone of `NairTenenbaum.HooleyShortSum` was initially
vendored byte-for-byte. It is now imported from
[nair-tenenbaum-short-sums](https://github.com/jasondavies/nair-tenenbaum-short-sums)
at commit `0f778ee8366de1204c118e212264ef096ec82b49`, with no mathematical
source changes. Every one of the 127 source hashes matches the former snapshot;
the revision and hashes are recorded in
[NAIR_TENENBAUM_SOURCES.json](NAIR_TENENBAUM_SOURCES.json).
All declarations in this cone, including private and generated declarations,
are included in the project’s standard-axiom audit. Mathlib, Nair–Tenenbaum,
and Tau Ceti are the direct remote Lake dependencies. Nair–Tenenbaum retains its upstream
Apache-2.0 license and depends only on the same pinned Mathlib release.
Its short-sum input specializes Corollary 3, proved from Theorem 1 of
M. Nair and G. Tenenbaum, *Short sums of certain arithmetic functions*,
Acta Mathematica 180 (1998), 119–144, DOI `10.1007/BF02392880`.
`PolynomialShortSum` provides checked bridges for
the Delta function, the short interval sum, and the root-weighted sum.


## Selected Tau Ceti closure for the polynomial input

The original 112-module vendored snapshot and its six compatibility patches
have been replaced by the unmodified
[Tau Ceti v4.35.0 release](https://github.com/TauCetiProject/TauCeti/releases/tag/v4.35.0),
pinned to commit `1f9b4414105d86e487a4ac4c3d3397076a44d0d2`.
The annotated tag object is `335f3574f9b1d396d8458e67b7a4d02764edcdf2`;
the Lake configuration pins the commit, not the movable tag name.
The project's direct imports have a 109-module transitive Tau Ceti closure
in this release. Source hashes are recorded in `TAU_CETI_SOURCES.json`.
The release supplies the ideal-count power saving, continuation across
`Re s=1`, and nonvanishing on that line. The larger prime-ideal boundary
and Tauberian modules are not imported.

The release targets Lean 4.35.0 but records Mathlib revision
`074063781836922cb02701cd12943c9f51731afa`. The root project retains Mathlib
v4.35.0 at `56a005855ea17e0b0958f73ec801ae140b0a1679`; the required closure
builds successfully with that override, without source edits. All other
existing dependency revisions remain unchanged. Upstream retains its
copyright headers and Apache-2.0 license. The audit includes every declaration
defined by every selected module, including declarations outside the
`TauCeti` namespace. It does not claim to build or audit unused upstream modules.

The project modules `DedekindZetaBounds`, `DedekindEulerLog`, and
`DedekindPrimeSum` prove compact strip bounds for the regularized zeta
function, the bounded contribution from higher prime powers, and the
uniform logarithmic profile of the smoothed reciprocal-prime-ideal sum.
The subsequent local modules through `PolynomialPrimeCosine` prove the
root-count correspondence, the convergent higher-degree remainder, finite
exceptional-prime correction, and removal of smoothing. They establish the
polynomial cosine estimate and hence the full polynomial mean bound.

`PrimitiveConductor` adapts the finite-index argument from Tau Ceti’s
`NumberTheory/NumberField/Index/Basic.lean` and `Index/Exponent.lean` at the
original revision `ea7e54cf967c2ab502c7e69bf69501e5a3ae3130`, under Apache 2.0.
Its header retains that provenance and its license reference points to the
root Apache-2.0 license.
No additional Tau Ceti modules are imported for this argument.

## Palomar submission preparation

The standalone `Challenge.lean` imports only Mathlib. Its thirty ordinary
mathematical definitions are mirrored from `BretecheTenenbaumMean/Definitions.lean`;
no definition is left unspecified. Ten theorem proofs are deliberate Challenge
holes, and `Solution.lean` imports the proved versions under the same names.
Comparator recursively compares the fixed definitions as well as the named
statements. The proof-development axiom audit excludes the Challenge.

The source scanner, Ruby metadata validator, and Comparator runner derive from
[PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate) at revision
`2891de4c48955af824969a263d31b25e7a9a1406` (Apache-2.0). The runner builds the local modules before invoking
Comparator and uses the bundled NanoDa and con-ron kernels. The upstream
source scanner and Ruby validator are retained verbatim. `check-palomar.py`
adds checks for this repository's configuration and provenance inventories.

Jason Davies confirmed authorship/maintenance and Apache-2.0 licensing for this
project, and ownership and Apache-2.0 licensing of the reused Nair–Tenenbaum
sources. Their original file hashes remain unchanged.
