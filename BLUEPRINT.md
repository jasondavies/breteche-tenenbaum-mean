# Proof map

Source: arXiv:2309.03958v14; see [paper/SOURCES.md](paper/SOURCES.md).
The objective is the whole paper. All named targets and their supporting analytic inputs are proved.
`paper_main_results` in `FullPaper` assembles the named statements; the exact global
Parseval identity is in `GlobalParseval`.

All implemented proofs must use only `propext`, `Classical.choice`, and
`Quot.sound`. Do not turn an open estimate into an assumption of a theorem
advertised as the paper's unconditional result. An open target is a `Prop`
definition, not a theorem.

## One proof of §2, through the weighted model

The moment, frequency and good-set arguments of §2 are proved once, for a
general weight satisfying `WeightedModel.PrimeEstimates`. `UnitWeight` proves
that structure for the constant weight, which recovers the paper's finite model
exactly: `abs_cosinePrimeSum_unit_sub_le` compares strict and weak prime cutoffs,
and `PrimeSums.cosinePrimeSum_log_ratio_two` extends (2.12) from `0 ≤ ψ ≤ 1` to
`0 ≤ ψ ≤ 2`. `hooleyDelta_expectation_bound`, `propositionTwoOneUpper` and
`propositionTwoTwo` are specializations. Polynomial root weights use the same
theorems through `PolynomialPrimeCosine`. The narrative sections below describe
the unweighted argument, which is the unit-weight case of those proofs.

## Checked foundations

| Paper material | Module | Declarations |
|---|---|---|
| §1, divisor windows and maximum | `Delta` | `hooleyDelta_attained`, `divisorWindow_mul`, `hooleyDelta_mul_le` |
| §1, positive-order moments | `Moments` | `integrable_delta_pow`, `moment_one`, `moment_le_max_mul_tau`, `moment_le_tau_pow` |
| Both sides of (1.4) | `HalfRange` | `moment_recurrence`, with the even-order midpoint handled by an inequality |
| Binomial expansion underlying (1.4), (1.5) | `MomentRecurrence` | `mixedMoment`, `moment_mul_prime` (all indices retained) |
| Reflection and mixed-moment symmetry | `Reflection` | `delta_reflect_ae`, `mixedMoment_symm` |
| Adjacent moment interpolation | `MomentConvexity` | `moment_logConvex`, `moment_two_sq_le` |
| Normalized moment monotonicity | `MomentRecurrence` | `normalized_moment_le_mul_prime`, `normalized_moment_le_of_dvd` |
| Introductory Hölder interpolation | `MomentInterpolation` | `moment_interpolation`; all `n≥1`, `q≥2`, `1≤j≤q−1`, with the displayed fractional exponents |
| Close-divisor pairs in §2.1 | `PairCount` | `integral_wideDelta_sq_eq_sum`, `closeDivisorPairs_bounds`; `M₂≤T(n,0)≤4M₂`, including pairs exactly one unit apart |
| Exact second moment as divisor-pair overlaps | `SecondMoment` | `moment_two_eq_sum`, `tau_le_moment_two` |
| §2.4, maximum controlled by moments | `WindowBounds` | `max_pow_le_moment`: `Δ(n)^q ≤ 2^q M_q(n)` |
| §4, pointwise pigeonhole bound | `WindowBounds` | `tau_le_max_mul_log`: `τ(n) ≤ Δ(n)(log n + 1)` |
| §2.1, finite probability and expectation | `Probability` | `mem_smoothSupport`, `sum_reciprocal_smoothSupport`, `expectation_one`, `probability_gt_le` |
| Multiplicative expectations and divisor-count moments | `Probability` | `expectation_multiplicative`, `expectation_tau_pow` |
| §2.2, divisor Dirichlet polynomial | `DivisorPolynomial` | `divisorPolynomial_mul`, `norm_divisorPolynomial_le`, `normSq_divisorPolynomial_prime` |
| Global Parseval identity (2.6) | `FejerIntegrable`, `TriangleTransform`, `FejerInversion`, `GlobalParseval` | `fourier_triangleKernel`, `integral_sinc_sq_cos`, `integrable_parseval_integrand`, `moment_two_parseval_sine`; exact `1/(2π)` normalization, convergent global integral, null singleton handled |
| Compact-frequency comparison (2.7) | `FejerKernel`, `FourierComparison` | `normalized_moment_two_le_fourier_integral`, explicit constant `π²/2` |
| One- and two-frequency Euler products | `PolynomialExpectation` | `expectation_normalizedPolynomial` |
| Averaged Fourier comparison | `FrequencyAverage` | `integral_expectation`, `expectation_moment_two_le` |
| PNT and strong Mertens estimate | `PrimeSums.Error`, `PrimeSums.Mertens`, `PrimeSums.Strict` | `theta_asymp`, `S_asymp`, `SLT_asymp`, exact endpoint control `S_sub_SLT` |
| Mertens products and divisor-count moments | `PrimeSums.Product`, `WeightedPrimeConsequences` | `normalizer_bounds`, `normalizer_ratio_bounds`, `abs_log_prod_sub_sum_le`, `WeightedModel.PrimeEstimates.expectation_tau_pow_bound` |
| Cosine prime-sum formula (2.12) | `PrimeSums.CosineIntegral` | `cosinePrimeSum_log_ratio`, uniform for `x ≥ 2`, `0 ≤ ψ ≤ 1`, including the transition `ψ log x = 1` |
| Uniform weighted prime sums | `PrimeSums.Abel`, `PrimeSums.Cosine` | `weighted_prime_error_bound`, `cosinePrimeSum_integral_error` for `|ψ| ≤ 2` |
| Interval prime-sum estimates (2.9)–(2.11) | `PrimeSums.Intervals`, `WeightedPrimeIntervals` | `abs_S_sub_loglog_le`, `WeightedModel.PrimeEstimates.interval_difference_frequency`, `WeightedModel.PrimeEstimates.halfOpen_U2`, `WeightedModel.PrimeEstimates.halfOpen_U3`; (2.9) is Mertens at `exp(1/φ)`, and (2.10)–(2.11) use half-open prime intervals, with difference-frequency and sum-frequency cases included |
| One-frequency mean and initial frequency range | `FrequencyEstimates`, `WeightedInitialFrequency` | `expectation_normalizedPolynomial_le`, `WeightedModel.initial_frequency_integral_le`, `expectation_moment_two_log_bound` |
| Small-prime-weighted frequency estimate | `SmallPrimePolynomial`, `SmallPrimeFrequency` | `expectation_smallPrimePolynomial_le`, `goodSet_frequency_bound`; strict cutoff endpoint controlled |
| Intermediate-frequency exceptional probability | `Penalty`, `IntermediateFrequency` | `penalty_eq_log`, `intermediate_frequency_mean_bound`, `intermediate_frequency_probability_bound`, explicit `K = 16 + 1/δ` |
| Uniform factorial and fixed-prime-count bounds | `PoissonBound`, `DistinctProductSum`, `PrimeLayers` | `factorial_term_uniform`, `distinctProductSum_le`, `probability_prime_layer_eq`, `tau_prime_layer_uniform` |
| Exact three-range multiplicative decomposition | `PrimePartition`, `TwoFrequencyWeight`, `WeightedTwoFrequency` | `sum_smallPrime_layer_eq_product`, `WeightedModel.twoFrequency_layer_uniform`; strict cutoffs and fixed small-prime count |
| Three-range analytic prime bound | `HighFrequencyPrimeBound`, `WeightedPrimeIntervals`, `WeightedHighFrequencyPrimeBound` | `WeightedModel.PrimeEstimates.halfOpen_U2`, `WeightedModel.PrimeEstimates.halfOpen_U3`, `WeightedModel.high_frequency_layer_bound`; square-root saving from both sides of Mertens' estimate |
| Exact dyadic good-set partition | `DyadicGoodSets`, `WeightedDyadicGoodSets` | `dyadicGoodSet_index_unique`, `dyadicGoodSet_fixed_prime_count`, `WeightedModel.goodSet_expectation_eq_dyadic_sum`, `WeightedModel.goodSet_expectation_le_of_dyadic` |
| Full high-frequency good-set integrand bound | `HighFrequencyDyadic`, `HighFrequencyKernel`, `WeightedHighFrequencyDyadic`, `WeightedHighFrequencyIntegration` | `WeightedModel.high_frequency_goodSet_bound`, `highFrequencyKernel_eq_regularized`, `WeightedModel.high_frequency_goodSet_one_penalty_bound`; both penalty factors retained before dropping one |
| Integration in the larger frequency | `HighFrequencyLogWeight`, `HighFrequencyRegions`, `HighFrequencyIntegration` | `integral_regularizedHighKernel_le`, explicit constant `816`; near-diagonal square-root and far-diagonal power bounds |
| Uniform penalty integral | `PenaltyGaussian`, `PenaltyIntegral` | `frequency_penalty_integral_le`; exact coordinate `√log(log 3 + 1/θ)`, two Gaussian majorants, bound independent of `T` and lower endpoint |
| High-frequency second moment and tail | `HighFrequencyMean`, `EventBounds`, `SecondMomentTail`, `WeightedHighFrequencyMean`, `WeightedSecondMomentTail` | `WeightedModel.high_frequency_triangle_bound`, `WeightedModel.high_frequency_second_moment_bound`, `WeightedModel.high_frequency_probability_bound`; all admissible cutoffs, no comparison of `T^K` with `log x` |
| §2.2, second-moment exception inside the good set | `SecondMomentTail`, `WeightedSecondMomentTail` | `WeightedModel.goodSet_second_moment_probability_bound`, `WeightedModel.probability_goodSetStar_compl_le`; unconditional `Oδ(1/T)` bound inside `E_T` and reduction of (2.4) to (2.1) |
| Refined Poisson tails and entropy | `PoissonTail`, `PoissonRate`, `PrimeCountTail`, `WeightedPrimeCountTail` | `sum_poissonTerm_tail_le`, `poissonTerm_le_rate`, `poissonRate_quadratic_lower`, `WeightedModel.probability_prime_ge_le_rate`, exact ceiling convention for divisor thresholds |
| Small-prime marginal distributions | `SmallPrimeDistribution`, `WeightedGoodSetReduction` | `probability_smallPrime_tau_ge_eq`, `WeightedModel.probability_smallPrime_tau_ge_le`; cutoffs beyond the ambient support included |
| Good-set grid reduction | `GoodSetGrid`, `GoodSetReduction`, `WeightedGoodSetReduction` | `goodSet_failure_grid`, `WeightedModel.goodSet_compl_le_finite_grid_sum`; exact envelope, grid `exp(exp j)/3`, explicit `exp 7` loss |
| Entropy and Mertens on the grid | `PrimeSums.Grid`, `PenaltyComparison`, `WeightedPrimeCountTail` | `WeightedModel.probability_prime_ge_exp_rate`, `poissonRate_scaled_global_lower`, global quadratic and Gaussian comparisons for the clipped penalty |
| Uniform grid tails and their summation | `GridThreshold`, `GridEntropy`, `GaussianGrid`, `WeightedGridTail` | `grid_entropy_lower`, `WeightedModel.grid_divisor_tail_bound`, `sum_gaussian_sqrt_grid_le`; rounding and Mertens errors retained uniformly |
| Good-set exception (2.1) and Proposition 2.1 upper (2.4) | `PropositionTwoOne`, `WeightedGoodSetExceptional` | `WeightedModel.goodSet_exceptional_probability_bound`, `propositionTwoOneUpper`; unconditional, with `δ = 10⁻⁶` admissible |
| Good sets and divisor closure | `GoodSets` | `goodSet`, `goodSetStar`, `momentGoodSet`, their `_of_dvd` lemmas |
| Corrected §2.4 Markov step | `GoodSets`, `WeightedAllMomentGoodSet` | `WeightedModel.probability_momentGoodSet_drop`, with denominator `θ(q+1)` |
| Largest-prime recursion and its finite iteration (2.15) | `LargestPrime`, `OrderedRecursion`, `PrimeRecursion`, `WeightedLargestPrime`, `WeightedPrimeRecursion` | `sum_smoothSupport_by_largest_prime`, `WeightedModel.truncatedMoment_largest_prime_le`, `sum_ordered_recursion_le`, `WeightedModel.truncatedMoment_recursion_bound`; one constant uniform in all moment and threshold data |
| Moment-product estimate (2.17) and exceptional midpoint | `WeightedTruncatedProducts` | `WeightedModel.momentProductSum_le`, `WeightedModel.momentProductSum_four_two_le`; exact normalizer bound before Mertens |
| Penalty integral in (2.19) | `LogarithmicPenaltyIntegral` | `logarithmic_penalty_integral_bound`; explicit `(1/δ + sqrt(π/δ)) sqrt(log T)` bound independent of the upper endpoint |
| Optimized finite Selberg sieve | `NairTenenbaum.SelbergWeights`, `NairTenenbaum.SelbergDenominator`, `NairTenenbaum.SelbergCoefficientBounds`, `NairTenenbaum.SelbergRemainder` | Imported from the pinned Nair–Tenenbaum dependency; `NairTenenbaum.exists_selberg_upper_bound`, with explicit cutoff and remainder |
| Short prime intervals | `Sieve.Interval`, `PrimeSums.ShortIntervals` | `card_multiples_Ioc_error`, `prime_interval_sieve_bound`, `prime_count_real_interval_le`, `prime_reciprocal_interval_bound`; square-root errors and both endpoints |
| Divisor tuples and arbitrary positive-order overlaps | `TupleWindows` | `moment_eq_tuple_sum`, `coherent_tuple_count_le`; the tuple-count error is at most `2^j M_j(n)` |
| Prime averaging in §2.3 | `PrimeWindowAverage` | `delta_pow_prime_average_bound`, `mixedMoment_prime_average_bound`, `mixedMoment_prime_band_bound`; uniform constant, exact `log(3y)` offset and fourth-root error |
| Smoothing and reciprocal-logarithmic prime tails | `SmoothSums`, `PrimeSmoothing`, `PrimeSums.LogTail`, `PrimeSmoothingTail` | `prime_sum_le_smoothed_integral`, `prime_inv_log_tail_bound`, `prime_integral_tail_bound`; exact endpoint and integrability control |
| Integrated moment recursion | `RecursionPrimeAverage`, `WeightedRecursionPrimeAverage`, `WeightedSmoothedRecursion`, `WeightedIntegralRecursion` | `WeightedModel.recursionPrimeTerm_band_bound`, `WeightedModel.recursionError_integral_bound`, `WeightedModel.truncatedMoment_integral_bound`; uniform constants and exact fourth-root error |
| Accumulated error and threshold absorption (2.16) | `RecursionErrorProducts`, `LogPowerIntegral`, `RecursionKernels`, `ThresholdRecursion`, `WeightedRecursionDecay`, `WeightedThresholdRecursion` | `WeightedModel.recursionDecay_integral_bound`, `factorial_error_le_threshold`, `WeightedModel.truncatedMoment_threshold_recursion`; factorial majorant and geometric saving, uniform for all sufficiently large threshold constants |
| Real-weight Euler products and square-root divisor counts | `WeightedSqrtDivisorAverage` | `WeightedModel.sum_sqrt_tau_div_eq_prod`, `WeightedModel.sum_sqrt_tau_div_bound`; exponent `sqrt 2`, uniform down to `y=1` |
| Third-moment base case (2.18) | `ThirdMomentProducts`, `LogisticIntegral`, `ThirdMomentBase`, `WeightedThirdMomentProducts`, `WeightedThirdMomentBase` | `WeightedModel.momentProductSum_three_one_bound`, `integral_logarithmic_transition_le`, `WeightedModel.truncatedMoment_three_bound`; unconditional `S₃(x) ≪ T log T`, independent of the thresholds |
| Moment induction and Proposition 2.2 | `RecursionEndpoints`, `ThresholdConvolution`, `PropositionTwoTwo`, `WeightedMomentInductionKernel`, `WeightedPropositionTwoTwo` | `WeightedModel.recursionMain_integral_induction_bound`, `WeightedModel.propositionTwoTwo_for_delta`, `propositionTwoTwo`; exceptional midpoint included and all constants selected before the varying parameters |
| Explicit thresholds in §2.4 | `InverseSquareConvolution`, `ExplicitThresholds` | `explicitThreshold_eq_paper`, `explicitThreshold_admissible`; exact `2π²/3` constant, using Mathlib's Basel sum |
| Simultaneous moment control and maximum tail | `AllMomentGoodSet`, `AllMomentMaximum`, `WeightedAllMomentGoodSet`, `WeightedDeltaProbabilityTail` | `WeightedModel.allMomentGoodSet_probability_bound`, `moment_order_floor_bounds`, `WeightedModel.hooleyDelta_probability_tail_bound`; all positive moments, corrected Markov denominator, explicit cutoff `exp(exp 4)` |
| Finite-model mean in §2.4 | `FiniteTailExpectation`, `DyadicTailScale`, `DeltaExpectation`, `WeightedTailToMean` | `WeightedModel.expectation_le_of_logarithmic_tail`, `hooleyDelta_expectation_bound`; unconditional `E_x(Δ) ≪ (log log x)^(5/2)`, with a second-moment remainder |
| Arithmetic transfer and Theorem 1.1 | `DeltaSubmultiplicative`, `WeightedMangoldt`, `DeltaLogAverage`, `SquareDivisorSum`, `SquarefreeTransfer`, `TheoremOne` | `hooleyDelta_mul_le_tau`, `sum_divisorMangoldt_le`, `meanSum_le_harmonic`, `sum_tau_square_div_sq_le`, `harmonic_delta_le_expectation`, `theoremOne`; unconditional ordinary mean bound, with explicit cutoff `exp(exp 4)` |
| Product-moment bound in §4 | `DeltaConvolution` | `deltaConvolution_eq_sum`, `deltaConvolution_sq_le`, `hooleyDelta_mul_sq_le_moments`; exact tent overlap formula, endpoint reflection almost everywhere, no coprimality |
| Finite-model quadratic upper bound | `DivisorConvolutionBounds`, `QuadraticExpectation` | `harmonic_convolution_smooth_le`, `squarefree_delta_sq_le_convolution`, `expectation_delta_sq_bound`; factor `4` retained, existing Fourier mean supplies the analytic input |
| Square-factor bounds and quadratic harmonic mean | `DivisorPowerSums`, `SquarefreeTransfer`, `QuadraticHarmonic` | `sum_tau_pow_div_sq_le`, `harmonic_squareFactor_bound`, `harmonic_delta_sq_bound`; general nonnegative square-factor transfer and explicit `(π²/6)^16` bound |
| Upper half of Theorem 1.2 | `WeightedMangoldtSquare`, `QuadraticLogAverage`, `QuadraticUpper` | `sum_divisorSquareMangoldt_le`, `quadraticSum_le_harmonic`, `theoremTwo_upper`; ordinary quadratic mean, full range `x ≥ 3` |
| Lower half and completion of Theorem 1.2 | `PrimeSums.ProductLower`, `OmegaWeight`, `OmegaTruncation`, `DivisorSquareLower`, `QuadraticLower`, `TheoremTwo` | `omegaThree_harmonic_lower`, `divisor_square_sum_lower`, `theoremTwo_lower`, `theoremTwo`; both quadratic bounds for every `x≥3` |
| Reciprocal-prime coefficient lower bounds | `DistinctProductLower`, `PrimeSums.InverseSquareTail`, `PrimeSums.Trimmed`, `PowerComparison`, `PrimeCoefficientBounds` | `distinctProductSum_collision_bound`, `distinctProductSum_lower_half`, `reciprocal_prime_coefficient_bounds`; all orders `k≤A log log y`, with constants depending only on `A` |
| Lemma 3.1, estimate (3.1) | `PrimeLayerAsymptotic`, `LemmaThreeOne` | `probability_prime_layer_bounds`, `lemmaThreeOne`; two-sided normalizer bounds and the exact dyadic logarithmic scale |
| Lemma 3.1, central-window consequence (3.2) | `PoissonLower`, `PrimeLayerCentral`, `LemmaThreeOneCentral` | `factorial_term_lower`, `factorial_term_central`, `probability_prime_layer_central`, `lemmaThreeOneCentral`; integer count `k`, real offset `t=k-h`, and explicit critical-slope identity |
| Exact nested-cutoff marginals and joint counts | `PrimeMarginal`, `JointPrimeLayers` | `expectation_smallPrimePart`, `probability_smallPrime_joint_marginal`, `probability_joint_prime_layers`; arbitrary projected statistics and exact independent-block factorization |
| Separated-scale overlaps and inclusion–exclusion | `PrimeGapDecay`, `FiniteBonferroni`, `SeparatedEvents` | `probability_dyadic_joint_decay`, `probability_exists_mem_ge_pairs`, `exists_dyadic_spacing`; geometric ratio `e log 2/2<1`, fixed spacing preserves half the marginal sum |
| Tilted size exceptions in §3 | `PrimeSums.Tilted`, `TiltedPrimeLayers` | `tilted_prime_sum_le`, `expectation_tilted_prime_layer_bound`, `probability_smallPrime_size_exception`; uniform relative loss `D exp(-K)` for counts at most `A log log y` |
| Local size control and lower-tail reduction | `SecondMomentPigeonhole`, `LowerTailReduction` | `tau_sq_le_moment_two_mul_log`, `normalized_second_moment_dyadic_layer`, `lower_tail_dyadic_reduction`; a quarter of the marginal sum survives and forces the normalized-moment tail |
| Completion of Proposition 2.1 lower | `CentralDyadicWindow`, `ScaleWindowCount`, `DyadicLowerTail`, `PropositionTwoOneLower` | `central_dyadic_marginal_lower`, `scaleWindow_card_lower`, `dyadic_second_moment_lower_tail`, `propositionTwoOneLower_quantitative`, `propositionTwoOneLower`; explicit range `x≥exp((B*T)^4)`, strict tail, integer rounding |
| Lower-tail range obstruction | `RangeCheck` | `not_uniform_lower_tail` |
| Polynomial consequence (1.7) | `PolynomialPrimeCosine`, `FullPaper` | `polynomialPrimeCosineEstimates`, `polynomialMeanBound`, `paper_main_results`; general irreducible integer polynomials, with no extra analytic hypotheses |
| Named statements | `Definitions` | Proposition definitions; `TheoremOne`, `TheoremTwo`, `PropositionTwoOneUpper`, `PropositionTwoOneLower`, `PropositionTwoTwo`, `LemmaThreeOne` and `LemmaThreeOneCentral`, together with `PolynomialMeanBound`, have unconditional proofs. `paper_main_results` in `FullPaper` assembles all eight. |

## Completion of the proof obligations

1. **Moment calculus — completed.** The adjacent-order inequalities and
   full Hölder interpolation inequality are proved. The comparisons
   `M₂(n) ≤ T(n,0) ≤ 4 M₂(n)` and the product inequality in §4 are also
   proved, with endpoint conventions handled explicitly.
2. **Good sets — completed.** The exceptional estimate (2.1) is proved for
   `0 < δ ≤ 10⁻⁶`, uniformly in `x` and `T > 1`. The proof includes exact
   small-prime marginals, logarithmic discretization, refined factorial tails,
   a global entropy remainder, rounded thresholds, uniform Gaussian summation,
   and absorption of bounded `T`.
3. **Fourier input — completed.** Both (2.6) and (2.7) are proved.
   `moment_two_parseval_sine` gives the exact printed global identity with
   factor `1/(2π)`, together with absolute integrability. The proof uses
   Mathlib's Fourier inversion theorem on the triangular overlap kernel.
   The compact comparison retains its direct proof and explicit constant.
4. **Prime sums.** Estimates (2.9)–(2.12), strong Mertens estimates, and
   positive Euler-product bounds are proved. The sum-frequency term up to
   two is handled directly by the uniform oscillatory tail estimate.
   The short-interval reciprocal-prime estimate and its mixed-moment
   averaging consequence in §2.3 are also proved. Smoothing, reciprocal-log
   prime-tail integration and the accumulated factorial error bound are proved.
5. **Proposition 2.1, upper bound — completed.** `propositionTwoOneUpper`
   proves (2.4), with `δ = 10⁻⁶` and a constant independent of `x ≥ 2`,
   `T ≥ 3`. It combines (2.1) with the second-moment exception inside the
   good set. The high-frequency estimate works for any positive cutoff at
   least `1/log x`, covering both regimes of `T^K` and `log x`. The separately
   proved intermediate-frequency estimate is not needed by this assembly.
6. **Proposition 2.2 — completed.** `propositionTwoTwo` proves the stated
   uniform bound for all admissible thresholds. Its proof includes the
   largest-prime recurrence, finite iteration, prime averaging, smoothing,
   factorial error and threshold absorption, the square-root divisor-count
   base case (2.18), the exceptional `q=4,j=2` term, and strong induction.
   The more general `propositionTwoTwo_for_delta` works for every fixed
   positive penalty parameter, with the threshold constant allowed to depend
   on that parameter. The explicit threshold sequence used in §2.4 is also
   verified, with its exact coefficient `2π²/3`.
7. **Theorem 1.1 — completed.** `theoremOne : TheoremOne` combines the
   finite-model mean with a proved arithmetic transfer. The latter uses
   `Δ(mn) ≤ τ(m)Δ(n)` without coprimality, the von Mangoldt identity and
   Chebyshev estimates, and the decomposition `n=b²a` with `a` squarefree.
   The bounded square-factor sum avoids an unproved appeal to
   Hall–Tenenbaum, Th. 61. The strict prime cutoff is enlarged to `2x`,
   and its logarithmic effect is controlled explicitly.
8. **Lemma 3.1 and the lower tail — completed.** Both (3.1) and (3.2)
   are proved. The lower-tail proof includes exact joint-event factorization,
   geometric overlap bounds, finite inclusion–exclusion, the tilted error
   estimate, and the count of separated scales. `propositionTwoOneLower`
   proves the target; its quantitative variant proves the explicit sufficient
   range `x≥exp((B*T)^4)` for `T≥3`, with absolute positive constants.
9. **Theorem 1.2 — completed.** `theoremTwo : TheoremTwo` proves both
   bounds for every `x≥3`. The upper bound uses the product-moment inequality,
   finite divisor convolution, the proved mean of `M₂/τ`, and the full
   squarefree-to-integer transfer. The lower bound uses a truncated `3^ω`
   Euler product, counting multiples, and the pigeonhole inequality.
   Constants are extended to the bounded initial range using `Δ(n)≥1`.
10. **Polynomial arguments (1.7) — completed.** `polynomialMeanBound` proves
    the full statement for every irreducible integer polynomial. The pinned
    Nair–Tenenbaum short-sum theorem, CRT, square-factor removal, fixed-prime
    removal, and interval summation reduce it to the weighted mean. The full
    weighted moment proof is instantiated by `polynomialPrimeCosineEstimates`.
    Kummer–Dedekind, integral normalization, Dedekind-zeta bounds, and the
    bounded error from removing exponential damping prove that arithmetic
    input. No prime-sum or mean-value assumption remains.

## Source issues resolved explicitly

- The Markov display in §2.4 divides by `ϑ_{q-1,T}` after a conditional
  expectation with denominator `ϑ_{q,T}`. The correct denominator at that
  equality is `ϑ_{q,T}`. This is visible in the TeX source too.
- The lower side of (2.5) cannot be uniform in all `x ≥ 2, T ≥ 3`:
  at `x=2` the support is `{1}` and `M₂(1)/τ(1)=1`. For every fixed finite
  cutoff the ratio is bounded. The proof in §3 requires `x` sufficiently
  large relative to the scales depending on `T`.
  `RangeCheck.not_uniform_lower_tail` proves this obstruction in Lean.
  `propositionTwoOneLower_quantitative` supplies the proved sufficient range
  `x≥exp((B*T)^4)`. This range is not claimed to be optimal.
- In §3, `t=log(2T)/log 2` is used as part of an integer index.
  `exists_dyadic_offset` rounds upward after a fixed initial offset, making
  the final tail inequality strict and bounding the rounding cost explicitly.
- The §3 size cutoff is handled locally for each event in the formal proof.
  An integer retained at one scale already forces the moment tail; it need
  not satisfy size bounds at every other scale. `probability_local_good_union`
  justifies subtracting the sum of these local exceptions. The proof does
  not assume the displayed same-index bound for the complement of the
  paper's simultaneous good set.
- The high-frequency display uses `1/ψ` in place of the good-set envelope's
  `log(3 exp(1/ψ))`. The formal dyadic layers keep the exact envelope. The
  comparison `log(3 exp(1/ψ)) ≤ 4/ψ` supplies a proved uniform constant.
  The fixed prime count is proved directly from the factor-two band, avoiding
  an implicit floor convention for a possibly negative logarithm.
- Strict versus non-strict prime cutoffs vary in the exposition. The formal
  probability model uses `p<x` throughout. Any endpoint comparison needed
  for quoted estimates must be proved.

## Verification

`bash scripts/check.sh` builds the library and audits all project and vendored modules,
plus the imported Nair–Tenenbaum and Tau Ceti dependency cones.
Keep its `import all` list in sync when adding modules; the audit deliberately
fails if a file is omitted. Target proposition definitions do not count as
proofs of their statements.

## Alternative proof of (2.7)

The proved finite Fejér-kernel argument avoids a general Montgomery–Wirsing
library. Expanding the triangularly weighted integral of `|τ(n,θ)|²` on `[0,1]`
gives a sum over divisor pairs of `(1-cos t)/t²`, extended by `1/2` at zero.
This kernel is nonnegative everywhere and at least `2/π²` for `|t|≤1`.
Termwise comparison with `moment_two_eq_sum`, followed by removal of the
triangular weight, gives `M₂(n) ≤ (π²/2) ∫₀¹ |τ(n,θ)|² dθ`.
The exact global identity (2.6) remains a separate obligation.

## Integration of the high-frequency bound

The larger-frequency integral uses the explicit exponent `95/64 < 3/2`
after transferring the logarithmic square-root weight. Splitting at `φ=2θ`
gives a bound `816 / (θ √log(3/θ))` for the regularized kernel when
`0 < 1/log x ≤ θ ≤ 1`.

For the remaining integral, set `s=√log(log 3 + 1/θ)` and `t=log T`.
The exact penalty becomes `δ min(t+s², (s²-bt)²/t)`. For nonnegative `s`,
`(s²-bt)²/t ≥ b(s-√(bt))²`. Thus its exponential is bounded by two
Gaussians, while the original frequency measure is at most six times the
positive substitution Jacobian. This gives a bound uniform in `T` and in
any positive lower endpoint. All substitutions, Jacobian comparisons and
Gaussian integral bounds are checked in Lean.

## Good-set exceptional estimate: completed proof

The grid is `y_j = exp(exp j)/3` for integers `j ≥ 1`, so
`log log(3 y_j) = j` exactly. Rounding a cutoff upward costs at most `exp 7`
in the good-set envelope when `0 ≤ δ ≤ 1`. Every failure of the continuum
of constraints is therefore detected on this grid. Finite support supplies
a finite witness subfamily, and exact small-prime marginal distributions
remove the ambient cutoff from every summand.

The divisor threshold `R` corresponds exactly to
`ceil(log R / log 2)` prime factors. Refined factorial tails retain both
`exp(-u Q(k/u))` and the `1/sqrt(k)` saving, with `Q(v)=v log v-v+1`.
The checked global entropy lower bound has quadratic term
`(k-2u)^2/(2 max(2u,k))`. For the clipped penalty, its quadratic comparison
uses denominator `t+u`, and a further lower bound is
`(sqrt u-sqrt(b t))^2/9`. With the ceiling and Mertens errors retained,
these give a grid tail bounded by
`(C/T) exp(-(δ/9)(sqrt j-sqrt(b log T))²)/sqrt j` for large `T`.
Each summand is compared with a widened Gaussian on
`[sqrt j, sqrt(j+1)]`. The intervals telescope, giving a bound independent
of the center and the finite grid subfamily. The trivial probability bound
absorbs bounded `T`. This proves (2.1), and adding the already proved
second-moment exception proves (2.4).

## Largest-prime recursion

`sum_smoothSupport_by_largest_prime` partitions the squarefree support into
`{1}` and unique products `m*p` with `m` in the strict support at `p`.
The moment good set is closed under divisors, which permits dropping its
constraint on `m*p` when applying the half-range recurrence.

The iteration is a finite ordered inequality: the contribution at each prime
is multiplied by the product of `1+1/r` at larger primes. Bounding this
product by the ratio of normalizers gives an exact-normalizer version of
(2.15), followed by Mertens. No limiting remainder is assumed.

For the induction's penalty integral, the exact coordinate is
`s = log log(3y)`, with Jacobian `1/(y log(3y))`. The clipped exponential
is bounded by an exponential tail and a translated Gaussian of width
`sqrt(log T)`. Integration gives a constant independent of the upper endpoint.

## Prime averaging

The interval sieve has error `K z^8` and main term bounded by
`4 (b-a)/normalizer(z)`. Taking `z=a^(1/16)`, applying Mertens, and absorbing
bounded `a` proves `#(primes in (a,b]) ≪ (b-a)/log a + sqrt a`. Floor errors
are retained when passing to real endpoints. Consequently, on a bounded
multiplicative interval, the reciprocal-prime sum is bounded by its logarithmic
length divided by the logarithm of the lower endpoint, plus a square-root
error. All of this is proved from the local Selberg construction and Mathlib.

For each divisor tuple, its window overlap has length
`max(1 + min(log d_i) - max(log d_i), 0)`. Summing these lengths gives the
moment exactly. The number of tuples with positive overlap is at most the
width-two moment, hence at most `2^j M_j(n)`. Applying the short-interval
bound to each tuple and integrating against the other window power proves
`mixedMoment_prime_band_bound`, including `1 ≤ y < 4` separately. The result
is uniform in `n,q,j,y` and every finite prime subset of `[sqrt y,y]`.

## Smoothed recursion and accumulated error

The smoothing weight is `1/(y log(3y))`, whose integral on `[p,p²]` is
at least `1/4` for every prime. Nonnegative summands permit extension to
the support at `y`; the prime-averaging bound then gives the integral
estimate for `V_q`. Abel summation applied to `1/(log t)²` proves
`sum_{p≥z} 1/(p log p) ≪ 1/log z` for every finite prime subset, including
an endpoint prime. Integrating this tail gives the extra logarithmic
denominator in the `S_q` bound. All sums are finite, and the restricted
integrands are proved interval integrable before the interchange.

The resulting kernel splits exactly into the main term in (2.16) and a
fourth-root error. On the good set, `τ(m) ≤ T log(3y)`; consequently
`Z_{q,j}(y) ≪ T^(q−2) (log(3y))^q` uniformly in both orders. The exponential
series gives
`∫₁ˣ (log(3y))^k/(y y^(1/4)) dy ≤ 24·8^k·k!`.
Together with the binomial bound `sum choose(q,j) 2^j ≤ 3^q`, this proves
the accumulated error `C^q q! T^(q−2)`. The factorial lower bound on
`θ(q−1)` absorbs this error with a `2^(−q)` saving whenever the threshold
constant is sufficiently large. This establishes (2.16) uniformly in all
parameters. The base case and induction have now also been proved, as described below.

## Third-moment base case and completion of Proposition 2.2

The exact Euler product for `sum sqrt(τ(m))/m` has prime factors
`1+sqrt(2)/p`; Mertens gives a bound by `C (log(3y))^(sqrt 2)`.
Inside the good set, `M₂ ≤ T τ` and `τ ≤ T log(3y)` give two bounds for
`Z₃,₁`: `A T (log(3y))²` and
`B T sqrt(T) sqrt(log(3y)) (log(3y))^(sqrt 2)`.
Multiplying these by the complementary denominator terms proves (2.18),
with positive saving `3/2-sqrt 2` and the small endpoint retained.
The coordinate `s=log log(3y)` reduces its integral to
`R/(R+exp(a s))`, whose integral is bounded by `log(1+R)/a`.
This proves `S₃(x) ≪ T log T` independently of the threshold sequence.

For higher orders, `(q-j)² ≥ q²/4` transfers the induction hypothesis to
the product sums. At `q=4`, the comparison `Z₄,₂ ≤ Z₄,₁` reduces the
midpoint to order three. The penalty integral costs `sqrt(log T)`.
The first convolution term absorbs the remaining geometric error because
`q ≤ 2^q` and `θ₁ ≥ 1`. The admissibility convolution bound then closes
strong induction after a single sufficiently large constant is chosen.
All small cutoffs `1 ≤ y ≤ 2` are handled using the exact support `{1}`.

## Explicit thresholds and the finite-model mean

The scale is `(2π² C₀/3) T sqrt(log T)`, with threshold
`θ_q = (q!/q²) scale^(q−1)` for positive orders and `θ_0=1`.
The packaged definition is proved equal to the paper's displayed formula.
Factorial cancellation reduces the convolution condition to
`sum_{j≤q/2} 1/(j²(q-j)²) ≤ (2π²/3)/q²`; this follows from the exact
Basel sum in Mathlib. All remaining growth and initial-order conditions
are checked.

The moment good sets agree with `E_T*` through order two. Every later
failure belongs to a consecutive drop, whose probability is bounded by
`C₀/(q² T)` using the corrected denominator `θ_q`. Finite support supplies
a finite witness subfamily for their countable union. Adding Proposition
2.1 proves the simultaneous moment exception `O(1/T)`.

For `x ≥ exp(exp 4)`, the order `q=floor(log log x)` satisfies `q≥3` and
`log log(3x)≤2q`. The divisor envelope and the explicit thresholds give
`Δ≤C T sqrt(log T) log log x` on the simultaneous good set. This proves
the uniform probability tail in §2.4.

The expectation proof uses thresholds corresponding to `T=2^(j+2)`.
With `s=log log x`, `ceil(3s/log 2)` layers reach beyond `(log x)^3`.
Each layer costs `O(s sqrt(j+3))`; their sum is `O(s^(5/2))`.
A general finite-tail inequality controls the remaining tail by the second
moment divided by the last threshold. Since `Δ≤τ` and
`E_x(τ²)≪(log x)^3`, this remainder is bounded uniformly. All layer counts,
endpoint inequalities and finite expectation interchanges are checked.
The arithmetic transfer is proved as described below, completing Theorem 1.1.


## Arithmetic transfer and Theorem 1.1

Every divisor of `mn` factors as a divisor of `m` times a divisor of `n`.
Counting a union gives `Δ(mn) ≤ τ(m)Δ(n)` without coprimality. The identity
`log n = sum_{d|n} Λ(d)` therefore bounds `Δ(n) log n` by the Dirichlet
convolution of `Δ` and `τΛ`. On primes this weight is `2 log p`; on other
prime powers it is at most `(1+log x/log 2)Λ(n)`. Mathlib's estimates
`θ(x) ≤ (log 4)x` and `ψ(x)-θ(x) ≪ sqrt x` give a linear summatory bound.
Interchanging finite convolution sums yields
`sum_{n≤x} Δ(n) log n ≪ x sum_{n≤x} Δ(n)/n`.
The contribution of `n≤sqrt x` is at most `x`, and above that cutoff
`log n≥(log x)/2`. This proves the ordinary-to-harmonic comparison.

Choose `n=b²a` with `a` squarefree. Its contribution is bounded by
`(Δ(a)/a)(τ(b²)/b²)`. On prime powers `2k+1≤(k+1)(k+2)/2`, so
`τ(b²)` is bounded by the three-divisor function. Twisting Dirichlet
convolution by `1/n²`, bounding finite convolution sums by products,
and applying the Basel sum gives
`sum_{b≤N} τ(b²)/b² ≤ (π²/6)³`.
An injective choice of the squarefree decomposition proves the harmonic
comparison with `normalizer(2x) E_{2x}(Δ)`. Mertens bounds the normalizer,
and the proved finite-model estimate controls the expectation.
The bounds `log(2x)≤2log x` and `log log(2x)≤2log log x` give
`theoremOne : TheoremOne`, with cutoff `exp(exp 4)` and absolute constants.


## Quadratic upper mean

Reflection changes each half-open window indicator only on its two endpoints.
Consequently the integral of `Δ(r,u)Δ(s,c-u)` is exactly the divisor-pair
sum of the tent kernel `max(1-|log d+log t-c-1|,0)`. Each unit-window pair
contributes at least `1/2` to the centered tent. Divisor factorization and
Cauchy–Schwarz therefore prove `Δ(rs)² ≤ 4 M₂(r)M₂(s)` for all `r,s`,
without requiring coprimality or the global Parseval identity.

For squarefree `n`, each factorization `n=rs` has `τ(r)τ(s)=τ(n)`.
Averaging the product inequality over its `τ(n)` divisor factorizations gives
`Δ(n)² ≤ 4 (g*g)(n)`, where `g(n)=M₂(n)/τ(n)` and `*` denotes Dirichlet
convolution. The proof retains the factor `4` from the preceding inequality;
the paper's displayed convolution bound has coefficient `1`, which is not
needed for the stated asymptotic result. Harmonic convolution over the
finite divisor-closed support is bounded by the product of the two harmonic
sums. Thus `E_x(Δ²) ≤ 4 normalizer(x) E_x(g)²`, and the proved Fourier
mean bound supplies `E_x(Δ²) ≪ log x · log²(1+log x)` directly.

The ordinary-mean transfer is proved separately. Submultiplicativity of
`τ` gives `τ^(k+1) ≤ τ^k * τ^k` pointwise for positive powers. Twisting by
`1/n²` and inducting yields
`sum_{n≤N} τ(n)^k/n² ≤ (π²/6)^(2^k)`.
In particular `τ(b²)² ≤ τ(b)^4` gives the bounded square-factor weight
`(π²/6)^16`. The generic square-factor transfer then handles `Δ²`.
The weight `τ²Λ` has a linear summatory bound because its prime contribution
is `4θ(x)`, while the higher prime powers are controlled by
`(1+log x/log 2)²(ψ(x)-θ(x)) ≪ x`.
Splitting at `exp(log x/3)` bounds the small-integer contribution by `x`
and removes the logarithmic weight from the remaining terms.
Finally uniform comparisons of `log(1+log x)` with `log log x` for `x≥3`
prove `theoremTwo_upper` on the entire printed range. The lower half is
proved separately as described below.


## Quadratic lower mean and completion of Theorem 1.2

Let `w(n)=3^ω(n)` for `n>0`, with the arithmetic-function extension `w(0)=0`.
It is multiplicative. On prime powers the divisor sum is `1+3k`, which is
at most `(k+1)²`, so `(w*ζ)(n)≤τ(n)²` for every `n`.
The full harmonic sum over squarefree integers with primes below `y` is
`F(y)=prod_{p<y}(1+3/p)`. Mertens and the quadratic Euler-product remainder
give `F(y)≫(log y)³`.

The exact logarithmic mean of this finite product is
`F(y) sum_{p<y} 3 log p/(p+3)`. Chebyshev bounds the local sum by `D log y`.
Taking `y=exp(log R/K)` for a fixed `K≥2D+1`, the logarithmic tail inequality
retains at least half of `F(y)` on integers `n≤R`. This proves
`sum_{n≤R} w(n)/n ≫ (log R)³`, beyond an explicit fixed cutoff.
Counting multiples gives
`sum_{n≤N} τ(n)² ≥ (N/2) sum_{d≤N} w(d)/d`, since
`floor(N/d)≥N/(2d)` for `1≤d≤N`. The real cutoff incurs one more factor two.
Thus `sum_{n≤x} τ(n)² ≫ x(log x)³`.

The already proved pigeonhole inequality bounds this sum above by
`(log x+1)² sum_{n≤x} Δ(n)²`. For large `x` this yields the required lower
bound `x log x`; for `3≤x` below the fixed cutoff, `Δ(n)≥1` gives
`sum Δ(n)²≥x/2`. A single positive minimum of the two constants establishes
`theoremTwo_lower` on the full range. `theoremTwo` combines it with the
previously proved upper bound.

## Elementary moment comparisons

The full introductory interpolation inequality is proved by weighted
arithmetic-geometric mean after normalizing `Δ(n,u)^q` by `M_q(n)` and
`Δ(n,u)` by `τ(n)`. The weights `(j−1)/(q−1)` and `(q−j)/(q−1)` add to one
and produce power `j`. Integrability of all terms is established before
integration; `j=1` is treated directly.

For the close-divisor count, the unit-width tent kernel is bounded by the
indicator of logarithmic distance at most one. Conversely every such pair
contributes at least one to the width-two overlap integral. Splitting a
width-two window into adjacent unit windows bounds that integral by `4M₂`.
This proves both comparisons, retaining equality cases at distance one.

## Lemma 3.1

The elementary-symmetric recurrence marks one prime in a product. Iterating
it bounds repeated-prime contributions by
`k(k-1)/2 · (sum w²) · (sum w)^(k-2)`. Thus the distinct-product sum is at
least half the exponential-series coefficient when `k² sum w² ≤ (sum w)²`.
Removing all primes below a fixed `P>4A²+2` makes this condition hold for
`k≤A log log y`, once `y` is sufficiently large. The removed reciprocal sum
is bounded independently of `y`; exponentiating its logarithmic effect
costs a constant depending only on `A`. This proves the uniform reciprocal
coefficient estimate directly, without importing Hardy–Ramanujan's lemma.
Mertens' two-sided normalizer bound then proves (3.1).

For (3.2), Stirling sequence monotonicity bounds the factorial from above.
The elementary inequality `log v≤v-1` yields a lower Poisson coefficient
with penalty `(k-u)²/u`; the existing upper coefficient bound supplies the
other side. Set `u=2 log log y` and factor out `2^(-k)`. The identity
`2γ log 2=γ+1` places `k=h+t` within the required window about `u`.
The dyadic scale assumptions compare `h log 2` with `log log x`, giving
constants that depend only on `ε`. The formal statement uses natural
numbers `h,k` and the real offset `t=k-h`; no rounding of a count is hidden.

## Completion of the lower tail

Arbitrary small-prime projections preserve expectation. Splitting a second
cutoff into two prime blocks gives an exact joint-layer probability: the
first marginal times the elementary-symmetric coefficient for the intervening
block and the normalizer ratio. The factorial bound and Mertens' estimates
bound the latter factor by `C (e log 2/2)^l`. This ratio is proved to lie
strictly between zero and one. Finite Bonferroni and a geometric-tail sum
then give a fixed spacing `m` that retains half the sum of all marginals.

For the size cutoff, `exp v≤1+e v` on `[0,1]` bounds the tilted reciprocal
prime sum by `log log y+H`. Comparing its coefficient with the unweighted
lower coefficient proves a uniform conditional tilted-moment bound.
Markov gives a relative exception `D exp(-K)`; choosing a fixed `K` makes
this at most one quarter. Removing each event's own size exception leaves
at least one quarter of the marginal sum. Cauchy–Schwarz on the window
support gives `τ(n)²≤M₂(n)(log n+1)`, and normalized-moment monotonicity
under squarefree divisibility transfers this to the ambient integer.

For an integer offset `t`, choose multiples `h=m i` in
`[γt,γt+sqrt t]`. For sufficiently large `t`, there are at least
`sqrt t/(2m)` of them, and each marginal is at least `c/(2^t sqrt t)`.
The dyadic tail follows for `x≥exp(2^(4t))`. Rounding the offset upward
ensures `T<2^t/(K+1)` and `2^t≤B T`. Hence the final sufficient range is
`x≥exp((B*T)^4)`, including every `T≥3` with the same absolute constants.

## Global Parseval identity

The removable-singularity definition of `fejerKernel θ` equals
`sinc(θ/2)²/2`. Its continuity and the global bound `4/(1+θ²)` prove
integrability. The compactly supported continuous triangle
`max(1-|u|,0)` has Fourier transform `2 fejerKernel(2πξ)` in Mathlib's
normalization. Splitting its support at zero cancels the imaginary parts
and reduces this transform to the already proved triangular cosine integral.

Fourier inversion therefore evaluates the global cosine transform of the
Fejér kernel. A change of variable `θ=2πξ` gives
`∫ sinc(θ/2)² cos(aθ) dθ = 2π max(1-|a|,0)`.
The exact divisor-pair expansion of `|τ(n,θ)|²` and the overlap formula for
`M₂(n)` then prove (2.6). Each summand is integrable, so the finite sums
can be exchanged with the integral. The literal sine quotient agrees with
sinc away from zero, and Lebesgue measure gives that singleton mass zero.

## Polynomial short-sum reduction and weighted model

`PolynomialShortSum` identifies the two projects’ definitions of Δ and
bridges both the short interval sum and the root-weighted harmonic sum.
The 127-module dependency cone of the proved Nair–Tenenbaum theorem is
imported from the pinned `nair_tenenbaum` Git dependency and fully included
in the axiom audit. Its source hashes match the former vendored snapshot.

`WeightedProbability` defines the finite model for a nonnegative
multiplicative weight `w`, with exact normalizer `∏(1+w(p)/p)`.
Normalization, multiplicative Euler products, divisor-count moments, and
Markov’s inequality are proved. `WeightedMarginal` proves exact smaller-cutoff
marginals and prime-count layer distributions. `WeightedFrequency` proves
the one-frequency identity and finite interchange with integration. Its
exponential majorant retains the explicit correction `Σ(w(p)/p)²`.

`PolynomialWeight` uses CRT to instantiate this model with `ρ_F`.
`PolynomialSquareFactor` proves
`ρ_F(b²a) ≤ τ(b)^k ρ_F(a)` for squarefree `a`, from a uniform
prime-power root bound `ρ_F(p^ν)≤2^k`. Vanishing root counts are preserved,
including at primes shared by `a` and `b`. Irreducibility and the absence of
a fixed prime divisor supply this bound through the Nair–Tenenbaum discriminant
estimates. Together with `Δ(b²a)≤τ(b²)Δ(a)` and the convergent sum of
`τ(b)^(k+2)/b²`, this transfers the entire harmonic root sum to squarefree
support. The cutoff `floor(x)+1` matches the sieve prime set exactly.
The theorem `polynomial_short_sum_weighted_bound` consequently proves
`Σ_{x<n≤x+y} Δ(|F(n)|) ≤ C_F y E_{ρ_F,floor(x)+1}(Δ)` in the short-sum
range, without assuming a weighted mean estimate.

`WeightedEulerEstimates` separates the analytic input: a bounded prime
weight and a weighted Mertens estimate give normalizer bounds; an upper
weighted prime cosine estimate gives the one-frequency bound and
`E_w(M₂/τ) ≪ log(1+log x)`. Those prime-sum hypotheses are now
proved for `ρ_F` in `PolynomialPrimeCosine`. The sharp weighted Delta mean
is proved under `PrimeEstimates`, as described below.
The fixed-prime-divisor reduction has now been completed, as described below. These reusable analytic lemmas are instantiated in the final proof of (1.7).

## Removal of fixed prime divisors

`AffineContent` proves that the content of `H=F(qX+a)` divides `q disc(F)`
for degree at least two. The proof evaluates the discriminant Bézout identity
and uses the constant and linear Taylor coefficients. Every higher coefficient
of `H` is divisible by `q²`.

`FixedPrimeDivisors` chooses `q=(|disc(F)| degree(F)!)²` and takes `G_a` to
be the primitive part of `F(qX+a)`. For each prime dividing `q`, the extra
prime factor in `q²` beyond `q|disc(F)|` makes every coefficient of `G_a`
of degree at least two divisible by that prime. Thus its reduction is linear
or constant, and primitivity makes that reduction nonzero. All remaining
primes exceed the degree and are handled by the root bound. Consequently
`progressionPrimitive_noFixedPrime` holds for every residue, with a single
slope. The low-degree cases are included separately.

`PolynomialProgressions` proves irreducibility of `G_a` using the rational
affine algebra automorphism and Gauss’s lemma. It retains the exact content
factor in `Δ(|F(qm+a)|) ≤ τ(|content(H)|) Δ(|G_a(m)|)` and bounds the full
sum by a finite rectangle of quotient and residue indices.

`PolynomialFixedPrimeReduction` proves `polynomialMeanBound_of_noFixedPrime`:
establishing the bound for polynomials without fixed prime divisors suffices.
In detail, it proves that
establishing (1.7) for irreducible polynomials with no fixed prime divisor
implies the full `PolynomialMeanBound`. Constant polynomials are proved
directly, and the terms with zero quotient are absorbed using positivity of
`(log log 3)^(5/2)`. This completes the fixed-prime-divisor reduction without
assuming any number-field analytic theorem. The mean estimate itself is supplied by the weighted argument and
`PolynomialPrimeCosine`.

## Transfer from the weighted expectation and weighted good-set tails

`HalfIntervalSummation.sum_le_of_half_interval_bound` sums upper-half
interval estimates by strong induction. It handles odd integer endpoints and
keeps the finite initial contribution explicitly. `PolynomialMeanTransfer`
applies the short-sum reduction at `s=y=n/2`; the model cutoff
`floor(s)+1` is at most the final cutoff. Monotonicity of `(log log x)^(5/2)`
and the explicit finite initial sum complete the transfer for every `x≥3`.
Together with the fixed-prime-divisor reduction, this proves
`polynomialMeanBound_of_weighted_expectation`. Its premise is the proposition
`PolynomialWeightedExpectationBound`, not an axiom. It is now proved from
`PolynomialPrimeEstimates`; establishing the latter remains necessary to
complete (1.7).

`WeightedEventBounds` proves support-local comparisons, event partitions,
finite and countable union bounds, and restricted Markov inequalities.
`WeightedPrimeCountTail` derives factorial and Poisson-rate tails from the
exact weighted count layers. Bounded prime weights contribute the explicit
normalization error `A²`. A zero weighted prime sum is handled separately:
all positive prime-count tails then have probability zero.

`WeightedGoodSetReduction` uses the exact weighted marginals and the existing
deterministic grid discretization. `WeightedGridTail` proves the Gaussian
grid bound under the explicit assumption
`|Σ_{p<x} w(p)/p - log log x|≤B` and a uniform prime-weight bound.
`WeightedGoodSetExceptional` sums it to obtain
`P_{w,x}(E_Tᶜ)≤C/T` for `0<δ≤10⁻⁶`, uniformly in `x` and `T>1`.
The constants may depend on the fixed weight bounds and `δ`. This is the
weighted version of (2.1); it does not assert the outstanding Mertens
hypothesis for polynomial root weights or the complete weighted mean.

## Weighted initial and intermediate frequencies

`WeightedPrimeEstimates.PrimeEstimates` (in the `WeightedModel` namespace)
records a nonnegative bound on prime weights and the uniform estimate
`|Σ_{p<x} w(p) cos(θ log p)/p - log(log x/(1+|θ| log x))|≤B`
for `x≥2`, `|θ|≤2`. It has no field asserting a Delta or moment bound.
At frequency zero it implies the weighted Mertens hypothesis. A general multiplicative-expectation inequality bounds the Euler product by
its linear prime sum plus the normalizer's quadratic error.

`WeightedIntermediateFrequency` proves the interchange of weighted
expectation and integration that the high-frequency argument uses. The
intermediate-frequency estimate itself is unnecessary for the assembly, so
only its unweighted form is kept, in `IntermediateFrequency`.
`WeightedInitialFrequency` proves the one-frequency majorant, the bounded
initial-frequency integral, and its corresponding `C/R` tail.
`WeightedPrimeConsequences` also derives normalizer bounds, all fixed natural
moments of the divisor count with exponent `2^k-1`, and the previously proved
good-set exception from the same explicit prime-estimate structure.

These results use explicit prime estimates. The subsequent weighted
frequency and higher-moment arguments are now completed; the arithmetic
construction for polynomial root weights is completed below.


## Weighted high frequencies and the sharp weighted mean

`WeightedPrimeIntervals`, `WeightedTwoFrequency`, and
`WeightedHighFrequencyPrimeBound` prove the three-prime-range estimate,
uniformly in the fixed small-prime-count layer. The difference-frequency
term retains its exact regularization at the diagonal. The weighted dyadic
partition uses the original pointwise good sets and finite decomposition.
`WeightedHighFrequencyIntegration` and `WeightedHighFrequencyMean` reuse the
unweighted analytic kernel integrals to prove the `O(T)` second moment.
`WeightedSecondMomentTail.goodSetStar_exceptional_probability_bound`
combines it with the initial frequencies and the independent good-set tail.

The weighted largest-prime recurrence retains both local factors `w(p)` and
`w(m)`. Finite iteration gives the exact weighted Euler-product tail. The
prime-window averaging estimate absorbs the bounded `w(p)` into a constant,
while retaining `w(m)` in the product sum. Smoothing, the integral recurrence,
factorial error bounds, and the third-moment base case are all proved.
`WeightedPropositionTwoTwo.propositionTwoTwo_for_delta` completes the strong
induction, including the exceptional fourth-moment midpoint.

`WeightedAllMomentGoodSet` sums the moment failures with the correct Markov
denominator. The original deterministic maximum bound, a weighted finite
tail decomposition, and the weighted divisor-count second moment now prove
`WeightedModel.hooleyDelta_expectation_bound`: for any `w` with
`PrimeEstimates w`, there is `K>0` such that
`E_{w,x}(Δ) ≤ K (log log x)^(5/2)` for `x≥exp(exp 4)`.
All weight dependence is confined to the constants.

`PolynomialPrimeMean.polynomialMeanBound_of_prime_estimates` connects this
to (1.7), including the previously completed fixed-prime and short-sum
reductions. Its explicit premise `PolynomialPrimeEstimates` asks for
`Nonempty (PrimeEstimates (polynomialRootWeight F))` for irreducible `F`
without a fixed prime divisor. It contains no Delta or moment assertion.
This arithmetic input is proved in `PolynomialPrimeCosine`, completing the
polynomial consequence and the full set of named paper targets.

The individual bound `ρ_F(p)≤deg F` is also proved, using the root bound over
`ZMod p` in the Nair–Tenenbaum dependency. Consequently
`polynomialMeanBound_of_prime_cosine_estimates` reduces (1.7) to the single
explicit proposition `PolynomialPrimeCosineEstimates`: the uniform cosine
prime-sum formula above for irreducible polynomial root weights. The
number-field argument and removal of smoothing below prove this input.


## Dedekind-zeta proof of the polynomial prime estimate

The selected Tau Ceti Dedekind-zeta closure is imported from the pinned
v4.35.0 release (109 modules; no local compatibility adaptations). It supplies the
ideal-count power saving, meromorphic continuation, nonvanishing on the
line `Re s=1`, and the convergent Euler product. The root project's Mathlib
pin is retained. No prime ideal theorem is assumed.

`DedekindZetaBounds` constructs a continuous, nonzero continuation of
`(s-1)ζ_K(s)` to `Re s≥1`. Compactness gives both norm bounds on every
fixed bounded strip. `DedekindEulerLog` takes the real part of the
exponential Euler-product identity, avoiding a logarithm-branch assertion
for `ζ_K`. The higher prime powers are bounded by the convergent sum
`Σ_P N(P)⁻²`, uniformly for `Re s>1`.

Together these prove `smoothed_primeIdeal_sum_log_ratio`: at
`s=1+1/log x+iθ`, for `x≥exp 1` and `|θ|≤2`, the real part of
`Σ_P N(P)⁻ˢ` differs from `log(log x/(1+|θ|log x))` by a field-dependent
constant.

`LinearPrimeFactors` restricts Mathlib’s Kummer–Dedekind equivalence to
linear factors. `PrimitiveConductor` proves that an integral primitive
element has positive conductor exponent. `PolynomialRootField` constructs
such an element from any irreducible nonconstant integer polynomial; its
minimal polynomial is the integral normalization. `IntegralNormalizationRoots`
proves that root counts are preserved away from the leading coefficient.
Consequently `exists_numberField_rootCount_eq_normPrimes` identifies root
counts with prime-norm ideal counts outside the divisors of a positive integer.

`PrimeIdealFibers` bounds the number of primes over a rational prime by the
field degree and bounds higher-degree norms below by the square of that prime.
`HigherDegreePrimeIdeals` proves summability of their reciprocal norms.
`PrimeNormDirichlet` reindexes the degree-one sum, and `FinitePrimeCorrections`
handles the finitely many exceptions. `PolynomialSmoothedPrimeSum` obtains
the uniform smoothed root-count estimate without monicity or fixed-prime
restrictions.

`PrimeDamping` applies that result to `X` to bound the total positive damped
prime mass. The existing elementary prime-log sum bound controls the loss
below the cutoff. Together with Mertens, `PrimeDampingError` proves a uniform
bound for the total absolute difference between sharp and damped kernels.
`BoundedPrimeUnsmoothing` transfers this to any uniformly bounded real prime
coefficients. Applying it to `ρ_F(p) cos(θ log p)`, and explicitly bounding
`2 ≤ x ≤ e`, proves `polynomialPrimeCosineEstimates` on the full range.
Finally `polynomialMeanBound` establishes (1.7), and `paper_main_results`
assembles every named target.

## Independent Palomar comparison surface

`Definitions.lean` centralizes the thirty statement definitions, preserving
their original values and names. `Challenge.lean` mirrors that ordinary
Mathlib-only block and states all eight named targets plus the exact Parseval
formula and integrability. `Solution.lean` imports the proved versions.
Comparator recursively compares the fixed definitions; there are no definition
holes. The ten intentional Challenge proof holes are kept outside the Solution
and the exhaustive proof-development axiom audit. See `PALOMAR.md` for validation.
