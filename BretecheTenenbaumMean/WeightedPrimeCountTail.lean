module

public import BretecheTenenbaumMean.PoissonRate
public import BretecheTenenbaumMean.PrimeLayers
public import BretecheTenenbaumMean.WeightedEventBounds
public import BretecheTenenbaumMean.WeightedMarginal
public import BretecheTenenbaumMean.WeightedEulerEstimates
public import BretecheTenenbaumMean.PrimeCountTail

@[expose] public section

/-! # Weighted upper tails for prime and divisor counts -/

namespace BretecheTenenbaumMean.WeightedModel

open Real Finset

/-- Summing the fixed prime-count layers gives a geometric factorial-tail bound. -/
theorem probability_prime_ge_le (w : MultiplicativeWeight) (x : ℝ) {ρ : ℝ} {k : ℕ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hk : (∑ p ∈ primesLT x, w p / p) ≤ ρ * (k + 1)) :
    probability w x {n | k ≤ n.primeFactors.card} ≤
      poissonTerm (∑ p ∈ primesLT x, w p / p) k / ((1 - ρ) * normalizer w x) := by
  classical
  let u := ∑ p ∈ primesLT x, w p / p
  have hu : 0 ≤ u := sum_nonneg (fun p _ ↦ div_nonneg (w.nonneg p) (Nat.cast_nonneg _))
  let s := ((smoothSupport x).image (fun n ↦ n.primeFactors.card)).filter (fun r ↦ k ≤ r)
  rw [probability_ge_eq_sum_fibers w x (fun n ↦ n.primeFactors.card) k]
  calc (∑ r ∈ s, probability w x {n | n.primeFactors.card = r})
      ≤ ∑ r ∈ s, poissonTerm u r / normalizer w x := by
        apply sum_le_sum
        intro r _
        rw [probability_prime_layer_eq]
        apply div_le_div_of_nonneg_right _ (normalizer_pos w x).le
        exact distinctProductSum_le _ _ _ (fun p _ ↦ div_nonneg (w.nonneg p) (Nat.cast_nonneg _))
    _ = (∑ r ∈ s, poissonTerm u r) / normalizer w x := (sum_div _ _ _).symm
    _ ≤ (poissonTerm u k / (1 - ρ)) / normalizer w x :=
      div_le_div_of_nonneg_right (sum_poissonTerm_tail_le hu hρ hρ1 hk s
        (fun r hr ↦ (mem_filter.1 hr).2)) (normalizer_pos w x).le
    _ = _ := by rw [div_div]

/-- The prime-count upper tail with its large-deviation exponential and
square-root saving. No approximation or rounding of the threshold is used. -/
theorem probability_prime_ge_le_rate (w : MultiplicativeWeight) (x : ℝ) {ρ : ℝ} {k : ℕ}
    (hu : 0 < ∑ p ∈ primesLT x, w p / p) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hk0 : k ≠ 0)
    (hk : (∑ p ∈ primesLT x, w p / p) ≤ ρ * (k + 1)) :
    probability w x {n | k ≤ n.primeFactors.card} ≤
      exp ((∑ p ∈ primesLT x, w p / p) *
        (1 - poissonRate (k / (∑ p ∈ primesLT x, w p / p)))) /
        ((1 - ρ) * sqrt (2 * π * k) * normalizer w x) := by
  refine (probability_prime_ge_le w x hρ hρ1 hk).trans ?_
  have hd : 0 ≤ (1 - ρ) * normalizer w x := mul_nonneg (by linarith) (normalizer_pos w x).le
  have h := div_le_div_of_nonneg_right (poissonTerm_le_rate hu hk0) hd
  convert h using 1
  rw [div_div]
  congr 1
  ring

/-- The exact equality of divisor and prime-count tail events on the support. -/
theorem probability_tau_ge_eq (w : MultiplicativeWeight) (x : ℝ) {R : ℝ} (hR : 0 < R) :
    probability w x {n | R ≤ tau n} = probability w x {n | ⌈log R / log 2⌉₊ ≤ n.primeFactors.card} := by
  apply probability_congr_on_support
  intro n hn
  exact tau_ge_iff_prime_count_ge_ceil (mem_smoothSupport.1 hn).1 hR

/-- Normalization cancels the leading Poisson exponential with a bounded
prime-weight correction. -/
theorem probability_prime_ge_exp_rate (w : MultiplicativeWeight) (x : ℝ) {A ρ : ℝ} {k : ℕ}
    (hw : ∀ p ∈ primesLT x, w p ≤ A)
    (hu : 0 < primeSum w x) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hk0 : k ≠ 0)
    (hk : primeSum w x ≤ ρ * (k + 1)) :
    probability w x {n | k ≤ n.primeFactors.card} ≤
      exp (A ^ 2 - primeSum w x * poissonRate (k / primeSum w x)) /
        ((1 - ρ) * sqrt (2 * π * k)) := by
  have hnorm := abs_le.1 (abs_log_normalizer_sub_primeSum_le w hw)
  have he : exp (primeSum w x * (1 - poissonRate (k / primeSum w x))) / normalizer w x ≤
      exp (A ^ 2 - primeSum w x * poissonRate (k / primeSum w x)) := by
    rw [← exp_log (normalizer_pos w x), ← exp_sub]
    apply exp_le_exp.2
    linarith [hnorm.1]
  have hd : 0 ≤ (1 - ρ) * sqrt (2 * π * k) := by positivity
  have h := div_le_div_of_nonneg_right he hd
  refine (probability_prime_ge_le_rate w x hu hρ hρ1 hk0 hk).trans ?_
  convert h using 1
  rw [div_div]
  congr 1
  ring

/-- A vanishing mean parameter makes every positive prime-count tail zero.
This case matters for root weights that vanish at all primes below a cutoff. -/
theorem probability_prime_ge_eq_zero (w : MultiplicativeWeight) (x : ℝ)
    (hu : primeSum w x = 0) {k : ℕ} (hk : k ≠ 0) :
    probability w x {n | k ≤ n.primeFactors.card} = 0 := by
  apply le_antisymm _ (probability_nonneg w x _)
  have h := probability_prime_ge_le w x (ρ := 0) (by norm_num) (by norm_num)
    (k := k) (by change primeSum w x ≤ _; rw [hu]; simp)
  change probability w x _ ≤ poissonTerm (primeSum w x) k / _ at h
  simpa [hu, poissonTerm, hk] using h

end BretecheTenenbaumMean.WeightedModel
