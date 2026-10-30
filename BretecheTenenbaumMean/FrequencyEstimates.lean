module

public import BretecheTenenbaumMean.PrimeSums.Intervals
public import BretecheTenenbaumMean.PrimeSums.Product
public import BretecheTenenbaumMean.FrequencyAverage

@[expose] public section

/-! # Uniform bounds for the frequency averages

These estimates make the initial frequency range in §2.2 bounded and give
the unrestricted logarithmic mean bound for the normalized second moment.
-/

namespace BretecheTenenbaumMean

open Real Finset MeasureTheory
open PrimeSums

theorem sum_primesLT_one_add_cos_le (x θ : ℝ) :
    (∑ p ∈ primesLT x, (1 + cos (θ * log p)) / p) ≤ S x + cosinePrimeSum x θ := by
  rw [primesLT, sum_filter, S_eq_sum, cosinePrimeSum, ← sum_add_distrib]
  apply sum_le_sum
  intro p _
  by_cases hp : p.Prime
  · by_cases hpx : (p : ℝ) < x
    · simp only [hp, hpx, and_self, ite_true]
      exact le_of_eq (by ring)
    · simp only [hp, hpx, and_false, ite_false, ite_true]
      have hc := neg_one_le_cos (θ * log p)
      have : 0 ≤ (1 + cos (θ * log p)) / (p : ℝ) := div_nonneg (by linarith) (by positivity)
      convert this using 1
      ring
  · simp [hp]

theorem log_polynomial_euler_le (x θ : ℝ) :
    log (∏ p ∈ primesLT x, (1 + (1 + cos (θ * log p)) / p)) ≤ S x + cosinePrimeSum x θ := by
  have hw (p : ℕ) : 0 ≤ (1 + cos (θ * log p)) / (p : ℝ) :=
    div_nonneg (by linarith [neg_one_le_cos (θ * log p)]) (by positivity)
  have hp : ∀ p ∈ primesLT x, 0 < 1 + (1 + cos (θ * log p)) / p := fun p _ ↦ by
    have := hw p
    linarith
  rw [log_prod (fun p h ↦ (hp p h).ne')]
  refine (sum_le_sum (fun p h ↦ ?_)).trans (sum_primesLT_one_add_cos_le x θ)
  have h := log_le_sub_one_of_pos (hp p h)
  linarith

/-- The one-frequency mean is bounded by `C log x / (1 + θ log x)`, uniformly
for `x ≥ 2` and `0 ≤ θ ≤ 1`. -/
theorem expectation_normalizedPolynomial_le : ∃ C > 0, ∀ x θ,
    2 ≤ x → 0 ≤ θ → θ ≤ 1 →
    expectation x (fun n ↦ normalizedPolynomial n θ) ≤ C * (log x / (1 + θ * log x)) := by
  obtain ⟨K₁, _, hK₁⟩ := abs_S_sub_loglog_le
  obtain ⟨K₂, _, hK₂⟩ := cosinePrimeSum_log_ratio
  obtain ⟨c, _, hc, _, hnorm⟩ := normalizer_bounds
  refine ⟨exp (K₁ + K₂) / c, div_pos (exp_pos _) hc, fun x θ hx hθ hθ1 ↦ ?_⟩
  have hl : 0 < log x := log_pos (by linarith)
  have hd : 0 < 1 + θ * log x := by positivity
  have hr : 0 < log x / (1 + θ * log x) := div_pos hl hd
  have hsum : log (∏ p ∈ primesLT x, (1 + (1 + cos (θ * log p)) / p)) ≤
      K₁ + K₂ + log (log x) + log (log x / (1 + θ * log x)) := by
    have h1 := (abs_le.1 (hK₁ x hx)).2
    have h2 := (abs_le.1 (hK₂ x θ hx hθ hθ1)).2
    have h3 := log_polynomial_euler_le x θ
    linarith
  have hp : 0 < ∏ p ∈ primesLT x, (1 + (1 + cos (θ * log p)) / p) := by
    apply prod_pos
    intro p _
    have : 0 ≤ (1 + cos (θ * log p)) / (p : ℝ) :=
      div_nonneg (by linarith [neg_one_le_cos (θ * log p)]) (by positivity)
    linarith
  have hprod : (∏ p ∈ primesLT x, (1 + (1 + cos (θ * log p)) / p)) ≤
      exp (K₁ + K₂) * log x * (log x / (1 + θ * log x)) := by
    calc _ = exp (log (∏ p ∈ primesLT x, (1 + (1 + cos (θ * log p)) / p))) := (exp_log hp).symm
         _ ≤ exp (K₁ + K₂ + log (log x) + log (log x / (1 + θ * log x))) := exp_le_exp.2 hsum
         _ = _ := by rw [exp_add, exp_add, exp_log hl, exp_log hr]
  rw [expectation_normalizedPolynomial]
  calc _ ≤ (exp (K₁ + K₂) * log x * (log x / (1 + θ * log x))) / (c * log x) :=
          div_le_div₀ (by positivity) hprod (mul_pos hc hl) (hnorm x hx).1
       _ = _ := by field_simp

theorem continuous_expectation_normalizedPolynomial (x : ℝ) :
    Continuous (fun θ ↦ expectation x (fun n ↦ normalizedPolynomial n θ)) := by
  unfold expectation normalizedPolynomial
  apply Continuous.div_const
  apply continuous_finsetSum
  intro n _
  exact ((((continuous_divisorPolynomial n).norm.pow 2).div_const (tau n)).div_const (n : ℝ))

/-- The integral of the one-frequency majorant. -/
theorem integral_log_div_one_add {x b : ℝ} (hx : 2 ≤ x) (hb : 0 ≤ b) :
    (∫ θ in (0 : ℝ)..b, log x / (1 + θ * log x)) = log (1 + b * log x) := by
  have hl : 0 < log x := log_pos (by linarith)
  have hd : ∀ θ ∈ Set.uIcc 0 b, 0 < 1 + θ * log x := by
    intro θ hθ
    rw [Set.uIcc_of_le hb] at hθ
    nlinarith [hθ.1]
  have hi : IntervalIntegrable (fun θ ↦ log x / (1 + θ * log x)) volume 0 b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    exact fun θ hθ ↦ (hd θ hθ).ne'
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun θ ↦ log (1 + θ * log x))
    (fun θ hθ ↦ ?_) hi
  · simpa only [zero_mul, add_zero, log_one, sub_zero] using he
  · convert (((hasDerivAt_id θ).mul_const (log x)).const_add 1).log (hd θ hθ).ne' using 1
    · ext t
      rfl
    · simp only [id_eq, one_mul]

/-- The unrestricted normalized second moment has logarithmic-logarithmic mean. -/
theorem expectation_moment_two_log_bound : ∃ C > 0, ∀ x ≥ 2,
    expectation x (fun n ↦ moment 2 n / tau n) ≤ C * log (1 + log x) := by
  obtain ⟨C, hC, h⟩ := expectation_normalizedPolynomial_le
  refine ⟨(π ^ 2 / 2) * C, mul_pos (by positivity) hC, fun x hx ↦ ?_⟩
  have hl : 0 < log x := log_pos (by linarith)
  have hcont : ContinuousOn (fun θ ↦ C * (log x / (1 + θ * log x))) (Set.uIcc 0 1) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro θ hθ
    rw [Set.uIcc_of_le zero_le_one] at hθ
    have : 0 ≤ θ := hθ.1
    positivity
  have hi : (∫ θ in (0 : ℝ)..1, expectation x (fun n ↦ normalizedPolynomial n θ)) ≤
      C * log (1 + log x) := by
    calc _ ≤ ∫ θ in (0 : ℝ)..1, C * (log x / (1 + θ * log x)) := by
            apply intervalIntegral.integral_mono_on zero_le_one
              ((continuous_expectation_normalizedPolynomial x).intervalIntegrable _ _)
              hcont.intervalIntegrable
            intro θ hθ
            exact h x θ hx hθ.1 hθ.2
         _ = _ := by
            rw [intervalIntegral.integral_const_mul, integral_log_div_one_add hx zero_le_one, one_mul]
  have hfourier := expectation_moment_two_le x
  simp_rw [← expectation_normalizedPolynomial] at hfourier
  calc _ ≤ (π ^ 2 / 2) * (∫ θ in (0 : ℝ)..1, expectation x (fun n ↦ normalizedPolynomial n θ)) := hfourier
       _ ≤ (π ^ 2 / 2) * (C * log (1 + log x)) := mul_le_mul_of_nonneg_left hi (by positivity)
       _ = _ := by ring

end BretecheTenenbaumMean
