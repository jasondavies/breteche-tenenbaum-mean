module

public import BretecheTenenbaumMean.DivisorPolynomial
public import BretecheTenenbaumMean.FejerKernel
public import BretecheTenenbaumMean.SecondMoment

@[expose] public section

/-! # The compact-frequency comparison (2.7)

A direct Fejér-kernel proof gives an explicit constant `π²/2`. Expanding a
triangularly weighted frequency integral produces a nonnegative kernel on
every divisor pair, which dominates the unit triangular overlap kernel.
Thus this special comparison does not require a general Montgomery–Wirsing
theorem or the global Parseval identity (2.6).
-/

namespace BretecheTenenbaumMean

open Real MeasureTheory

theorem integral_weighted_norm_sq (n : ℕ) :
    (∫ θ in (0 : ℝ)..1, (1 - θ) * ‖divisorPolynomial n θ‖ ^ 2) =
      ∑ d ∈ n.divisors, ∑ e ∈ n.divisors, fejerKernel (log d - log e) := by
  have hi (d e : ℕ) : IntervalIntegrable
      (fun θ : ℝ => (1 - θ) * cos (θ * (log d - log e))) volume 0 1 :=
    (by fun_prop : Continuous
      (fun θ : ℝ => (1 - θ) * cos (θ * (log d - log e)))).intervalIntegrable _ _
  have hi' (d : ℕ) : IntervalIntegrable
      (fun θ : ℝ => ∑ e ∈ n.divisors, (1 - θ) * cos (θ * (log d - log e))) volume 0 1 :=
    (by fun_prop : Continuous
      (fun θ : ℝ => ∑ e ∈ n.divisors, (1 - θ) * cos (θ * (log d - log e)))).intervalIntegrable _ _
  simp_rw [norm_sq_divisorPolynomial_eq_sum, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum (fun (d : ℕ) _ => hi' d)]
  apply Finset.sum_congr rfl
  intro d _
  rw [intervalIntegral.integral_finsetSum (fun (e : ℕ) _ => hi d e)]
  simp_rw [integral_triangular_cos]

theorem moment_two_le_fourier_integral (n : ℕ) :
    moment 2 n ≤ (π ^ 2 / 2) * ∫ θ in (0 : ℝ)..1, ‖divisorPolynomial n θ‖ ^ 2 := by
  have hc := (continuous_divisorPolynomial n).norm.pow 2
  have hw : Continuous (fun θ : ℝ => (1 - θ) * ‖divisorPolynomial n θ‖ ^ 2) :=
    (continuous_const.sub continuous_id).mul hc
  calc
    moment 2 n ≤ (π ^ 2 / 2) *
        (∑ d ∈ n.divisors, ∑ e ∈ n.divisors, fejerKernel (log d - log e)) := by
      rw [moment_two_eq_sum]
      simp only [Finset.mul_sum]
      exact Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun e _ =>
        triangle_le_fejerKernel (log d - log e)
    _ = (π ^ 2 / 2) * ∫ θ in (0 : ℝ)..1, (1 - θ) * ‖divisorPolynomial n θ‖ ^ 2 := by
      rw [integral_weighted_norm_sq]
    _ ≤ (π ^ 2 / 2) * ∫ θ in (0 : ℝ)..1, ‖divisorPolynomial n θ‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply intervalIntegral.integral_mono_on (by norm_num) (hw.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)
      intro θ hθ
      exact mul_le_of_le_one_left (sq_nonneg _) (by linarith [hθ.1])

/-- Equation (2.7), with the divisor-count normalization inside the integral. -/
theorem normalized_moment_two_le_fourier_integral (n : ℕ) :
    moment 2 n / tau n ≤ (π ^ 2 / 2) *
      ∫ θ in (0 : ℝ)..1, ‖divisorPolynomial n θ‖ ^ 2 / tau n := by
  rw [intervalIntegral.integral_div]
  simpa only [mul_div_assoc, tau] using div_le_div_of_nonneg_right
    (moment_two_le_fourier_integral n) (Nat.cast_nonneg n.divisors.card)

end BretecheTenenbaumMean
