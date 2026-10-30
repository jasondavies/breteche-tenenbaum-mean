module

public import BretecheTenenbaumMean.FourierComparison
public import BretecheTenenbaumMean.PolynomialExpectation

@[expose] public section

/-! # Averaging the compact-frequency comparison

The finite support permits interchange with integration without any uniform
integrability assumption in the cutoff. No prime-sum estimate is assumed here.
-/

namespace BretecheTenenbaumMean

open Real MeasureTheory

theorem integral_expectation (x a b : ℝ) (f : ℕ → ℝ → ℝ)
    (hf : ∀ n ∈ smoothSupport x, IntervalIntegrable (f n) volume a b) :
    (∫ t in a..b, expectation x (fun n => f n t)) =
      expectation x (fun n => ∫ t in a..b, f n t) := by
  unfold expectation
  rw [intervalIntegral.integral_div]
  congr 1
  rw [intervalIntegral.integral_finsetSum (fun n hn => (hf n hn).div_const (n : ℝ))]
  exact Finset.sum_congr rfl (fun n _ => intervalIntegral.integral_div (n : ℝ) (f n))

/-- An explicit finite Euler-product integral bounds the mean normalized second moment. -/
theorem expectation_moment_two_le (x : ℝ) :
    expectation x (fun n => moment 2 n / tau n) ≤ (π ^ 2 / 2) *
      ∫ θ in (0 : ℝ)..1,
        (∏ p ∈ primesLT x, (1 + (1 + cos (θ * log p)) / p)) / normalizer x := by
  have hi (n : ℕ) : IntervalIntegrable (normalizedPolynomial n) volume 0 1 :=
    (((continuous_divisorPolynomial n).norm.pow 2).div_const (tau n)).intervalIntegrable _ _
  calc
    expectation x (fun n => moment 2 n / tau n) ≤
        expectation x (fun n => (π ^ 2 / 2) * ∫ θ in (0 : ℝ)..1, normalizedPolynomial n θ) :=
      expectation_mono x (fun n _ => normalized_moment_two_le_fourier_integral n)
    _ = (π ^ 2 / 2) * expectation x (fun n => ∫ θ in (0 : ℝ)..1, normalizedPolynomial n θ) :=
      expectation_const_mul _ _ _
    _ = (π ^ 2 / 2) * ∫ θ in (0 : ℝ)..1,
        expectation x (fun n => normalizedPolynomial n θ) := by
      rw [integral_expectation x 0 1 normalizedPolynomial (fun n _ => hi n)]
    _ = _ := by simp_rw [expectation_normalizedPolynomial]

end BretecheTenenbaumMean
