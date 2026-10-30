module

public import BretecheTenenbaumMean.WeightedFrequency
public import BretecheTenenbaumMean.FrequencyEstimates

@[expose] public section

/-! # Analytic reductions for the weighted model

The prime-sum hypotheses in this file are explicit. In particular, no
root-weighted Mertens or cosine estimate is asserted for a polynomial.
The lemmas isolate exactly where those outstanding estimates enter.
-/

namespace BretecheTenenbaumMean.WeightedModel

open Real Finset MeasureTheory

noncomputable def primeSum (w : MultiplicativeWeight) (x : ℝ) : ℝ :=
  ∑ p ∈ primesLT x, w p / p

noncomputable def cosinePrimeSum (w : MultiplicativeWeight) (x θ : ℝ) : ℝ :=
  ∑ p ∈ primesLT x, w p * cos (θ * log p) / p

theorem abs_log_normalizer_sub_primeSum_le (w : MultiplicativeWeight) {A x : ℝ}
    (hw : ∀ p ∈ primesLT x, w p ≤ A) :
    |log (normalizer w x) - primeSum w x| ≤ A ^ 2 :=
  PrimeSums.abs_log_prod_sub_sum_le (fun p hp ↦ ⟨w.nonneg p, hw p hp⟩)

/-- A weighted reciprocal-prime estimate gives the required normalization
without any asymptotic assumptions on composite values of the weight. -/
theorem normalizer_bounds_of_prime_sum (w : MultiplicativeWeight) {A B x : ℝ}
    (hx : 2 ≤ x) (hw : ∀ p ∈ primesLT x, w p ≤ A)
    (hmean : |primeSum w x - log (log x)| ≤ B) :
    exp (-(A ^ 2 + B)) * log x ≤ normalizer w x ∧
      normalizer w x ≤ exp (A ^ 2 + B) * log x := by
  have hl : 0 < log x := log_pos (by linarith)
  have he := abs_le.1 (abs_log_normalizer_sub_primeSum_le w hw)
  have hm := abs_le.1 hmean
  constructor
  · calc
      _ = exp (-(A ^ 2 + B) + log (log x)) := by rw [exp_add, exp_log hl]
      _ ≤ exp (log (normalizer w x)) := exp_le_exp.2 (by linarith)
      _ = _ := exp_log (normalizer_pos w x)
  · calc
      _ = exp (log (normalizer w x)) := (exp_log (normalizer_pos w x)).symm
      _ ≤ exp (A ^ 2 + B + log (log x)) := exp_le_exp.2 (by linarith)
      _ = _ := by rw [exp_add, exp_log hl]

/-- The square correction in the normalized local factors is uniformly bounded. -/
theorem sum_prime_weight_sq_le (w : MultiplicativeWeight) {A x : ℝ}
    (hw : ∀ p ∈ primesLT x, w p ≤ A) :
    (∑ p ∈ primesLT x, (w p / p) ^ 2) ≤ A ^ 2 := by
  calc
    _ ≤ ∑ p ∈ primesLT x, A ^ 2 * ((p : ℝ)⁻¹) ^ 2 := by
      apply sum_le_sum
      intro p hp
      rw [div_eq_mul_inv, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (w.nonneg p) (hw p hp) 2) (sq_nonneg _)
    _ = A ^ 2 * ∑ p ∈ primesLT x, ((p : ℝ)⁻¹) ^ 2 := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_of_le_one_right (sq_nonneg _) (PrimeSums.sum_prime_inv_sq_le_one x)

/-- The only arithmetic input for the unrestricted one-frequency mean is
an upper bound for the root-weighted prime cosine sum. -/
theorem expectation_normalizedPolynomial_le_of_cosine (w : MultiplicativeWeight)
    {A B x θ : ℝ} (hx : 2 ≤ x) (hθ : 0 ≤ θ)
    (hw : ∀ p ∈ primesLT x, w p ≤ A)
    (hcos : cosinePrimeSum w x θ ≤ B + log (log x / (1 + θ * log x))) :
    expectation w x (fun n ↦ normalizedPolynomial n θ) ≤
      exp (A ^ 2 + B) * (log x / (1 + θ * log x)) := by
  have hl : 0 < log x := log_pos (by linarith)
  have hr : 0 < log x / (1 + θ * log x) := div_pos hl (by positivity)
  calc
    _ ≤ exp (cosinePrimeSum w x θ + ∑ p ∈ primesLT x, (w p / p) ^ 2) :=
      expectation_normalizedPolynomial_le_exp w x θ
    _ ≤ exp (A ^ 2 + B + log (log x / (1 + θ * log x))) :=
      exp_le_exp.2 (by linarith [sum_prime_weight_sq_le w hw])
    _ = _ := by rw [exp_add, exp_log hr]

end BretecheTenenbaumMean.WeightedModel
