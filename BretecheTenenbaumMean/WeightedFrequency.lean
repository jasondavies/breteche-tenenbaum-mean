module

public import BretecheTenenbaumMean.FrequencyAverage
public import BretecheTenenbaumMean.WeightedProbability

@[expose] public section

/-! # Frequency identities for multiplicative weights

These identities and the compact-frequency second-moment comparison use only
nonnegativity and multiplicativity. The arithmetic estimates for polynomial
root-weighted prime sums are separate proof obligations.
-/

namespace BretecheTenenbaumMean.WeightedModel

open Real Finset MeasureTheory

theorem integral_expectation (w : MultiplicativeWeight) (x a b : ℝ)
    (f : ℕ → ℝ → ℝ)
    (hf : ∀ n ∈ smoothSupport x, IntervalIntegrable (f n) volume a b) :
    (∫ t in a..b, expectation w x (fun n ↦ f n t)) =
      expectation w x (fun n ↦ ∫ t in a..b, f n t) := by
  unfold expectation
  rw [intervalIntegral.integral_div]
  congr 1
  rw [intervalIntegral.integral_finsetSum
    (fun n hn ↦ ((hf n hn).const_mul (w n)).div_const (n : ℝ))]
  apply sum_congr rfl
  intro n _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul]

theorem expectation_normalizedPolynomial (w : MultiplicativeWeight) (x θ : ℝ) :
    expectation w x (fun n ↦ normalizedPolynomial n θ) =
      (∏ p ∈ primesLT x, (1 + w p * (1 + cos (θ * log p)) / p)) / normalizer w x := by
  rw [expectation_multiplicative w x _ (normalizedPolynomial_one θ)
    (fun _ _ h ↦ normalizedPolynomial_mul h θ)]
  congr 1
  exact prod_congr rfl (fun p hp ↦ by
    rw [normalizedPolynomial_prime (mem_primesLT.mp hp).1])

@[fun_prop]
theorem continuous_expectation_normalizedPolynomial (w : MultiplicativeWeight) (x : ℝ) :
    Continuous (fun θ ↦ expectation w x (fun n ↦ normalizedPolynomial n θ)) := by
  unfold expectation normalizedPolynomial
  apply Continuous.div_const
  apply continuous_finsetSum
  intro n _
  exact (((((continuous_divisorPolynomial n).norm.pow 2).div_const (tau n)).const_mul
    (w n)).div_const (n : ℝ))

/-- An exact local-factor form separates the oscillation from normalization. -/
theorem expectation_normalizedPolynomial_eq_product (w : MultiplicativeWeight) (x θ : ℝ) :
    expectation w x (fun n ↦ normalizedPolynomial n θ) =
      ∏ p ∈ primesLT x, (1 + (w p / (p + w p)) * cos (θ * log p)) := by
  rw [expectation_normalizedPolynomial, normalizer, ← prod_div_distrib]
  apply prod_congr rfl
  intro p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_primesLT.1 hp).1.pos
  have hwp := w.nonneg p
  have hd : (p : ℝ) + w p ≠ 0 := by positivity
  field_simp
  ring

/-- The normalized Euler product is controlled by the corresponding prime
cosine sum, with an explicit summable correction for local normalization. -/
theorem expectation_normalizedPolynomial_le_exp (w : MultiplicativeWeight) (x θ : ℝ) :
    expectation w x (fun n ↦ normalizedPolynomial n θ) ≤
      exp ((∑ p ∈ primesLT x, w p * cos (θ * log p) / p) +
        ∑ p ∈ primesLT x, (w p / p) ^ 2) := by
  rw [expectation_normalizedPolynomial_eq_product]
  calc
    _ ≤ ∏ p ∈ primesLT x, exp ((w p / (p + w p)) * cos (θ * log p)) := by
      apply prod_le_prod₀
      · intro p hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_primesLT.1 hp).1.pos
        have hw := w.nonneg p
        have hd : 0 < (p : ℝ) + w p := by positivity
        have ha0 : 0 ≤ w p / (p + w p) := div_nonneg hw hd.le
        have ha1 : w p / (p + w p) ≤ 1 := (div_le_one hd).2 (by linarith)
        nlinarith [neg_one_le_cos (θ * log p)]
      · intro p _
        linarith [add_one_le_exp ((w p / (p + w p)) * cos (θ * log p))]
    _ = exp (∑ p ∈ primesLT x, (w p / (p + w p)) * cos (θ * log p)) :=
      (exp_sum _ _).symm
    _ ≤ _ := by
      apply exp_le_exp.2
      rw [← sum_add_distrib]
      apply sum_le_sum
      intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_primesLT.1 hp).1.pos
      have hw := w.nonneg p
      have hd : 0 < (p : ℝ) + w p := by positivity
      have he : w p / p - w p / (p + w p) = (w p / p) ^ 2 * (p / (p + w p)) := by
        field_simp
        ring
      have hfrac0 : 0 ≤ (p : ℝ) / (p + w p) := div_nonneg hp0.le hd.le
      have hfrac1 : (p : ℝ) / (p + w p) ≤ 1 := (div_le_one hd).2 (by linarith)
      have hdiff0 : 0 ≤ w p / p - w p / (p + w p) := by rw [he]; positivity
      have hdiff1 : w p / p - w p / (p + w p) ≤ (w p / p) ^ 2 := by
        rw [he]
        exact mul_le_of_le_one_right (sq_nonneg _) hfrac1
      have hc := neg_one_le_cos (θ * log p)
      have h := mul_nonneg hdiff0 (show 0 ≤ 1 + cos (θ * log p) by linarith)
      rw [mul_div_right_comm]
      nlinarith

end BretecheTenenbaumMean.WeightedModel
