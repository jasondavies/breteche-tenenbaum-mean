module

public import BretecheTenenbaumMean.SmallPrimePolynomial
public import BretecheTenenbaumMean.PrimePartition

@[expose] public section

/-! # The two-frequency weight in the high-frequency argument -/

namespace BretecheTenenbaumMean

open Real Finset

/-- The square-root divisor-count factors extracted using the good set. -/
noncomputable def twoFrequencyWeight (n : ℕ) (a b θ φ : ℝ) : ℝ :=
  (normalizedPolynomial n θ * normalizedPolynomial n φ) /
    sqrt (tau (smallPrimePart n a) * tau (smallPrimePart n b))

theorem twoFrequencyWeight_nonneg (n : ℕ) (a b θ φ : ℝ) : 0 ≤ twoFrequencyWeight n a b θ φ :=
  div_nonneg (mul_nonneg (normalizedPolynomial_nonneg n θ) (normalizedPolynomial_nonneg n φ))
    (sqrt_nonneg _)

@[simp] theorem twoFrequencyWeight_one (a b θ φ : ℝ) : twoFrequencyWeight 1 a b θ φ = 1 := by
  simp [twoFrequencyWeight]

theorem twoFrequencyWeight_mul {m n : ℕ} (hmn : m.Coprime n) (a b θ φ : ℝ) :
    twoFrequencyWeight (m * n) a b θ φ =
      twoFrequencyWeight m a b θ φ * twoFrequencyWeight n a b θ φ := by
  simp only [twoFrequencyWeight, normalizedPolynomial_mul hmn, smallPrimePart_mul hmn,
    tau_mul_of_coprime (smallPrimePart_coprime hmn a),
    tau_mul_of_coprime (smallPrimePart_coprime hmn b)]
  have he : (tau (smallPrimePart m a) * tau (smallPrimePart n a)) *
      (tau (smallPrimePart m b) * tau (smallPrimePart n b)) =
      (tau (smallPrimePart m a) * tau (smallPrimePart m b)) *
      (tau (smallPrimePart n a) * tau (smallPrimePart n b)) := by ring
  rw [he, sqrt_mul (mul_nonneg (tau_pos (smallPrimePart_ne_zero m a)).le
    (tau_pos (smallPrimePart_ne_zero m b)).le)]
  ring

/-- The primewise majorant on the three consecutive ranges. -/
noncomputable def threeRangeWeight (p : ℕ) (a b θ φ : ℝ) : ℝ :=
  if (p : ℝ) < a then 2
  else if (p : ℝ) < b then sqrt 2 * (1 + cos (φ * log p))
  else (1 + cos (θ * log p)) * (1 + cos (φ * log p))

theorem threeRangeWeight_nonneg (p : ℕ) (a b θ φ : ℝ) : 0 ≤ threeRangeWeight p a b θ φ := by
  have hθ : 0 ≤ 1 + cos (θ * log p) := by linarith [neg_one_le_cos (θ * log p)]
  have hφ : 0 ≤ 1 + cos (φ * log p) := by linarith [neg_one_le_cos (φ * log p)]
  unfold threeRangeWeight
  split_ifs <;> positivity

/-- The small range costs two per prime; the middle range costs `√2 (1+cos φ log p)`. -/
theorem twoFrequencyWeight_prime_le {p : ℕ} (hp : p.Prime) {a b : ℝ} (hab : a ≤ b) (θ φ : ℝ) :
    twoFrequencyWeight p a b θ φ ≤ threeRangeWeight p a b θ φ := by
  have hθ : 0 ≤ 1 + cos (θ * log p) := by linarith [neg_one_le_cos (θ * log p)]
  have hφ : 0 ≤ 1 + cos (φ * log p) := by linarith [neg_one_le_cos (φ * log p)]
  have hθ2 : 1 + cos (θ * log p) ≤ 2 := by linarith [cos_le_one (θ * log p)]
  have hφ2 : 1 + cos (φ * log p) ≤ 2 := by linarith [cos_le_one (φ * log p)]
  simp only [twoFrequencyWeight, normalizedPolynomial_prime hp, smallPrimePart_prime hp,
    threeRangeWeight]
  by_cases hpa : (p : ℝ) < a
  · have hpb := hpa.trans_le hab
    simp only [hpa, hpb, ite_true, tau_prime hp]
    norm_num
    nlinarith [mul_le_mul hθ2 hφ2 hφ (by norm_num : (0 : ℝ) ≤ 2)]
  · simp only [hpa, ite_false, tau_one, one_mul]
    by_cases hpb : (p : ℝ) < b
    · simp only [hpb, ite_true, tau_prime hp]
      have hs : 0 < sqrt (2 : ℝ) := sqrt_pos.2 (by norm_num)
      rw [div_le_iff₀ hs]
      have hsq := sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      nlinarith [mul_le_mul_of_nonneg_right hθ2 hφ]
    · simp only [hpb, ite_false, tau_one, sqrt_one, div_one, le_refl]

end BretecheTenenbaumMean
