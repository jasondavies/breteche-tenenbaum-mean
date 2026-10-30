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

/-- The high-frequency multiplicative sum on a fixed small-prime layer is
bounded by an elementary-symmetric sum times a finite Euler product. -/
theorem twoFrequency_layer_product_bound (x a b θ φ : ℝ) (r : ℕ) (hab : a ≤ b) :
    (∑ n ∈ smoothSupport x, if (smallPrimePart n a).primeFactors.card = r
      then twoFrequencyWeight n a b θ φ / n else 0) ≤
      distinctProductSum ((primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < a))
        (fun p ↦ threeRangeWeight p a b θ φ / p) r *
      ∏ p ∈ primesLT x \ (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < a),
        (1 + threeRangeWeight p a b θ φ / p) :=
  sum_smallPrime_layer_le_product x a r
    (fun n ↦ twoFrequencyWeight n a b θ φ) (fun p ↦ threeRangeWeight p a b θ φ)
    (twoFrequencyWeight_one a b θ φ) (fun _ _ h ↦ twoFrequencyWeight_mul h a b θ φ)
    (fun _p _ ↦ twoFrequencyWeight_nonneg _p a b θ φ)
    (fun _p hp ↦ twoFrequencyWeight_prime_le (mem_primesLT.1 hp).1 hab θ φ)

/-- The factorial form of the three-range estimate, before prime-sum asymptotics.
Every endpoint follows the strict cutoff in `smallPrimePart`. -/
theorem twoFrequency_layer_factorial_bound (x a b θ φ : ℝ) (r : ℕ) (hab : a ≤ b) :
    (∑ n ∈ smoothSupport x, if (smallPrimePart n a).primeFactors.card = r
      then twoFrequencyWeight n a b θ φ / n else 0) ≤
      ((2 * ∑ p ∈ (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < a), (p : ℝ)⁻¹) ^ r /
        (r.factorial : ℝ)) *
      exp (∑ p ∈ primesLT x \ (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < a),
        threeRangeWeight p a b θ φ / p) := by
  let A := (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < a)
  let w := fun p ↦ threeRangeWeight p a b θ φ / (p : ℝ)
  have hw : ∀ p, 0 ≤ w p := fun p ↦
    div_nonneg (threeRangeWeight_nonneg p a b θ φ) (Nat.cast_nonneg p)
  have hs : (∑ p ∈ A, w p) = 2 * ∑ p ∈ A, (p : ℝ)⁻¹ := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p hp
    have hpa := (mem_filter.1 hp).2
    simp only [w, threeRangeWeight, hpa, ite_true, div_eq_mul_inv]
  have hsym := distinctProductSum_le A w r (fun p _ ↦ hw p)
  rw [hs] at hsym
  have heuler := prod_one_add_le_exp_sum (primesLT x \ A) hw
  refine (twoFrequency_layer_product_bound x a b θ φ r hab).trans ?_
  exact mul_le_mul hsym heuler
    (prod_nonneg (fun p _ ↦ by have := hw p; change 0 ≤ 1 + w p; linarith))
    (by positivity)

/-- Uniformly in the layer index, the small-prime range gives a square-root saving. -/
theorem twoFrequency_layer_uniform (x a b θ φ : ℝ) (r : ℕ) (hab : a ≤ b) :
    (∑ n ∈ smoothSupport x, if (smallPrimePart n a).primeFactors.card = r
      then twoFrequencyWeight n a b θ φ / n else 0) ≤
      (8 * exp (2 * ∑ p ∈ (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < a), (p : ℝ)⁻¹) /
        sqrt (1 + 2 * ∑ p ∈ (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < a), (p : ℝ)⁻¹)) *
      exp (∑ p ∈ primesLT x \ (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < a),
        threeRangeWeight p a b θ φ / p) :=
  (twoFrequency_layer_factorial_bound x a b θ φ r hab).trans
    (mul_le_mul_of_nonneg_right (factorial_term_uniform (by positivity) r) (exp_pos _).le)

end BretecheTenenbaumMean
