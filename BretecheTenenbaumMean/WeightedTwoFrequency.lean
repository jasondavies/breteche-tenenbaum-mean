module

public import BretecheTenenbaumMean.TwoFrequencyWeight
public import BretecheTenenbaumMean.WeightedProbability

@[expose] public section

/-! # Weighted two-frequency sums with a fixed small-prime count -/

namespace BretecheTenenbaumMean.WeightedModel

open Real Finset

/-- The existing multiplicative partition lemma also applies to the product
of the arithmetic weight and the two-frequency test function. -/
theorem twoFrequency_layer_product_bound (w : MultiplicativeWeight)
    (x a b θ φ : ℝ) (r : ℕ) (hab : a ≤ b) :
    (∑ n ∈ smoothSupport x, if (smallPrimePart n a).primeFactors.card = r
      then w n * twoFrequencyWeight n a b θ φ / n else 0) ≤
      distinctProductSum ((primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < a))
        (fun p ↦ w p * threeRangeWeight p a b θ φ / p) r *
      ∏ p ∈ primesLT x \ (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < a),
        (1 + w p * threeRangeWeight p a b θ φ / p) := by
  apply sum_smallPrime_layer_le_product x a r
    (fun n ↦ w n * twoFrequencyWeight n a b θ φ)
    (fun p ↦ w p * threeRangeWeight p a b θ φ)
  · rw [w.map_one, twoFrequencyWeight_one, mul_one]
  · intro m n hmn
    rw [w.map_mul m n hmn, twoFrequencyWeight_mul hmn]
    ring
  · intro p _
    exact mul_nonneg (w.nonneg p) (twoFrequencyWeight_nonneg p a b θ φ)
  · intro p hp
    exact mul_le_mul_of_nonneg_left
      (twoFrequencyWeight_prime_le (mem_primesLT.1 hp).1 hab θ φ) (w.nonneg p)

/-- The small-prime coefficient has the factorial majorant with weighted
reciprocal-prime mean. -/
theorem twoFrequency_layer_factorial_bound (w : MultiplicativeWeight)
    (x a b θ φ : ℝ) (r : ℕ) (hab : a ≤ b) :
    (∑ n ∈ smoothSupport x, if (smallPrimePart n a).primeFactors.card = r
      then w n * twoFrequencyWeight n a b θ φ / n else 0) ≤
      ((2 * ∑ p ∈ (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < a), w p / p) ^ r /
        (r.factorial : ℝ)) *
      exp (∑ p ∈ primesLT x \ (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < a),
        w p * threeRangeWeight p a b θ φ / p) := by
  let P := (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < a)
  let v := fun p ↦ w p * threeRangeWeight p a b θ φ / (p : ℝ)
  have hv : ∀ p, 0 ≤ v p := fun p ↦
    div_nonneg (mul_nonneg (w.nonneg p) (threeRangeWeight_nonneg p a b θ φ)) (Nat.cast_nonneg p)
  have hs : (∑ p ∈ P, v p) = 2 * ∑ p ∈ P, w p / p := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p hp
    have hpa := (mem_filter.1 hp).2
    simp only [v, threeRangeWeight, hpa, ite_true]
    ring
  have hsym := distinctProductSum_le P v r (fun p _ ↦ hv p)
  rw [hs] at hsym
  have heuler := prod_one_add_le_exp_sum (primesLT x \ P) hv
  refine (twoFrequency_layer_product_bound w x a b θ φ r hab).trans ?_
  apply mul_le_mul hsym heuler
  · apply prod_nonneg
    intro p _
    change 0 ≤ 1 + v p
    linarith [hv p]
  · apply div_nonneg _ (Nat.cast_nonneg _)
    apply pow_nonneg
    exact mul_nonneg (by norm_num) (sum_nonneg (fun p _ ↦ div_nonneg (w.nonneg p) (Nat.cast_nonneg _)))

/-- The square-root coefficient saving is uniform in the layer index,
including the case in which the weighted prime mean is zero. -/
theorem twoFrequency_layer_uniform (w : MultiplicativeWeight)
    (x a b θ φ : ℝ) (r : ℕ) (hab : a ≤ b) :
    (∑ n ∈ smoothSupport x, if (smallPrimePart n a).primeFactors.card = r
      then w n * twoFrequencyWeight n a b θ φ / n else 0) ≤
      (8 * exp (2 * ∑ p ∈ (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < a), w p / p) /
        sqrt (1 + 2 * ∑ p ∈ (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < a), w p / p)) *
      exp (∑ p ∈ primesLT x \ (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < a),
        w p * threeRangeWeight p a b θ φ / p) := by
  have hu : 0 ≤ 2 * ∑ p ∈ (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < a), w p / p :=
    mul_nonneg (by norm_num) (sum_nonneg (fun p _ ↦ div_nonneg (w.nonneg p) (Nat.cast_nonneg _)))
  exact (twoFrequency_layer_factorial_bound w x a b θ φ r hab).trans
    (mul_le_mul_of_nonneg_right (factorial_term_uniform hu r) (exp_pos _).le)

end BretecheTenenbaumMean.WeightedModel
