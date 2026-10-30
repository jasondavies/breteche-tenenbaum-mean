module

public import BretecheTenenbaumMean.WeightedTruncatedProducts
public import BretecheTenenbaumMean.LargestPrime

@[expose] public section

/-! # The weighted largest-prime recurrence -/

namespace BretecheTenenbaumMean.WeightedModel

open Finset

/-- The unnormalized error term `V_q(x)` in §2.3. -/
noncomputable def recursionError (w : MultiplicativeWeight) (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  1 + ∑ p ∈ primesLT x, ∑ m ∈ smoothSupport p,
    w p * w m * (momentGoodSet δ T θ (q - 1)).indicator (fun m ↦ mixedRemainder q m p / tau m) m /
      ((m : ℝ) * p)

/-- The first largest-prime recursion for `L_x S_q(x)`. The divisor closure
of the moment good set justifies dropping its constraint on `m*p`. -/
theorem truncatedMoment_largest_prime_le (w : MultiplicativeWeight) (δ T : ℝ) (θ : ℕ → ℝ)
    {q : ℕ} (hq : 1 ≤ q) (x : ℝ) :
    normalizer w x * truncatedMoment w δ T θ q x ≤ recursionError w δ T θ q x +
      ∑ p ∈ primesLT x, w p * normalizer w p * truncatedMoment w δ T θ q p / p := by
  classical
  let E := momentGoodSet δ T θ (q - 1)
  let f := E.indicator (fun n ↦ moment q n / tau n)
  have hnorm : ∀ y : ℝ, normalizer w y * truncatedMoment w δ T θ q y =
      ∑ n ∈ smoothSupport y, w n * f n / n := by
    intro y
    unfold truncatedMoment expectation
    dsimp only [f, E]
    field_simp [(normalizer_pos w y).ne']
  rw [hnorm, sum_smoothSupport_by_largest_prime]
  have h1 : w 1 * f 1 / (1 : ℕ) ≤ 1 := by
    rw [w.map_one, one_mul]
    dsimp only [f]
    by_cases h : 1 ∈ E
    · simp only [Set.indicator_of_mem h, tau_one, Nat.cast_one, div_one]
      simpa only [tau_one, one_pow] using moment_le_tau_pow 1 q hq
    · simp only [Set.indicator_of_notMem h, zero_div]; norm_num
  have hterm : ∀ p ∈ primesLT x, ∀ m ∈ smoothSupport p,
      w (m * p) * f (m * p) / (m * p : ℕ) ≤
        w p * w m * (f m + E.indicator (fun m ↦ mixedRemainder q m p / tau m) m) / ((m : ℝ) * p) := by
    intro p hp m hm
    rw [Nat.cast_mul, w.map_mul m p
      ((mem_primesLT.1 hp).1.coprime_iff_not_dvd.2
        (prime_not_dvd_of_mem_smoothSupport (mem_primesLT.1 hp).1 hm)).symm,
      mul_comm (w m) (w p)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (w.nonneg p) (w.nonneg m))
    by_cases hmp : m * p ∈ E
    · have hmE : m ∈ E := momentGoodSet_of_dvd hmp (Nat.dvd_mul_right m p)
      simp only [f, Set.indicator_of_mem hmp, Set.indicator_of_mem hmE]
      exact normalized_moment_mul_prime_le (mem_primesLT.1 hp).1 hm hq
    · simp only [f, Set.indicator_of_notMem hmp]
      apply add_nonneg
      · exact Set.indicator_nonneg (fun n _ ↦ div_nonneg (moment_nonneg _ _) (Nat.cast_nonneg _)) m
      · apply Set.indicator_nonneg _ m
        intro n _
        exact div_nonneg (sum_nonneg (fun j _ ↦ mul_nonneg (Nat.cast_nonneg _) (mixedMoment_nonneg _ _ _ _)))
          (Nat.cast_nonneg _)
  calc
    _ ≤ 1 + ∑ p ∈ primesLT x, ∑ m ∈ smoothSupport p,
        w p * w m * (f m + E.indicator (fun m ↦ mixedRemainder q m p / tau m) m) / ((m : ℝ) * p) :=
      add_le_add h1 (sum_le_sum (fun p hp ↦ sum_le_sum (hterm p hp)))
    _ = _ := by
      have hs (p : ℕ) : (∑ m ∈ smoothSupport p,
          w p * w m * f m / ((m : ℝ) * p)) =
          w p * normalizer w p * truncatedMoment w δ T θ q p / p := by
        rw [mul_assoc, hnorm, mul_sum, sum_div]
        apply sum_congr rfl
        intro m _
        ring
      simp_rw [mul_add, add_div, sum_add_distrib, hs]
      unfold recursionError
      dsimp only [E]
      ring


end BretecheTenenbaumMean.WeightedModel
