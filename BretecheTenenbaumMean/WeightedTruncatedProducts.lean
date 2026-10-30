module

public import BretecheTenenbaumMean.WeightedPrimeConsequences
public import BretecheTenenbaumMean.PrimeRecursion
public import BretecheTenenbaumMean.MomentConvexity

@[expose] public section

/-! # Weighted truncated moments and products -/

namespace BretecheTenenbaumMean.WeightedModel

open Finset Real

/-- The weighted truncated expectation, with the paper's original good sets. -/
noncomputable def truncatedMoment (w : MultiplicativeWeight) (δ T : ℝ)
    (θ : ℕ → ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  expectation w x ((momentGoodSet δ T θ (q - 1)).indicator (fun n ↦ moment q n / tau n))

/-- The unnormalized product sum `Z_{q,j}(y,T)` in §2.3. -/
noncomputable def momentProductSum (w : MultiplicativeWeight) (δ T : ℝ) (θ : ℕ → ℝ) (q j : ℕ) (y : ℝ) : ℝ :=
  ∑ m ∈ smoothSupport y, w m * (momentGoodSet δ T θ (q - 1)).indicator
    (fun m ↦ moment (q - j) m * moment j m / ((m : ℝ) * tau m)) m

/-- The exact normalizer version of (2.17). -/
theorem momentProductSum_le (w : MultiplicativeWeight) (δ : ℝ) {T y : ℝ} (hT : 0 ≤ T) (hy : 1 ≤ y)
    (θ : ℕ → ℝ) {q j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ q - 1) (hθ : 0 ≤ θ j) :
    momentProductSum w δ T θ q j y ≤
      θ j * (T * log (3 * y) * exp (-penalty δ T y)) *
        normalizer w y * truncatedMoment w δ T θ (q - j) y := by
  classical
  let B := T * log (3 * y) * exp (-penalty δ T y)
  have hB : 0 ≤ B := by
    apply mul_nonneg _ (exp_pos _).le
    exact mul_nonneg hT (log_nonneg (by linarith))
  have hnorm : normalizer w y * truncatedMoment w δ T θ (q - j) y =
      ∑ m ∈ smoothSupport y, w m * (momentGoodSet δ T θ (q - j - 1)).indicator
        (fun m ↦ moment (q - j) m / tau m) m / m := by
    unfold truncatedMoment expectation
    field_simp [(normalizer_pos w y).ne']
  rw [mul_assoc (θ j * _) (normalizer w y), hnorm, mul_sum]
  unfold momentProductSum
  apply sum_le_sum
  intro m hm
  have hm0 := (mem_smoothSupport.1 hm).1.ne_zero
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  have ht := tau_pos hm0
  by_cases hE : m ∈ momentGoodSet δ T θ (q - 1)
  · have hE' : m ∈ momentGoodSet δ T θ (q - j - 1) :=
      momentGoodSet_antitone δ T θ (show q - j - 1 ≤ q - 1 by omega) hE
    have hτ : tau m ≤ B := by
      have h := hE.1.1.2 y hy
      rw [smallPrimePart_eq_self (mem_smoothSupport.1 hm).1 (mem_smoothSupport.1 hm).2] at h
      exact h
    have hMj : moment j m ≤ θ j * B := by
      calc _ ≤ tau m * θ j := hE.2 j hj hjq
           _ ≤ B * θ j := mul_le_mul_of_nonneg_right hτ hθ
           _ = _ := mul_comm _ _
    simp only [Set.indicator_of_mem hE, Set.indicator_of_mem hE']
    have h := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hMj (moment_nonneg (q - j) m)) (mul_nonneg hmpos.le ht.le)
    have hw := mul_le_mul_of_nonneg_left h (w.nonneg m)
    convert hw using 1
    ring
  · rw [Set.indicator_of_notMem hE, mul_zero]
    apply mul_nonneg (mul_nonneg hθ hB)
    apply div_nonneg _ hmpos.le
    exact mul_nonneg (w.nonneg m) (Set.indicator_nonneg (fun n _ ↦ div_nonneg (moment_nonneg _ _) (Nat.cast_nonneg _)) m)

/-- The exceptional midpoint `q=4,j=2` reduces to the `j=1` term by
adjacent moment log-convexity. -/
theorem momentProductSum_four_two_le (w : MultiplicativeWeight) (δ T y : ℝ) (θ : ℕ → ℝ) :
    momentProductSum w δ T θ 4 2 y ≤ momentProductSum w δ T θ 4 1 y := by
  classical
  unfold momentProductSum
  apply sum_le_sum
  intro m _
  by_cases hm : m ∈ momentGoodSet δ T θ (4 - 1)
  · simp only [Set.indicator_of_mem hm, Nat.reduceSub, moment_one]
    apply mul_le_mul_of_nonneg_left _ (w.nonneg m)
    apply div_le_div_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg _))
    simpa only [pow_two] using moment_two_sq_le m
  · simp only [Set.indicator_of_notMem hm, le_refl]

end BretecheTenenbaumMean.WeightedModel
