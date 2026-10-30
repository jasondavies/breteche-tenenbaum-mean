module

public import BretecheTenenbaumMean.WeightedSmoothSums
public import BretecheTenenbaumMean.RecursionErrorProducts

@[expose] public section

/-! # Weighted product bounds for the fourth-root error -/

namespace BretecheTenenbaumMean.WeightedModel

open Finset Real

theorem sum_tau_div_bound (w : MultiplicativeWeight) (hp : PrimeEstimates w) : ∃ C > 0, ∀ y : ℝ, 1 ≤ y →
    (∑ m ∈ smoothSupport y, w m * tau m / m) ≤ C * log (3 * y) ^ 2 := by
  obtain ⟨_, A, _, hA, hnormal⟩ := hp.normalizer_bounds
  obtain ⟨B, hB, hmean⟩ := hp.expectation_tau_pow_bound 1
  refine ⟨A * B, mul_pos hA hB, fun y hy ↦ ?_⟩
  have hz : 2 ≤ 3 * y := by linarith
  have hlog : 0 < log (3 * y) := log_pos (by linarith)
  have he : (∑ m ∈ smoothSupport (3 * y), w m * tau m / m) =
      normalizer w (3 * y) * expectation w (3 * y) (fun m ↦ tau m) := by
    unfold expectation
    field_simp [(normalizer_pos w _).ne']
  have hm := hmean (3 * y) hz
  norm_num only [pow_one, Nat.pow_one, Nat.reduceSub] at hm
  calc
    _ ≤ ∑ m ∈ smoothSupport (3 * y), w m * tau m / m :=
      sum_smoothSupport_mono (fun m ↦ div_nonneg (mul_nonneg (w.nonneg m) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
        (by linarith)
    _ = _ := he
    _ ≤ (A * log (3 * y)) * (B * log (3 * y)) :=
      mul_le_mul (hnormal _ hz).2 hm (expectation_nonneg w _ (fun m _ ↦ Nat.cast_nonneg _))
        (by positivity)
    _ = _ := by ring

/-- Uniform in both orders: the elementary product bound used for the
fourth-root error in §2.3. -/
theorem momentProductSum_trivial_bound (w : MultiplicativeWeight) (hp : PrimeEstimates w) : ∃ C > 0, ∀ δ T (θ : ℕ → ℝ) (q j : ℕ),
    0 ≤ δ → 1 ≤ T → 1 ≤ j → j < q → ∀ y : ℝ, 1 ≤ y →
    momentProductSum w δ T θ q j y ≤ C * T ^ (q - 2) * log (3 * y) ^ q := by
  classical
  obtain ⟨C, hC, hsum⟩ := sum_tau_div_bound w hp
  refine ⟨C, hC, fun δ T θ q j hδ hT hj hjq y hy ↦ ?_⟩
  have hq : 2 ≤ q := by omega
  have hlog : 0 ≤ log (3 * y) := log_nonneg (by linarith)
  have hT0 : 0 ≤ T := by linarith
  have hpoint : ∀ m ∈ smoothSupport y,
      (momentGoodSet δ T θ (q - 1)).indicator
        (fun m ↦ moment (q - j) m * moment j m / ((m : ℝ) * tau m)) m ≤
      (T * log (3 * y)) ^ (q - 2) * (tau m / m) := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (mem_smoothSupport.1 hm).1.ne_zero
    have ht := tau_pos (mem_smoothSupport.1 hm).1.ne_zero
    by_cases hE : m ∈ momentGoodSet δ T θ (q - 1)
    · rw [Set.indicator_of_mem hE]
      have hτ := tau_le_goodSet_log hδ hT hy hm hE.1.1
      calc
        _ ≤ (tau m ^ (q - j) * tau m ^ j) / ((m : ℝ) * tau m) :=
          div_le_div_of_nonneg_right
            (mul_le_mul (moment_le_tau_pow m (q - j) (by omega))
              (moment_le_tau_pow m j hj) (moment_nonneg j m) (by positivity)) (by positivity)
        _ = tau m ^ (q - 2) * (tau m / m) := by
          rw [← pow_add, Nat.sub_add_cancel (by omega : j ≤ q)]
          have he : q = (q - 2) + 2 := by omega
          conv_lhs => rw [he, pow_add, pow_two]
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht.le hτ _) (by positivity)
    · rw [Set.indicator_of_notMem hE]
      positivity
  calc
    _ ≤ ∑ m ∈ smoothSupport y, (T * log (3 * y)) ^ (q - 2) * (w m * tau m / m) :=
      sum_le_sum (fun m hm ↦ by
        have h := mul_le_mul_of_nonneg_left (hpoint m hm) (w.nonneg m)
        convert h using 1; ring)
    _ = (T * log (3 * y)) ^ (q - 2) * ∑ m ∈ smoothSupport y, w m * tau m / m := (mul_sum ..).symm
    _ ≤ (T * log (3 * y)) ^ (q - 2) * (C * log (3 * y) ^ 2) :=
      mul_le_mul_of_nonneg_left (hsum y hy) (by positivity)
    _ = _ := by
      rw [mul_pow]
      have he : q = (q - 2) + 2 := by omega
      have hp : log (3 * y) ^ q = log (3 * y) ^ (q - 2) * log (3 * y) ^ 2 := by
        conv_lhs => rw [he, pow_add]
      rw [hp]
      ring


end BretecheTenenbaumMean.WeightedModel
