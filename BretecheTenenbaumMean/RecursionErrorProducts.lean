module

public import BretecheTenenbaumMean.SmoothSums
public import BretecheTenenbaumMean.HighFrequencyKernel

@[expose] public section

/-! # Trivial product bounds for the fourth-root recursion error -/

namespace BretecheTenenbaumMean

open Finset Real

/-- The unnormalized first divisor-count moment, uniformly down to `y = 1`. -/
theorem sum_tau_div_bound : ∃ C > 0, ∀ y : ℝ, 1 ≤ y →
    (∑ m ∈ smoothSupport y, tau m / m) ≤ C * log (3 * y) ^ 2 := by
  obtain ⟨_, A, _, hA, hnormal⟩ := PrimeSums.normalizer_bounds
  obtain ⟨B, hB, hmean⟩ := PrimeSums.expectation_tau_pow_le 1
  refine ⟨A * B, mul_pos hA hB, fun y hy ↦ ?_⟩
  have hz : 2 ≤ 3 * y := by linarith
  have hlog : 0 < log (3 * y) := log_pos (by linarith)
  have he : (∑ m ∈ smoothSupport (3 * y), tau m / m) =
      normalizer (3 * y) * expectation (3 * y) (fun m ↦ tau m) := by
    unfold expectation
    field_simp [(normalizer_pos _).ne']
  have hm := hmean (3 * y) hz
  norm_num only [pow_one, Nat.pow_one, Nat.reduceSub] at hm
  calc
    _ ≤ ∑ m ∈ smoothSupport (3 * y), tau m / m :=
      sum_smoothSupport_mono (fun m ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (by linarith)
    _ = _ := he
    _ ≤ (A * log (3 * y)) * (B * log (3 * y)) :=
      mul_le_mul (hnormal _ hz).2 hm (expectation_nonneg _ (fun m _ ↦ Nat.cast_nonneg _))
        (by positivity)
    _ = _ := by ring

/-- Dropping the nonnegative penalty gives the divisor-count envelope. -/
theorem tau_le_goodSet_log {δ T y : ℝ} (hδ : 0 ≤ δ) (hT : 1 ≤ T) (hy : 1 ≤ y)
    {m : ℕ} (hm : m ∈ smoothSupport y) (hE : m ∈ goodSet δ T) :
    tau m ≤ T * log (3 * y) := by
  have h := hE.2 y hy
  rw [smallPrimePart_eq_self (mem_smoothSupport.1 hm).1 (mem_smoothSupport.1 hm).2] at h
  have hp := exp_le_one_iff.2 (neg_nonpos.2 (penalty_nonneg hδ hT hy))
  exact h.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hp (mul_nonneg (by linarith : 0 ≤ T)
      (log_nonneg (by linarith))))

/-- Uniform in both orders: the elementary product bound used for the
fourth-root error in §2.3. -/
theorem momentProductSum_trivial_bound : ∃ C > 0, ∀ δ T (θ : ℕ → ℝ) (q j : ℕ),
    0 ≤ δ → 1 ≤ T → 1 ≤ j → j < q → ∀ y : ℝ, 1 ≤ y →
    momentProductSum δ T θ q j y ≤ C * T ^ (q - 2) * log (3 * y) ^ q := by
  classical
  obtain ⟨C, hC, hsum⟩ := sum_tau_div_bound
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
    _ ≤ ∑ m ∈ smoothSupport y, (T * log (3 * y)) ^ (q - 2) * (tau m / m) :=
      sum_le_sum hpoint
    _ = (T * log (3 * y)) ^ (q - 2) * ∑ m ∈ smoothSupport y, tau m / m := (mul_sum ..).symm
    _ ≤ (T * log (3 * y)) ^ (q - 2) * (C * log (3 * y) ^ 2) :=
      mul_le_mul_of_nonneg_left (hsum y hy) (by positivity)
    _ = _ := by
      rw [mul_pow]
      have he : q = (q - 2) + 2 := by omega
      have hp : log (3 * y) ^ q = log (3 * y) ^ (q - 2) * log (3 * y) ^ 2 := by
        conv_lhs => rw [he, pow_add]
      rw [hp]
      ring

end BretecheTenenbaumMean
