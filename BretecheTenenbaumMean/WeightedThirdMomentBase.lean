module

public import BretecheTenenbaumMean.ThirdMomentBase
public import BretecheTenenbaumMean.WeightedThirdMomentProducts
public import BretecheTenenbaumMean.WeightedRecursionDecay

@[expose] public section

/-! # The weighted third-moment base case -/

namespace BretecheTenenbaumMean.WeightedModel

open Finset Real MeasureTheory

theorem thirdMoment_main_integral_bound (w : MultiplicativeWeight) (hpw : PrimeEstimates w) : ∃ C > 0, ∀ δ T (θ : ℕ → ℝ),
    0 ≤ δ → 3 ≤ T → ∀ X : ℝ, 1 ≤ X →
    (∫ y in 1..X, recursionMainKernel w δ T θ 3 y) ≤ C * T * log T := by
  obtain ⟨C, hC, hZ⟩ := momentProductSum_three_one_bound w hpw
  let a := thirdMomentSaving
  have ha : 0 < a := thirdMomentSaving_pos
  refine ⟨6 * C / a, by positivity, fun δ T θ hδ hT X hX ↦ ?_⟩
  have hT0 : 0 < T := by linarith
  let g := fun y : ℝ ↦ (sqrt T / (sqrt T + log (3 * y) ^ a)) / (y * log (3 * y))
  have hg := intervalIntegrable_logarithmic_transition (a := a) (sqrt_nonneg T) hX
  have hp : ∀ y ∈ Set.Icc 1 X,
      recursionMainKernel w δ T θ 3 y ≤ 3 * C * T * g y := by
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    have hl : 0 < log (3 * y) := log_pos (by linarith [hy.1])
    have hr : 0 < log (3 * y) ^ a := rpow_pos_of_pos hl _
    norm_num only [recursionMainKernel, Nat.reduceDiv, Icc_self, sum_singleton,
      Nat.choose_one_right, Nat.cast_ofNat]
    calc
      _ ≤ 3 * (C * T * sqrt T * log (3 * y) ^ 2 /
          (sqrt T + log (3 * y) ^ a)) / (y * log (3 * y) ^ 3) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hZ δ T θ y hδ (by linarith) hy.1) (by norm_num)) (by positivity)
      _ = _ := by
        dsimp only [g]
        generalize hL : log (3 * y) = L at hl hr ⊢
        field_simp
  have hi := intervalIntegral.integral_mono_on hX
    (intervalIntegrable_recursionMainKernel w δ T θ 3 hX) (hg.const_mul (3 * C * T)) hp
  rw [intervalIntegral.integral_const_mul] at hi
  have hlog := integral_logarithmic_transition_le ha (sqrt_nonneg T) hX
  have hbound := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 3 * C * T)
  have hlt := div_le_div_of_nonneg_right (log_one_add_sqrt_le_two_log hT) ha.le
  have hlast := mul_le_mul_of_nonneg_left hlt (by positivity : 0 ≤ 3 * C * T)
  convert hi.trans (hbound.trans hlast) using 1
  ring


theorem truncatedMoment_three_bound (w : MultiplicativeWeight) (hpw : PrimeEstimates w) : ∃ C > 0, ∀ δ T (θ : ℕ → ℝ),
    0 ≤ δ → 3 ≤ T → ∀ x : ℝ, 2 ≤ x →
    truncatedMoment w δ T θ 3 x ≤ C * T * log T := by
  obtain ⟨A, hA, B, hB, hrec⟩ := truncatedMoment_factorial_recursion w hpw
  obtain ⟨D, hD, hmain⟩ := thirdMoment_main_integral_bound w hpw
  refine ⟨A * (1 + 6 * B ^ 3 + D), by positivity, fun δ T θ hδ hT x hx ↦ ?_⟩
  have hT0 : 0 < T := by linarith
  have hlog : 1 ≤ log T := (show (1 : ℝ) ≤ log 3 by linarith [log_three_gt_d9]).trans
    (log_le_log (by norm_num) hT)
  have hTlog : T ≤ T * log T := by nlinarith
  have hrec' := hrec δ T θ 3 hδ (by linarith) (by norm_num) x hx
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.cast_ofNat, Nat.reduceSub, pow_one] at hrec'
  have hm := hmain δ T θ hδ hT (x ^ 2) (by nlinarith)
  have hi := mul_le_mul_of_nonneg_left hm hA.le
  have hb := mul_le_mul_of_nonneg_left hTlog (by positivity : 0 ≤ A * (6 * B ^ 3))
  have hc := mul_le_mul_of_nonneg_left (show 1 ≤ T * log T by linarith) hA.le
  nlinarith


end BretecheTenenbaumMean.WeightedModel
