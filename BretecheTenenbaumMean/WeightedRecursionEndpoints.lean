module

public import BretecheTenenbaumMean.WeightedSmoothSums
public import BretecheTenenbaumMean.RecursionEndpoints

@[expose] public section

/-! # Weighted moment-recursion endpoint bounds -/

namespace BretecheTenenbaumMean.WeightedModel

open Finset Real

theorem expectation_of_le_two (w : MultiplicativeWeight) {x : ℝ} (hx : x ≤ 2) (f : ℕ → ℝ) : expectation w x f = f 1 := by
  simp [expectation, smoothSupport, primeProduct, normalizer, primesLT_eq_empty_of_le_two hx, w.map_one]

theorem truncatedMoment_eq_two_of_le (w : MultiplicativeWeight) (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ)
    {x : ℝ} (hx : x ≤ 2) : truncatedMoment w δ T θ q x = truncatedMoment w δ T θ q 2 := by
  unfold truncatedMoment
  rw [expectation_of_le_two w hx, expectation_of_le_two w le_rfl]

theorem normalizer_log_three_bound (w : MultiplicativeWeight) (hp : PrimeEstimates w) : ∃ C > 0, ∀ y : ℝ, 1 ≤ y →
    normalizer w y ≤ C * log (3 * y) := by
  obtain ⟨_, C, _, hC, hnormal⟩ := hp.normalizer_bounds
  refine ⟨C, hC, fun y hy ↦ ?_⟩
  have hm : normalizer w y ≤ normalizer w (3 * y) := by
    rw [← sum_weight w, ← sum_weight w]
    exact sum_smoothSupport_mono (fun n ↦ div_nonneg (w.nonneg n) (Nat.cast_nonneg _)) (by linarith)
  exact hm.trans (hnormal (3 * y) (by linarith)).2

/-- The product estimate (2.17) on the entire smoothing interval. -/
theorem momentProductSum_bound_one (w : MultiplicativeWeight) (hp : PrimeEstimates w) : ∃ C > 0, ∀ δ T y (θ : ℕ → ℝ) (q j : ℕ),
    0 ≤ T → 1 ≤ y → 1 ≤ j → j ≤ q - 1 → 0 ≤ θ j →
    momentProductSum w δ T θ q j y ≤ C * θ j * T * log (3 * y) ^ 2 *
      truncatedMoment w δ T θ (q - j) y * exp (-penalty δ T y) := by
  obtain ⟨C, hC, hnormal⟩ := normalizer_log_three_bound w hp
  refine ⟨C, hC, fun δ T y θ q j hT hy hj hjq hθ ↦ ?_⟩
  have hl : 0 ≤ log (3 * y) := log_nonneg (by linarith)
  have hS : 0 ≤ truncatedMoment w δ T θ (q - j) y := by
    apply expectation_nonneg
    intro m _
    exact Set.indicator_nonneg (fun n _ ↦ div_nonneg (moment_nonneg _ _) (Nat.cast_nonneg _)) m
  calc
    _ ≤ θ j * (T * log (3 * y) * exp (-penalty δ T y)) *
        normalizer w y * truncatedMoment w δ T θ (q - j) y := momentProductSum_le w δ hT hy θ hj hjq hθ
    _ ≤ θ j * (T * log (3 * y) * exp (-penalty δ T y)) *
        (C * log (3 * y)) * truncatedMoment w δ T θ (q - j) y :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hnormal y hy) (by positivity)) hS
    _ = _ := by ring


end BretecheTenenbaumMean.WeightedModel
