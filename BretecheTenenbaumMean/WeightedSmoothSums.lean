module

public import BretecheTenenbaumMean.WeightedTruncatedProducts
public import BretecheTenenbaumMean.SmoothSums

@[expose] public section

/-! # Monotonicity and integrability of weighted product sums -/

namespace BretecheTenenbaumMean.WeightedModel

open Finset MeasureTheory

theorem momentProductSum_nonneg (w : MultiplicativeWeight) (δ T : ℝ) (θ : ℕ → ℝ) (q j : ℕ) (y : ℝ) :
    0 ≤ momentProductSum w δ T θ q j y := by
  apply sum_nonneg
  intro m _
  apply mul_nonneg (w.nonneg m)
  apply Set.indicator_nonneg _ m
  intro n _
  exact div_nonneg (mul_nonneg (moment_nonneg _ _) (moment_nonneg _ _))
    (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg _))

theorem momentProductSum_mono (w : MultiplicativeWeight) (δ T : ℝ) (θ : ℕ → ℝ) (q j : ℕ) :
    Monotone (momentProductSum w δ T θ q j) := by
  apply sum_smoothSupport_mono
  intro m
  apply mul_nonneg (w.nonneg m)
  apply Set.indicator_nonneg _ m
  intro n _
  exact div_nonneg (mul_nonneg (moment_nonneg _ _) (moment_nonneg _ _))
    (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg _))

theorem intervalIntegrable_momentProductSum (w : MultiplicativeWeight) (δ T : ℝ) (θ : ℕ → ℝ) (q j : ℕ) (a b : ℝ) :
    IntervalIntegrable (momentProductSum w δ T θ q j) volume a b :=
  (momentProductSum_mono w δ T θ q j).intervalIntegrable


end BretecheTenenbaumMean.WeightedModel
