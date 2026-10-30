module

public import BretecheTenenbaumMean.TruncatedProducts

@[expose] public section

/-! # Monotonicity and local integrability of smooth-support sums -/

namespace BretecheTenenbaumMean

open Finset MeasureTheory

theorem smoothSupport_mono : Monotone smoothSupport := by
  intro x y hxy n hn
  obtain ⟨hsq, hp⟩ := mem_smoothSupport.1 hn
  exact mem_smoothSupport.2 ⟨hsq, fun p hpn ↦ (hp p hpn).trans_le hxy⟩

theorem sum_smoothSupport_mono {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    Monotone (fun y ↦ ∑ n ∈ smoothSupport y, f n) := by
  intro x y hxy
  exact sum_le_sum_of_subset_of_nonneg (smoothSupport_mono hxy) (fun n _ _ ↦ hf n)

theorem momentProductSum_nonneg (δ T : ℝ) (θ : ℕ → ℝ) (q j : ℕ) (y : ℝ) :
    0 ≤ momentProductSum δ T θ q j y := by
  apply sum_nonneg
  intro m _
  apply Set.indicator_nonneg _ m
  intro n _
  exact div_nonneg (mul_nonneg (moment_nonneg _ _) (moment_nonneg _ _))
    (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg _))

theorem momentProductSum_mono (δ T : ℝ) (θ : ℕ → ℝ) (q j : ℕ) :
    Monotone (momentProductSum δ T θ q j) := by
  apply sum_smoothSupport_mono
  intro m
  apply Set.indicator_nonneg _ m
  intro n _
  exact div_nonneg (mul_nonneg (moment_nonneg _ _) (moment_nonneg _ _))
    (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg _))

theorem intervalIntegrable_momentProductSum (δ T : ℝ) (θ : ℕ → ℝ) (q j : ℕ) (a b : ℝ) :
    IntervalIntegrable (momentProductSum δ T θ q j) volume a b :=
  (momentProductSum_mono δ T θ q j).intervalIntegrable

end BretecheTenenbaumMean
