module

public import BretecheTenenbaumMean.InductionProducts
public import BretecheTenenbaumMean.WeightedRecursionEndpoints

@[expose] public section

/-! # Induction bounds for weighted moment products -/

namespace BretecheTenenbaumMean.WeightedModel

open Finset Real MeasureTheory

theorem momentProductSum_induction_bound (w : MultiplicativeWeight) (hpw : PrimeEstimates w) : ∃ C > 0,
    ∀ δ T (θ : ℕ → ℝ) (K : ℝ) (q j : ℕ), 0 < T → 0 ≤ K →
    (∀ i, 0 ≤ θ i) → 1 ≤ j → j ≤ q / 2 → 3 ≤ q - j →
    (∀ x : ℝ, 2 ≤ x → truncatedMoment w δ T θ (q - j) x ≤
      K * θ (q - j) / ((q - j : ℕ) : ℝ) ^ 2 / T) →
    ∀ y : ℝ, 1 ≤ y → momentProductSum w δ T θ q j y ≤
      C * K * θ j * θ (q - j) / (q : ℝ) ^ 2 * log (3 * y) ^ 2 * exp (-penalty δ T y) := by
  obtain ⟨A, hA, hZ⟩ := momentProductSum_bound_one w hpw
  refine ⟨4 * A, by positivity, fun δ T θ K q j hT hK hθ hj hjq hk hIH y hy ↦ ?_⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hk0 : (0 : ℝ) < (q - j : ℕ) := by exact_mod_cast (show 0 < q - j by omega)
  have hqk : (q : ℝ) ≤ 2 * (q - j : ℕ) := by exact_mod_cast (show q ≤ 2 * (q - j) by omega)
  have hS : truncatedMoment w δ T θ (q - j) y ≤ K * θ (q - j) / ((q - j : ℕ) : ℝ) ^ 2 / T := by
    by_cases hy2 : 2 ≤ y
    · exact hIH y hy2
    · rw [truncatedMoment_eq_two_of_le w δ T θ (q - j) (le_of_not_ge hy2)]
      exact hIH 2 le_rfl
  have hratio : K * θ (q - j) / ((q - j : ℕ) : ℝ) ^ 2 / T ≤
      4 * K * θ (q - j) / (q : ℝ) ^ 2 / T := by
    apply div_le_div_of_nonneg_right _ hT.le
    apply (div_le_div_iff₀ (sq_pos_of_pos hk0) (sq_pos_of_pos hq0)).2
    have hsq : (q : ℝ) ^ 2 ≤ 4 * ((q - j : ℕ) : ℝ) ^ 2 := by nlinarith
    have h := mul_le_mul_of_nonneg_left hsq (mul_nonneg hK (hθ (q - j)))
    nlinarith
  have hθj := hθ j
  have hL : 0 < log (3 * y) := log_pos (by linarith)
  calc
    _ ≤ A * θ j * T * log (3 * y) ^ 2 * truncatedMoment w δ T θ (q - j) y * exp (-penalty δ T y) :=
      hZ δ T y θ q j hT.le hy hj (by omega) (hθ j)
    _ ≤ A * θ j * T * log (3 * y) ^ 2 * (4 * K * θ (q - j) / (q : ℝ) ^ 2 / T) *
        exp (-penalty δ T y) := by
      apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
      exact mul_le_mul_of_nonneg_left (hS.trans hratio) (by positivity)
    _ = _ := by field_simp


end BretecheTenenbaumMean.WeightedModel
