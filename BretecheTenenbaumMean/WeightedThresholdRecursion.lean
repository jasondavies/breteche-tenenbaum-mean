module

public import BretecheTenenbaumMean.ThresholdRecursion
public import BretecheTenenbaumMean.WeightedRecursionDecay

@[expose] public section

/-! # Absorbing the weighted recursion error -/

namespace BretecheTenenbaumMean.WeightedModel

open Finset Real MeasureTheory

theorem truncatedMoment_threshold_recursion (w : MultiplicativeWeight) (hpw : PrimeEstimates w) : ∃ Cmin ≥ (1 : ℝ), ∃ C > 0, ∀ C₀ : ℝ, Cmin ≤ C₀ →
    ∀ δ T (θ : ℕ → ℝ) (q : ℕ), 0 ≤ δ → 1 ≤ T →
    AdmissibleThresholds C₀ T θ → 3 ≤ q → ∀ x : ℝ, 2 ≤ x →
    truncatedMoment w δ T θ q x ≤ C * (θ (q - 1) / 2 ^ q +
      ∫ y in 1..x ^ 2, recursionMainKernel w δ T θ q y) := by
  obtain ⟨A, hA, B, hB, hrec⟩ := truncatedMoment_factorial_recursion w hpw
  let D := max B 1
  have hD : 1 ≤ D := le_max_right _ _
  have hD0 : 0 < D := by linarith
  let Cmin := 4 * D
  have hCmin : 1 ≤ Cmin := by dsimp only [Cmin]; linarith
  refine ⟨Cmin, hCmin, A * (32 * D ^ 2), by positivity,
    fun C₀ hC₀ δ T θ q hδ hT hθ hq x hx ↦ ?_⟩
  have hx2 : 1 ≤ x ^ 2 := by nlinarith
  have hI : 0 ≤ ∫ y in 1..x ^ 2, recursionMainKernel w δ T θ q y :=
    intervalIntegral.integral_nonneg hx2 (fun y hy ↦ recursionMainKernel_nonneg w δ T θ q hy.1)
  have he := hθ.2.2.2.2.1 (q - 1) (by omega)
  have hsub : q - 1 - 1 = q - 2 := by omega
  rw [hsub] at he
  have herror := factorial_error_le_threshold hD hC₀ hT hq he
  have hpow : B ^ q ≤ D ^ q := pow_le_pow_left₀ hB.le (le_max_left _ _) q
  have hcoef : 1 ≤ 32 * D ^ 2 := by nlinarith [sq_nonneg (D - 1)]
  have hBerror : B ^ q * (q.factorial : ℝ) * T ^ (q - 2) ≤
      D ^ q * (q.factorial : ℝ) * T ^ (q - 2) := by
    have hT0 : 0 ≤ T := by linarith
    gcongr
  have h := hrec δ T θ q hδ hT (by omega) x hx
  have hbound : 1 + B ^ q * (q.factorial : ℝ) * T ^ (q - 2) +
      (∫ y in 1..x ^ 2, recursionMainKernel w δ T θ q y) ≤
      (32 * D ^ 2) * (θ (q - 1) / 2 ^ q +
        ∫ y in 1..x ^ 2, recursionMainKernel w δ T θ q y) := by
    have hI' := mul_le_mul_of_nonneg_right hcoef hI
    rw [mul_div_assoc] at herror
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hbound hA.le
  nlinarith


end BretecheTenenbaumMean.WeightedModel
