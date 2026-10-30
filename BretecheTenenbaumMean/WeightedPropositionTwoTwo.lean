module

public import BretecheTenenbaumMean.WeightedThirdMomentBase
public import BretecheTenenbaumMean.WeightedMomentInductionKernel
public import BretecheTenenbaumMean.WeightedThresholdRecursion

@[expose] public section

/-! # Weighted higher-moment bounds from prime estimates -/

namespace BretecheTenenbaumMean.WeightedModel

open Finset Real MeasureTheory

/-- The weighted version of Proposition 2.2. The threshold constant may depend
on the fixed prime estimates and the positive penalty parameter. -/
theorem propositionTwoTwo_for_delta (w : MultiplicativeWeight) (hpw : PrimeEstimates w) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C₀ ≥ (1 : ℝ), ∀ T : ℝ, 3 ≤ T → ∀ θ : ℕ → ℝ,
    AdmissibleThresholds C₀ T θ → ∀ q : ℕ, 3 ≤ q → ∀ x : ℝ, 2 ≤ x →
      truncatedMoment w δ T θ q x ≤ C₀ * θ q / ((q : ℝ) ^ 2 * T) := by
  obtain ⟨Cmin, hCmin, A, hA, hrec⟩ := truncatedMoment_threshold_recursion w hpw
  obtain ⟨D, hD, hmain⟩ := recursionMain_integral_induction_bound w hpw hδ
  obtain ⟨B, hB, hbase⟩ := truncatedMoment_three_bound w hpw
  let C₀ := max Cmin (max (2 * A * (D + 1)) (max (9 * B) 1))
  have hCmin' : Cmin ≤ C₀ := le_max_left _ _
  have hCA : 2 * A * (D + 1) ≤ C₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hCB : 9 * B ≤ C₀ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hC : 1 ≤ C₀ := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hC0 : 0 < C₀ := by linarith
  have hcoef : A * (1 + D * C₀) ≤ C₀ ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hCA hC0.le
    have h' := mul_le_mul_of_nonneg_left hC hA.le
    nlinarith
  refine ⟨C₀, hC, fun T hT θ hθ ↦ ?_⟩
  have hT0 : 0 < T := by linarith
  have hlog : 1 ≤ log T := (show (1 : ℝ) ≤ log 3 by linarith [log_three_gt_d9]).trans
    (log_le_log (by norm_num) hT)
  have hsqrt : 1 ≤ sqrt (log T) := by simpa only [sqrt_one] using sqrt_le_sqrt hlog
  have hsqrt0 : 0 < sqrt (log T) := by linarith
  have hθ0 : ∀ j, 0 ≤ θ j := fun j ↦ (hθ.1 j).le
  have hall : ∀ q : ℕ, 3 ≤ q → ∀ x : ℝ, 2 ≤ x →
      truncatedMoment w δ T θ q x ≤ C₀ * θ q / (q : ℝ) ^ 2 / T := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro hq x hx
      by_cases hq3 : q = 3
      · subst q
        have hb := hbase δ T θ hδ.le hT x hx
        have hθ3 := hθ.2.2.2.1
        have hcub : 9 * B ≤ 2 * C₀ ^ 3 := by nlinarith [sq_nonneg (C₀ - 1)]
        have hcub' := mul_le_mul_of_nonneg_right hcub (by positivity : 0 ≤ T ^ 2 * log T)
        have htheta := mul_le_mul_of_nonneg_left hθ3 hC0.le
        have hb' := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ 9 * T)
        norm_num only [Nat.cast_ofNat, Nat.reducePow]
        rw [div_div]
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < 9 * T)).2
        nlinarith
      · have hq4 : 4 ≤ q := by omega
        have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
        have hIH : ∀ k : ℕ, 3 ≤ k → k < q → ∀ z : ℝ, 2 ≤ z →
            truncatedMoment w δ T θ k z ≤ C₀ * θ k / (k : ℝ) ^ 2 / T :=
          fun k hk hkq z hz ↦ ih k hkq hk z hz
        have hi := hmain T θ C₀ q hT hC0.le hθ0 hq4 hIH (x ^ 2) (by nlinarith)
        have hr := hrec C₀ hCmin' δ T θ q hδ.le (by linarith) hθ hq x hx
        have hg := threshold_geometric_error_le hθ0 hθ.2.1 hq
        have hconv0 := thresholdConvolution_nonneg hθ0 q
        let W := sqrt (log T) / (q : ℝ) ^ 2 * thresholdConvolution θ q
        have hW0 : 0 ≤ W := by dsimp only [W]; positivity
        have hgeo : θ (q - 1) / 2 ^ q ≤ W := by
          calc
            _ ≤ thresholdConvolution θ q / (q : ℝ) ^ 2 := hg
            _ ≤ sqrt (log T) * (thresholdConvolution θ q / (q : ℝ) ^ 2) := by
              have h := mul_le_mul_of_nonneg_right hsqrt (div_nonneg hconv0 (sq_nonneg (q : ℝ)))
              simpa only [one_mul] using h
            _ = _ := by dsimp only [W]; ring
        have hi' : (∫ y in 1..x ^ 2, recursionMainKernel w δ T θ q y) ≤ D * C₀ * W := by
          convert hi using 1
          dsimp only [W]
          ring
        have hs : truncatedMoment w δ T θ q x ≤ A * (1 + D * C₀) * W := by
          have h := mul_le_mul_of_nonneg_left (add_le_add hgeo hi') hA.le
          nlinarith
        have hconv : thresholdConvolution θ q ≤ θ q / (C₀ * T * sqrt (log T)) := hθ.2.2.2.2.2 q hq
        have hW : W ≤ θ q / (C₀ * T * (q : ℝ) ^ 2) := by
          calc
            _ ≤ sqrt (log T) / (q : ℝ) ^ 2 * (θ q / (C₀ * T * sqrt (log T))) :=
              mul_le_mul_of_nonneg_left hconv (by positivity)
            _ = _ := by field_simp
        calc
          _ ≤ C₀ ^ 2 * W := hs.trans (mul_le_mul_of_nonneg_right hcoef hW0)
          _ ≤ C₀ ^ 2 * (θ q / (C₀ * T * (q : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hW (sq_nonneg _)
          _ = _ := by field_simp
  intro q hq x hx
  simpa only [div_div] using hall q hq x hx


end BretecheTenenbaumMean.WeightedModel
