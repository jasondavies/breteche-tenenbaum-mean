module

public import BretecheTenenbaumMean.WeightedRecursionKernels

@[expose] public section

/-! # Factorial bounds for the weighted recursion error -/

namespace BretecheTenenbaumMean.WeightedModel

open Finset Real MeasureTheory

theorem recursionDecay_integral_bound (w : MultiplicativeWeight) (hpw : PrimeEstimates w) : ∃ C > 0, ∀ δ T (θ : ℕ → ℝ) (q : ℕ),
    0 ≤ δ → 1 ≤ T → 2 ≤ q → ∀ X : ℝ, 1 ≤ X →
    (∫ y in 1..X, recursionDecayKernel w δ T θ q y) ≤
      C ^ q * (q.factorial : ℝ) * T ^ (q - 2) := by
  obtain ⟨C, hC, hdecay⟩ := recursionDecayKernel_bound w hpw
  let D := 24 * (24 * C + 1)
  refine ⟨D, by dsimp only [D]; positivity, fun δ T θ q hδ hT hq X hX ↦ ?_⟩
  have hT0 : 0 ≤ T := by linarith
  have hi := intervalIntegral.integral_mono_on hX
    (intervalIntegrable_recursionDecayKernel w δ T θ q hX)
    ((intervalIntegrable_logPowerKernel (q - 2) hX).const_mul (C * 3 ^ q * T ^ (q - 2)))
    (fun y hy ↦ hdecay δ T θ q hδ hT hq y hy.1)
  rw [intervalIntegral.integral_const_mul] at hi
  have hh := mul_le_mul_of_nonneg_left (integral_logPowerKernel_le (q - 2) hX)
    (by positivity : 0 ≤ C * 3 ^ q * T ^ (q - 2))
  have hp8 : (8 : ℝ) ^ (q - 2) ≤ 8 ^ q := pow_le_pow_right₀ (by norm_num) (by omega)
  have hfac : ((q - 2).factorial : ℝ) ≤ q.factorial := by
    exact_mod_cast (Nat.factorial_le (show q - 2 ≤ q by omega))
  have hcoef : 24 * C * 3 ^ q * 8 ^ (q - 2) * ((q - 2).factorial : ℝ) ≤
      D ^ q * (q.factorial : ℝ) := by
    have hCpow : 24 * C ≤ (24 * C + 1) ^ q := by
      calc
        _ ≤ 24 * C + 1 := by linarith
        _ = (24 * C + 1) ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
    calc
      _ ≤ 24 * C * 3 ^ q * 8 ^ q * (q.factorial : ℝ) := by
        apply mul_le_mul _ hfac (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hp8 (by positivity)
      _ = (24 * C) * 24 ^ q * (q.factorial : ℝ) := by
        have he : (24 : ℝ) ^ q = 3 ^ q * 8 ^ q := by rw [← mul_pow]; norm_num
        rw [he]
        ring
      _ ≤ (24 * C + 1) ^ q * 24 ^ q * (q.factorial : ℝ) := by
        gcongr
      _ = _ := by dsimp only [D]; rw [mul_pow]; ring
  have hc := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hT0 (q - 2))
  nlinarith


theorem truncatedMoment_factorial_recursion (w : MultiplicativeWeight) (hpw : PrimeEstimates w) : ∃ A > 0, ∃ B > 0,
    ∀ δ T (θ : ℕ → ℝ) (q : ℕ), 0 ≤ δ → 1 ≤ T → 2 ≤ q →
    ∀ x : ℝ, 2 ≤ x →
    truncatedMoment w δ T θ q x ≤ A *
      (1 + B ^ q * (q.factorial : ℝ) * T ^ (q - 2) +
        ∫ y in 1..x ^ 2, recursionMainKernel w δ T θ q y) := by
  obtain ⟨A, hA, hrec⟩ := truncatedMoment_integral_bound w hpw
  obtain ⟨B, hB, hdecay⟩ := recursionDecay_integral_bound w hpw
  refine ⟨A, hA, B, hB, fun δ T θ q hδ hT hq x hx ↦ ?_⟩
  have hx2 : 1 ≤ x ^ 2 := by nlinarith
  have he : (∫ y in 1..x ^ 2, recursionIntegralKernel w δ T θ q y / log (3 * y)) =
      (∫ y in 1..x ^ 2, recursionMainKernel w δ T θ q y) +
      ∫ y in 1..x ^ 2, recursionDecayKernel w δ T θ q y := by
    rw [← intervalIntegral.integral_add (intervalIntegrable_recursionMainKernel w δ T θ q hx2)
      (intervalIntegrable_recursionDecayKernel w δ T θ q hx2)]
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hx2]
    exact fun y hy ↦ recursionIntegralKernel_split w δ T θ q hy.1
  have h := hrec δ T θ q hq x hx
  rw [he] at h
  have hd := hdecay δ T θ q hδ hT hq (x ^ 2) hx2
  have hm := mul_le_mul_of_nonneg_left hd hA.le
  linarith


end BretecheTenenbaumMean.WeightedModel
