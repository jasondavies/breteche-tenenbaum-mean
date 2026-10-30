module

public import BretecheTenenbaumMean.RecursionKernels

@[expose] public section

/-! # Factorial control of the accumulated recursion error -/

namespace BretecheTenenbaumMean

open Finset Real MeasureTheory

/-- The fourth-root contribution is at most `C^q q! T^(q-2)`, uniformly
in the upper endpoint, the penalty and the threshold sequence. -/
theorem recursionDecay_integral_bound : ∃ C > 0, ∀ δ T (θ : ℕ → ℝ) (q : ℕ),
    0 ≤ δ → 1 ≤ T → 2 ≤ q → ∀ X : ℝ, 1 ≤ X →
    (∫ y in 1..X, recursionDecayKernel δ T θ q y) ≤
      C ^ q * (q.factorial : ℝ) * T ^ (q - 2) := by
  obtain ⟨C, hC, hdecay⟩ := recursionDecayKernel_bound
  let D := 24 * (24 * C + 1)
  refine ⟨D, by dsimp only [D]; positivity, fun δ T θ q hδ hT hq X hX ↦ ?_⟩
  have hT0 : 0 ≤ T := by linarith
  have hi := intervalIntegral.integral_mono_on hX
    (intervalIntegrable_recursionDecayKernel δ T θ q hX)
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

/-- The integral recursion with its error replaced by an explicit factorial
majorant, before using the admissible threshold sequence to absorb it. -/
theorem truncatedMoment_factorial_recursion : ∃ A > 0, ∃ B > 0,
    ∀ δ T (θ : ℕ → ℝ) (q : ℕ), 0 ≤ δ → 1 ≤ T → 2 ≤ q →
    ∀ x : ℝ, 2 ≤ x →
    truncatedMoment δ T θ q x ≤ A *
      (1 + B ^ q * (q.factorial : ℝ) * T ^ (q - 2) +
        ∫ y in 1..x ^ 2, recursionMainKernel δ T θ q y) := by
  obtain ⟨A, hA, hrec⟩ := truncatedMoment_integral_bound
  obtain ⟨B, hB, hdecay⟩ := recursionDecay_integral_bound
  refine ⟨A, hA, B, hB, fun δ T θ q hδ hT hq x hx ↦ ?_⟩
  have hx2 : 1 ≤ x ^ 2 := by nlinarith
  have he : (∫ y in 1..x ^ 2, recursionIntegralKernel δ T θ q y / log (3 * y)) =
      (∫ y in 1..x ^ 2, recursionMainKernel δ T θ q y) +
      ∫ y in 1..x ^ 2, recursionDecayKernel δ T θ q y := by
    rw [← intervalIntegral.integral_add (intervalIntegrable_recursionMainKernel δ T θ q hx2)
      (intervalIntegrable_recursionDecayKernel δ T θ q hx2)]
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hx2]
    exact fun y hy ↦ recursionIntegralKernel_split δ T θ q hy.1
  have h := hrec δ T θ q hq x hx
  rw [he] at h
  have hd := hdecay δ T θ q hδ hT hq (x ^ 2) hx2
  have hm := mul_le_mul_of_nonneg_left hd hA.le
  linarith

end BretecheTenenbaumMean
