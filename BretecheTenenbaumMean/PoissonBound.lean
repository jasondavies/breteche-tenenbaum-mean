module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-! # The uniform factorial bound in the high-frequency argument

A simple absolute constant suffices: `u^r/r! ≤ 8 exp(u)/sqrt(1+u)`.
-/

namespace BretecheTenenbaumMean

open Real

/-- Stirling's lower bound and `log v ≤ v-1` bound an individual exponential term. -/
theorem factorial_term_le_stirling {u : ℝ} (hu : 0 ≤ u) {r : ℕ} (hr : r ≠ 0) :
    u ^ r / (r.factorial : ℝ) ≤ exp u / sqrt (2 * π * r) := by
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hr
  have hf : 0 < (r.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos r
  have hs : 0 < sqrt (2 * π * r) := sqrt_pos.2 (by positivity)
  have hp : u ^ r ≤ exp u * ((r : ℝ) / exp 1) ^ r := by
    rcases hu.eq_or_lt with rfl | hu
    · simp only [zero_pow hr]
      positivity
    · have hl := log_le_sub_one_of_pos (div_pos hu hr0)
      have hmul := mul_le_mul_of_nonneg_left hl hr0.le
      have he : (r : ℝ) * ((u / r) - 1) = u - r := by field_simp
      rw [he] at hmul
      have hpower : (u / r) ^ r ≤ exp (u - r) := by
        calc (u / r) ^ r = exp ((r : ℝ) * log (u / r)) := by
                rw [exp_nat_mul, exp_log (div_pos hu hr0)]
             _ ≤ exp (u - r) := exp_le_exp.2 hmul
      calc u ^ r = (u / r) ^ r * (r : ℝ) ^ r := by rw [← mul_pow]; congr 1; field_simp
           _ ≤ exp (u - r) * (r : ℝ) ^ r := mul_le_mul_of_nonneg_right hpower (by positivity)
           _ = exp u * ((r : ℝ) / exp 1) ^ r := by
              rw [div_pow, exp_sub, show exp (r : ℝ) = (exp 1) ^ r by simpa only [mul_one] using exp_nat_mul (1 : ℝ) r]
              ring
  have hst := Stirling.le_factorial_stirling r
  rw [div_le_div_iff₀ hf hs]
  calc u ^ r * sqrt (2 * π * r) ≤ (exp u * ((r : ℝ) / exp 1) ^ r) * sqrt (2 * π * r) :=
          mul_le_mul_of_nonneg_right hp hs.le
       _ = exp u * (sqrt (2 * π * r) * ((r : ℝ) / exp 1) ^ r) := by ring
       _ ≤ exp u * (r.factorial : ℝ) := mul_le_mul_of_nonneg_left hst (exp_pos u).le

/-- Uniform Poisson point-mass bound, including `u=0` and `r=0`. -/
theorem factorial_term_uniform {u : ℝ} (hu : 0 ≤ u) (r : ℕ) :
    u ^ r / (r.factorial : ℝ) ≤ 8 * exp u / sqrt (1 + u) := by
  have hs : 0 < sqrt (1 + u) := sqrt_pos.2 (by linarith)
  have hterm : 0 ≤ u ^ r / (r.factorial : ℝ) := by positivity
  by_cases hfar : 2 * (r : ℝ) ≤ u
  · have hsmall := pow_div_factorial_le_exp (u / 2) (show 0 ≤ u / 2 by positivity) r
    have hterm' : u ^ r / (r.factorial : ℝ) ≤ exp (7 * u / 8) := by
      calc u ^ r / (r.factorial : ℝ) = (2 : ℝ) ^ r * ((u / 2) ^ r / (r.factorial : ℝ)) := by
              rw [← mul_div_assoc, ← mul_pow]
              congr 1
              ring
           _ ≤ (2 : ℝ) ^ r * exp (u / 2) := mul_le_mul_of_nonneg_left hsmall (by positivity)
           _ = exp ((r : ℝ) * log 2 + u / 2) := by
              rw [exp_add, exp_nat_mul, exp_log (by norm_num : (0 : ℝ) < 2)]
           _ ≤ exp (7 * u / 8) := by
              apply exp_le_exp.2
              have hl : log 2 ≤ 3 / 4 := by have := log_two_lt_d9; linarith
              have h := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg r)
              nlinarith
    have hs' : sqrt (1 + u) ≤ 8 * exp (u / 8) := by
      have hroot : sqrt (1 + u) ≤ 1 + u := by
        have hsq := sq_sqrt (show 0 ≤ 1 + u by linarith)
        have hnonneg := sqrt_nonneg (1 + u)
        nlinarith [sq_nonneg u]
      have he := add_one_le_exp (u / 8)
      linarith
    rw [le_div_iff₀ hs]
    calc (u ^ r / (r.factorial : ℝ)) * sqrt (1 + u)
        ≤ exp (7 * u / 8) * (8 * exp (u / 8)) := mul_le_mul hterm' hs' hs.le (exp_pos _).le
      _ = 8 * exp u := by rw [← mul_assoc, mul_comm _ 8, mul_assoc, ← exp_add]; congr 2; ring
  · have hr : r ≠ 0 := by intro hr; subst r; norm_num at hfar; linarith
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hr
    have hpi : 3 ≤ 2 * π := by have := pi_gt_three; linarith
    have hsq : 1 + u ≤ 2 * π * r := by
      have h := mul_le_mul_of_nonneg_right hpi (Nat.cast_nonneg r)
      linarith
    calc u ^ r / (r.factorial : ℝ) ≤ exp u / sqrt (2 * π * r) := factorial_term_le_stirling hu hr
         _ ≤ exp u / sqrt (1 + u) := by gcongr
         _ ≤ 8 * exp u / sqrt (1 + u) :=
          div_le_div_of_nonneg_right (by nlinarith [exp_pos u]) hs.le

end BretecheTenenbaumMean
