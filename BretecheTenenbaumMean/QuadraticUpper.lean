module

public import BretecheTenenbaumMean.QuadraticHarmonic
public import BretecheTenenbaumMean.QuadraticLogAverage

@[expose] public section

/-! # The upper bound in Theorem 1.2 -/

namespace BretecheTenenbaumMean

open Finset Real

lemma quadraticSum_regularized_bound : ∃ C > 0, ∀ x : ℝ, 2 ≤ x →
    quadraticSum x ≤ x + C * x * log x * log (1 + log x) ^ 2 := by
  obtain ⟨A, hA, hmean⟩ := quadraticSum_le_harmonic
  obtain ⟨B, hB, hharmonic⟩ := harmonic_delta_sq_bound
  refine ⟨A * B, by positivity, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hlx : 0 < log x := log_pos (by linarith)
  calc
    _ ≤ x + A * x / log x * ∑ n ∈ Ioc 0 ⌊x⌋₊, (hooleyDelta n : ℝ) ^ 2 / n :=
      hmean x hx
    _ ≤ x + A * x / log x * (B * log x ^ 2 * log (1 + log x) ^ 2) := by
      gcongr
      exact hharmonic x hx
    _ = _ := by field_simp

/-- The upper half of Theorem 1.2, on the paper's full range `x ≥ 3`. -/
theorem theoremTwo_upper : ∃ C > 0, ∀ x : ℝ, 3 ≤ x →
    quadraticSum x ≤ C * x * log x * log (log x) ^ 2 := by
  obtain ⟨A, hA, hmean⟩ := quadraticSum_regularized_bound
  have hl3 : 1 < log (3 : ℝ) := by linarith [log_three_gt_d9]
  have hs3 : 0 < log (log (3 : ℝ)) := log_pos hl3
  let c := log 3 * log (log 3) ^ 2
  let H := 1 + log 2 / log (log 3)
  have hc : 0 < c := by dsimp [c]; positivity
  have hH : 0 < H := by
    dsimp [H]
    have := log_pos (show (1 : ℝ) < 2 by norm_num)
    positivity
  refine ⟨1 / c + A * H ^ 2, by positivity, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hlog : log 3 ≤ log x := log_le_log (by norm_num) hx
  have hlx : 0 < log x := by linarith
  have hs : log (log 3) ≤ log (log x) := log_le_log (by linarith) hlog
  have hsx : 0 < log (log x) := hs3.trans_le hs
  have hsmall : c ≤ log x * log (log x) ^ 2 := by
    exact mul_le_mul hlog (pow_le_pow_left₀ hs3.le hs 2) (sq_nonneg _) hlx.le
  have hreg : log (1 + log x) ≤ H * log (log x) := by
    have h := log_le_log (show 0 < 1 + log x by linarith)
      (show 1 + log x ≤ 2 * log x by linarith)
    rw [log_mul (by norm_num) hlx.ne'] at h
    have hratio : log 2 ≤ (log 2 / log (log 3)) * log (log x) := by
      have hmul := mul_le_mul_of_nonneg_left hs
        (div_nonneg (log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)) hs3.le)
      have he : (log 2 / log (log 3)) * log (log 3) = log 2 := by field_simp
      rw [he] at hmul
      exact hmul
    dsimp [H]
    nlinarith
  have hreg0 : 0 ≤ log (1 + log x) := log_nonneg (by linarith)
  have hreg2 := pow_le_pow_left₀ hreg0 hreg 2
  have hxsmall : x ≤ (1 / c) * x * log x * log (log x) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ x / c by positivity)
    have he : x / c * c = x := by field_simp
    rw [he] at h
    convert h using 1; ring
  calc
    _ ≤ x + A * x * log x * log (1 + log x) ^ 2 := hmean x (by linarith)
    _ ≤ x + A * x * log x * (H * log (log x)) ^ 2 := by gcongr
    _ ≤ (1 / c) * x * log x * log (log x) ^ 2 +
        A * x * log x * (H * log (log x)) ^ 2 := add_le_add_left hxsmall _
    _ = _ := by ring

end BretecheTenenbaumMean
