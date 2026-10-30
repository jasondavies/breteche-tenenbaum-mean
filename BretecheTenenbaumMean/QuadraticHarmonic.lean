module

public import BretecheTenenbaumMean.QuadraticExpectation
public import BretecheTenenbaumMean.DivisorPowerSums
public import BretecheTenenbaumMean.SquarefreeTransfer

@[expose] public section

/-! # The harmonic quadratic mean over all integers -/

namespace BretecheTenenbaumMean

open Finset Real

/-- Square factors can be removed in the quadratic mean as well. -/
theorem harmonic_delta_sq_le_expectation {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, (hooleyDelta n : ℝ) ^ 2 / n) ≤
      (π ^ 2 / 6) ^ 16 * normalizer (2 * x) *
        expectation (2 * x) (fun n ↦ (hooleyDelta n : ℝ) ^ 2) := by
  have h := harmonic_squareFactor_bound (fun n ↦ (hooleyDelta n : ℝ) ^ 2)
    (fun b ↦ tau (b ^ 2) ^ 2) (fun _ ↦ sq_nonneg _) (fun _ ↦ sq_nonneg _)
    (fun b a ↦ by
      have h := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (hooleyDelta (b ^ 2 * a)))
        (hooleyDelta_mul_le_tau (b ^ 2) a) 2
      simpa only [mul_pow] using h) sum_tau_square_sq_div_sq_le hx
  convert h using 1
  unfold expectation
  field_simp [(normalizer_pos (2 * x)).ne']

lemma doubled_cutoff_regularized_log_bounds {x : ℝ} (hx : 2 ≤ x) :
    log (2 * x) ≤ 2 * log x ∧ log (1 + log (2 * x)) ≤ 2 * log (1 + log x) := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < log x := log_pos (by linarith)
  have hlog : log (2 : ℝ) ≤ log x := log_le_log (by norm_num) hx
  have hd : log (2 * x) ≤ 2 * log x := by rw [log_mul (by norm_num) hx0.ne']; linarith
  refine ⟨hd, ?_⟩
  have h0 : 0 < 1 + log (2 * x) := by
    have := log_pos (show 1 < 2 * x by linarith)
    linarith
  calc
    _ ≤ log ((1 + log x) ^ 2) := log_le_log h0 (by nlinarith [sq_nonneg (log x)])
    _ = _ := by rw [log_pow]; norm_num

/-- The quadratic harmonic sum has the expected extra factor of `log x`. -/
theorem harmonic_delta_sq_bound : ∃ C > 0, ∀ x : ℝ, 2 ≤ x →
    (∑ n ∈ Ioc 0 ⌊x⌋₊, (hooleyDelta n : ℝ) ^ 2 / n) ≤
      C * log x ^ 2 * log (1 + log x) ^ 2 := by
  obtain ⟨A, hA, hmean⟩ := expectation_delta_sq_bound
  obtain ⟨_, B, _, hB, hnorm⟩ := PrimeSums.normalizer_bounds
  let D : ℝ := (π ^ 2 / 6) ^ 16
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨16 * D * B * A, by positivity, fun x hx ↦ ?_⟩
  have h2x : 2 ≤ 2 * x := by linarith
  have hlx : 0 < log x := log_pos (by linarith)
  have hl2x : 0 < log (2 * x) := log_pos (by linarith)
  have hL : 0 ≤ log (1 + log (2 * x)) := log_nonneg (by linarith)
  have hlog := doubled_cutoff_regularized_log_bounds hx
  have he : 0 ≤ expectation (2 * x) (fun n ↦ (hooleyDelta n : ℝ) ^ 2) :=
    expectation_nonneg _ (fun n _ ↦ sq_nonneg _)
  calc
    _ ≤ D * normalizer (2 * x) * expectation (2 * x) (fun n ↦ (hooleyDelta n : ℝ) ^ 2) :=
      harmonic_delta_sq_le_expectation (by linarith)
    _ ≤ D * (B * log (2 * x)) * (A * log (2 * x) * log (1 + log (2 * x)) ^ 2) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hnorm (2 * x) h2x).2 hD.le
      · exact hmean (2 * x) h2x
      · exact he
      · positivity
    _ = D * B * A * log (2 * x) ^ 2 * log (1 + log (2 * x)) ^ 2 := by ring
    _ ≤ D * B * A * (2 * log x) ^ 2 * (2 * log (1 + log x)) ^ 2 := by
      gcongr
      · exact hlog.1
      · exact hlog.2
    _ = _ := by ring

end BretecheTenenbaumMean
