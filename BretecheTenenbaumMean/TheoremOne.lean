module

public import BretecheTenenbaumMean.DeltaLogAverage
public import BretecheTenenbaumMean.SquarefreeTransfer
public import BretecheTenenbaumMean.DeltaExpectation

@[expose] public section

/-! # Theorem 1.1: the ordinary mean of the Erdős–Hooley Delta function -/

namespace BretecheTenenbaumMean

open Finset Real

lemma doubled_cutoff_log_bounds {x : ℝ} (hx : exp (exp 4) ≤ x) :
    log (2 * x) ≤ 2 * log x ∧ log (log (2 * x)) ≤ 2 * log (log x) := by
  obtain ⟨hx3, hq, hqle, _⟩ := moment_order_floor_bounds hx
  have hx0 : 0 < x := by linarith
  have hlx : 0 < log x := log_pos (by linarith)
  have hs : 1 ≤ log (log x) := by
    have hq' : (3 : ℝ) ≤ ⌊log (log x)⌋₊ := by exact_mod_cast hq
    linarith
  have hl2x : log (2 : ℝ) ≤ log x := log_le_log (by norm_num) (by linarith)
  have hd : log (2 * x) ≤ 2 * log x := by
    rw [log_mul (by norm_num) hx0.ne']
    linarith
  refine ⟨hd, ?_⟩
  have h := log_le_log (log_pos (show 1 < 2 * x by linarith)) hd
  rw [log_mul (by norm_num) hlx.ne'] at h
  have h2 := log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  linarith

/-- Theorem 1.1, including the transfer from the finite squarefree model to
all positive integers. All constants are absolute. -/
theorem theoremOne : TheoremOne := by
  obtain ⟨A, hA, hmean⟩ := meanSum_le_harmonic
  obtain ⟨_, D, _, hD, hnorm⟩ := PrimeSums.normalizer_bounds
  obtain ⟨K, hK, hexpect⟩ := hooleyDelta_expectation_bound
  let B : ℝ := (π ^ 2 / 6) ^ 3
  let E : ℝ := 2 * A * B * D * K * (2 : ℝ) ^ (5 / 2 : ℝ)
  have hB : 0 < B := by dsimp [B]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨1 + E, by positivity, exp (exp 4),
    (moment_order_floor_bounds (x := exp (exp 4)) le_rfl).1, fun x hx ↦ ?_⟩
  obtain ⟨hx3, hq, hqle, _⟩ := moment_order_floor_bounds hx
  have hx0 : 0 < x := by linarith
  have hlx : 0 < log x := log_pos (by linarith)
  have hs : 1 ≤ log (log x) := by
    have hq' : (3 : ℝ) ≤ ⌊log (log x)⌋₊ := by exact_mod_cast hq
    linarith
  have h2x : exp (exp 4) ≤ 2 * x := hx.trans (by linarith)
  have h2x2 : 2 ≤ 2 * x := by linarith
  have hlog := doubled_cutoff_log_bounds hx
  have hs2 : 0 ≤ log (log (2 * x)) := by
    obtain ⟨_, hq2, hqle2, _⟩ := moment_order_floor_bounds h2x
    exact (Nat.cast_nonneg _).trans hqle2
  have hp : log (log (2 * x)) ^ (5 / 2 : ℝ) ≤
      (2 : ℝ) ^ (5 / 2 : ℝ) * log (log x) ^ (5 / 2 : ℝ) := by
    calc
      _ ≤ (2 * log (log x)) ^ (5 / 2 : ℝ) := rpow_le_rpow hs2 hlog.2 (by norm_num)
      _ = _ := mul_rpow (by norm_num) (by linarith)
  have hnorm' : normalizer (2 * x) ≤ D * (2 * log x) :=
    (hnorm (2 * x) h2x2).2.trans (mul_le_mul_of_nonneg_left hlog.1 hD.le)
  have hexpect' : expectation (2 * x) (fun n ↦ (hooleyDelta n : ℝ)) ≤
      K * ((2 : ℝ) ^ (5 / 2 : ℝ) * log (log x) ^ (5 / 2 : ℝ)) :=
    (hexpect (2 * x) h2x).trans (mul_le_mul_of_nonneg_left hp hK.le)
  have he0 : 0 ≤ expectation (2 * x) (fun n ↦ (hooleyDelta n : ℝ)) :=
    expectation_nonneg _ (fun _ _ ↦ Nat.cast_nonneg _)
  have hh : (∑ n ∈ Ioc 0 ⌊x⌋₊, (hooleyDelta n : ℝ) / n) ≤
      B * (D * (2 * log x)) *
        (K * ((2 : ℝ) ^ (5 / 2 : ℝ) * log (log x) ^ (5 / 2 : ℝ))) := by
    calc
      _ ≤ B * normalizer (2 * x) * expectation (2 * x) (fun n ↦ (hooleyDelta n : ℝ)) :=
        harmonic_delta_le_expectation (by linarith)
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hnorm' hB.le) hexpect' he0 (by positivity)
  have hpow : 1 ≤ log (log x) ^ (5 / 2 : ℝ) := one_le_rpow hs (by norm_num)
  calc
    meanSum x ≤ x + A * x / log x * ∑ n ∈ Ioc 0 ⌊x⌋₊, (hooleyDelta n : ℝ) / n :=
      hmean x (by linarith)
    _ ≤ x + A * x / log x * (B * (D * (2 * log x)) *
        (K * ((2 : ℝ) ^ (5 / 2 : ℝ) * log (log x) ^ (5 / 2 : ℝ)))) := by
      gcongr
    _ = x + E * x * log (log x) ^ (5 / 2 : ℝ) := by
      dsimp [E]
      field_simp
    _ ≤ (1 + E) * x * log (log x) ^ (5 / 2 : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hpow hx0.le]

end BretecheTenenbaumMean
