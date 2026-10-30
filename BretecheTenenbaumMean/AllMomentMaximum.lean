module

public import BretecheTenenbaumMean.AllMomentGoodSet
public import BretecheTenenbaumMean.WindowBounds

@[expose] public section

/-! # Recovering the maximum on the simultaneous moment good set -/

namespace BretecheTenenbaumMean

open Real

/-- A single moment order controls the maximum once it exceeds the
logarithmic size of the ambient prime cutoff. -/
theorem max_le_of_all_moments {δ C₀ T x : ℝ} (hδ : 0 ≤ δ) (hC : 1 ≤ C₀)
    (hT : 3 ≤ T) (hx : 1 ≤ x) {q n : ℕ} (hq : 1 ≤ q)
    (horder : log (log (3 * x)) ≤ 2 * (q : ℝ)) (hn : n ∈ smoothSupport x)
    (hE : n ∈ allMomentGoodSet δ T (explicitThreshold C₀ T)) :
    (hooleyDelta n : ℝ) ≤ 2 * exp 2 * q * thresholdScale C₀ T := by
  have hC0 : 0 < C₀ := by linarith
  have hT0 : 0 < T := by linarith
  have hs := thresholdScale_pos hC0 (by linarith : 1 < T)
  have hscale := thresholdScale_ge_T hC hT
  have hL : 0 < log (3 * x) := log_pos (by linarith)
  have hτ := tau_le_goodSet_log hδ (by linarith : 1 ≤ T) hx hn (hE q).1.1
  have hM := (hE q).2 q hq le_rfl
  have hθ := explicitThreshold_upper hC0 (by linarith : 1 < T) hq
  have hτ0 : 0 ≤ tau n := Nat.cast_nonneg _
  have hLexp : log (3 * x) ≤ (exp 2) ^ q := by
    have h := exp_le_exp.2 horder
    rw [exp_log hL] at h
    have he : exp (2 * (q : ℝ)) = (exp 2) ^ q := by rw [mul_comm, exp_nat_mul]
    rwa [he] at h
  have hscalePow : T * thresholdScale C₀ T ^ (q - 1) ≤ thresholdScale C₀ T ^ q := by
    have h := mul_le_mul_of_nonneg_right hscale (pow_nonneg hs.le (q - 1))
    simpa only [← pow_succ', Nat.sub_add_cancel hq] using h
  apply (pow_le_pow_iff_left₀ (Nat.cast_nonneg (hooleyDelta n)) (by positivity) (by omega : q ≠ 0)).1
  calc
    _ ≤ 2 ^ q * moment q n := max_pow_le_moment n q hq
    _ ≤ 2 ^ q * (tau n * explicitThreshold C₀ T q) := mul_le_mul_of_nonneg_left hM (by positivity)
    _ ≤ 2 ^ q * ((T * log (3 * x)) * ((q : ℝ) ^ q * thresholdScale C₀ T ^ (q - 1))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul hτ hθ (explicitThreshold_pos hC0 (by linarith) q).le (by positivity)
    _ = (2 * (q : ℝ)) ^ q * log (3 * x) * (T * thresholdScale C₀ T ^ (q - 1)) := by
      rw [mul_pow]
      ring
    _ ≤ (2 * (q : ℝ)) ^ q * log (3 * x) * thresholdScale C₀ T ^ q :=
      mul_le_mul_of_nonneg_left hscalePow (by positivity)
    _ ≤ (2 * (q : ℝ)) ^ q * (exp 2) ^ q * thresholdScale C₀ T ^ q := by gcongr
    _ = _ := by simp only [mul_pow]; ring

/-- Explicit floor control for the order chosen in §2.4. -/
theorem moment_order_floor_bounds {x : ℝ} (hx : exp (exp 4) ≤ x) :
    3 ≤ x ∧ 3 ≤ ⌊log (log x)⌋₊ ∧ (⌊log (log x)⌋₊ : ℝ) ≤ log (log x) ∧
      log (log (3 * x)) ≤ 2 * (⌊log (log x)⌋₊ : ℝ) := by
  have hx0 : 0 < x := (exp_pos _).trans_le hx
  have hlx : exp 4 ≤ log x := by
    have h := log_le_log (exp_pos _) hx
    simpa only [log_exp] using h
  have hs : 4 ≤ log (log x) := by
    have h := log_le_log (exp_pos _) hlx
    simpa only [log_exp] using h
  have hlx4 : 4 ≤ log x := by linarith [add_one_le_exp (4 : ℝ)]
  have hx3 : 3 ≤ x := by
    have h := add_one_le_exp (log x)
    rw [exp_log hx0] at h
    linarith
  have hfloor : 3 ≤ ⌊log (log x)⌋₊ := Nat.le_floor (by linarith : (3 : ℝ) ≤ log (log x))
  have hfloorle := Nat.floor_le (by linarith : 0 ≤ log (log x))
  refine ⟨hx3, hfloor, hfloorle, ?_⟩
  have hl3 : log 3 ≤ log x := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hL : log (3 * x) ≤ 2 * log x := by rw [log_mul (by norm_num) hx0.ne']; linarith
  have hLL := log_le_log (log_pos (show 1 < 3 * x by linarith)) hL
  rw [log_mul (by norm_num) (by linarith : log x ≠ 0)] at hLL
  have hlog2 : log 2 ≤ 1 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hf := Nat.lt_floor_add_one (log (log x))
  linarith

/-- The maximum is at most `C T sqrt(log T) log log x` on the simultaneous
good set, with an explicit constant depending only on the threshold scale. -/
theorem allMomentGoodSet_max_bound {δ C₀ : ℝ} (hδ : 0 ≤ δ) (hC : 1 ≤ C₀) :
    ∃ C > 0, ∀ x T : ℝ, exp (exp 4) ≤ x → 3 ≤ T → ∀ n ∈ smoothSupport x,
      n ∈ allMomentGoodSet δ T (explicitThreshold C₀ T) →
      (hooleyDelta n : ℝ) ≤ C * T * sqrt (log T) * log (log x) := by
  have hC0 : 0 < C₀ := by linarith
  refine ⟨2 * exp 2 * (2 * π ^ 2 * C₀ / 3), by positivity, fun x T hx hT n hn hE ↦ ?_⟩
  obtain ⟨hx3, hq, hqle, hord⟩ := moment_order_floor_bounds hx
  have hs := thresholdScale_pos hC0 (by linarith : 1 < T)
  calc
    _ ≤ 2 * exp 2 * (⌊log (log x)⌋₊ : ℝ) * thresholdScale C₀ T :=
      max_le_of_all_moments hδ hC hT (by linarith) (by omega) hord hn hE
    _ ≤ 2 * exp 2 * log (log x) * thresholdScale C₀ T := by gcongr
    _ = _ := by unfold thresholdScale; ring

end BretecheTenenbaumMean
