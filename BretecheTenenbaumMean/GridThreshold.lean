module

public import BretecheTenenbaumMean.PenaltyComparison
public import BretecheTenenbaumMean.GoodSetReduction

@[expose] public section

/-! # Rounded thresholds with explicit large-deviation errors -/

namespace BretecheTenenbaumMean

open Real

/-- The defining identity for the critical scale. -/
theorem criticalSlope_log_identity : 2 * criticalSlope * log 2 = criticalSlope + 1 := by
  have hl : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num
  have hc : log 4 - 1 ≠ 0 := ne_of_gt (by rw [hl]; linarith [log_two_gt_d9])
  have h : criticalSlope * (log 4 - 1) = 1 := by unfold criticalSlope; field_simp
  rw [hl] at h
  nlinarith

/-- The integer cutoff is within a bounded logarithmic error and comparable
to the sum of the two logarithmic scales. -/
theorem rounded_grid_threshold_bounds {δ t r : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 1000000) (ht : 100 ≤ t) (hr : 0 ≤ r) :
    let f := δ * min (t + r) ((r - criticalSlope * t) ^ 2 / t)
    let k := ⌈(t + r - f - 7) / log 2⌉₊
    0 ≤ f ∧ f ≤ (t + r) / 100 ∧
      (5 / 4 : ℝ) * (t + r) ≤ k ∧ (k : ℝ) ≤ 2 * (t + r) ∧
      |(k : ℝ) * log 2 - (t + r - f)| ≤ 7 := by
  dsimp only
  let f := δ * min (t + r) ((r - criticalSlope * t) ^ 2 / t)
  let k := ⌈(t + r - f - 7) / log 2⌉₊
  have ht0 : 0 < t := by linarith
  have hS : 0 < t + r := by linarith
  have hf0 : 0 ≤ f := mul_nonneg hδ (le_min hS.le (div_nonneg (sq_nonneg _) ht0.le))
  have hf : f ≤ (t + r) / 100 := by
    have h1 := mul_le_mul_of_nonneg_left (min_le_left (t + r) ((r - criticalSlope * t) ^ 2 / t)) hδ
    have h2 := mul_le_mul_of_nonneg_right hδ1 hS.le
    dsimp only [f] at *
    linarith
  have hlog : 0 < log 2 := log_pos (by norm_num)
  have hz : 0 ≤ (t + r - f - 7) / log 2 := div_nonneg (by linarith) hlog.le
  have hlow : t + r - f - 7 ≤ (k : ℝ) * log 2 := (div_le_iff₀ hlog).1 (Nat.le_ceil _)
  have hupp : (k : ℝ) * log 2 < t + r - f - 7 + log 2 := by
    have h := (Nat.ceil_lt_add_one hz)
    have hm := (mul_lt_mul_iff_left₀ hlog).2 h
    dsimp only [k] at *
    field_simp at hm
    linarith
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hlogU : log 2 ≤ 7 / 10 := by linarith [log_two_lt_d9]
  have hlogL : 1 / 2 ≤ log 2 := by linarith [log_two_gt_d9]
  have hklo : (5 / 4 : ℝ) * (t + r) ≤ k := by
    have h := mul_le_mul_of_nonneg_left hlogU hk0
    nlinarith
  have hkhi : (k : ℝ) ≤ 2 * (t + r) := by
    have h := mul_le_mul_of_nonneg_left hlogL hk0
    linarith
  have he : |(k : ℝ) * log 2 - (t + r - f)| ≤ 7 := by
    rw [abs_le]
    constructor <;> linarith [log_two_lt_d9]
  exact ⟨hf0, hf, hklo, hkhi, he⟩

/-- The distance from the critical scale is controlled by the count deviation
and the bounded errors from Mertens and the rounded threshold. -/
theorem critical_distance_le_count_error {δ t r u k K : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 1000000) (ht : 0 < t) (hr : 0 ≤ r)
    (hK : 0 ≤ K) (hu : |u - r| ≤ K)
    (he : |k * log 2 - (t + r - δ * min (t + r) ((r - criticalSlope * t) ^ 2 / t))| ≤ 7) :
    |r - criticalSlope * t| ≤ 3 * |k - 2 * u| + 6 * (K + 7) := by
  let f := δ * min (t + r) ((r - criticalSlope * t) ^ 2 / t)
  let e := k * log 2 - (t + r - f)
  have hf0 : 0 ≤ f := mul_nonneg hδ (le_min (by linarith) (div_nonneg (sq_nonneg _) ht.le))
  have hf : f ≤ 5 * δ * |r - criticalSlope * t| := by
    have h := mul_le_mul_of_nonneg_left (clipped_penalty_le_abs ht hr) hδ
    dsimp only [f]
    nlinarith
  have hb0 := criticalSlope_pos
  have hb3 := criticalSlope_le_three
  have hbl0 : 0 ≤ criticalSlope * log 2 := mul_nonneg hb0.le (log_pos (by norm_num)).le
  have hbl2 : criticalSlope * log 2 ≤ 2 := by linarith [criticalSlope_log_identity]
  have hid : r - criticalSlope * t =
      -(criticalSlope * log 2 * (k - 2 * u)) + -(criticalSlope * f) +
        criticalSlope * e + -((criticalSlope + 1) * (u - r)) := by
    dsimp only [e]
    nlinarith [congrArg (fun z : ℝ ↦ z * u) criticalSlope_log_identity]
  have htri : |r - criticalSlope * t| ≤
      criticalSlope * log 2 * |k - 2 * u| + criticalSlope * f +
        criticalSlope * |e| + (criticalSlope + 1) * |u - r| := by
    rw [hid]
    have h1 := abs_add_le (-(criticalSlope * log 2 * (k - 2 * u)) + -(criticalSlope * f) + criticalSlope * e)
      (-((criticalSlope + 1) * (u - r)))
    have h2 := abs_add_le (-(criticalSlope * log 2 * (k - 2 * u)) + -(criticalSlope * f)) (criticalSlope * e)
    have h3 := abs_add_le (-(criticalSlope * log 2 * (k - 2 * u))) (-(criticalSlope * f))
    simp only [abs_neg, abs_mul, abs_of_nonneg hb0.le, abs_of_nonneg hbl0,
      abs_of_nonneg hf0, abs_of_nonneg (show 0 ≤ criticalSlope + 1 by linarith)] at h1 h2 h3
    linarith
  have hgap := mul_le_mul_of_nonneg_right hbl2 (abs_nonneg (k - 2 * u))
  have hff := mul_le_mul_of_nonneg_left hf hb0.le
  have hδsmall : criticalSlope * (5 * δ) ≤ 1 / 4 := by
    have h := mul_le_mul hb3 hδ1 hδ (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith
  have hfa := mul_le_mul_of_nonneg_right hδsmall (abs_nonneg (r - criticalSlope * t))
  have herr := mul_le_mul hb3 he (abs_nonneg e) (by norm_num : (0 : ℝ) ≤ 3)
  have hur := mul_le_mul (show criticalSlope + 1 ≤ 4 by linarith) hu (abs_nonneg (u - r)) (by norm_num : (0 : ℝ) ≤ 4)
  change criticalSlope * |e| ≤ 3 * 7 at herr
  nlinarith [abs_nonneg (k - 2 * u)]

end BretecheTenenbaumMean
