module

public import BretecheTenenbaumMean.GoodSetGrid
public import BretecheTenenbaumMean.PoissonRate

@[expose] public section

/-! # Global comparisons for the clipped penalty

These bounds treat both extreme scales and the critical scale together.
-/

namespace BretecheTenenbaumMean

open Real

/-- Clipping the quadratic penalty makes it globally bounded by a constant
times the distance from the critical scale. -/
theorem clipped_penalty_le_abs {t u : ℝ} (ht : 0 < t) (_hu : 0 ≤ u) :
    min (t + u) ((u - criticalSlope * t) ^ 2 / t) ≤ 5 * |u - criticalSlope * t| := by
  let d := |u - criticalSlope * t|
  have hd : 0 ≤ d := abs_nonneg _
  have hu' : u ≤ d + 3 * t := by
    have h := le_abs_self (u - criticalSlope * t)
    have hb := mul_le_mul_of_nonneg_right criticalSlope_le_three ht.le
    dsimp only [d]
    linarith
  by_cases hsmall : d ≤ t
  · refine (min_le_right _ _).trans ?_
    rw [div_le_iff₀ ht]
    have hsq : (u - criticalSlope * t) ^ 2 = d ^ 2 := (sq_abs _).symm
    rw [hsq]
    change d ^ 2 ≤ 5 * d * t
    nlinarith [mul_nonneg hd (sub_nonneg.2 hsmall)]
  · exact (min_le_left _ _).trans (by change t + u ≤ 5 * d; linarith)

/-- A global quadratic comparison with denominator `t+u`, avoiding separate
small-, middle-, and large-scale regimes. -/
theorem clipped_penalty_le_quadratic {t u : ℝ} (ht : 0 < t) (hu : 0 ≤ u) :
    min (t + u) ((u - criticalSlope * t) ^ 2 / t) ≤
      25 * (u - criticalSlope * t) ^ 2 / (t + u) := by
  let d := |u - criticalSlope * t|
  have hd : 0 ≤ d := abs_nonneg _
  have hsum : 0 < t + u := by linarith
  have hsq : (u - criticalSlope * t) ^ 2 = d ^ 2 := (sq_abs _).symm
  have hu' : u ≤ d + 3 * t := by
    have h := le_abs_self (u - criticalSlope * t)
    have hb := mul_le_mul_of_nonneg_right criticalSlope_le_three ht.le
    dsimp only [d]
    linarith
  by_cases hsmall : d ≤ t
  · refine (min_le_right _ _).trans ?_
    rw [div_le_div_iff₀ ht hsum, hsq]
    have hbound : t + u ≤ 25 * t := by linarith
    nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.2 hbound)]
  · refine (min_le_left _ _).trans ?_
    rw [le_div_iff₀ hsum, hsq]
    have hbound : t + u ≤ 5 * d := by linarith
    nlinarith [sq_nonneg (5 * d - (t + u))]

/-- Global version of the entropy remainder, with no boundedness assumption
on `k/u`. The denominator automatically switches between the two scales. -/
theorem poissonRate_scaled_global_lower {u k : ℝ} (hu : 0 < u) (hk : 0 < k) :
    k * log 2 - u + (k - 2 * u) ^ 2 / (2 * max (2 * u) k) ≤ u * poissonRate (k / u) := by
  let M := max (2 * u) k / u
  have hM : 2 ≤ M := (le_div_iff₀ hu).2 (le_max_left _ _)
  have hkM : k / u ≤ M := div_le_div_of_nonneg_right (le_max_right _ _) hu.le
  have h := poissonRate_scaled_quadratic_lower hu hk hkM hM
  have he : 2 * M * u = 2 * max (2 * u) k := by dsimp only [M]; field_simp
  simpa only [he] using h

/-- The clipped profile also retains a global quadratic lower bound. -/
theorem clipped_penalty_ge_quadratic {t u : ℝ} (ht : 0 < t) (hu : 0 ≤ u) :
    (u - criticalSlope * t) ^ 2 / (9 * (t + u)) ≤
      min (t + u) ((u - criticalSlope * t) ^ 2 / t) := by
  have hsum : 0 < t + u := by linarith
  have hb := mul_le_mul_of_nonneg_right criticalSlope_le_three ht.le
  have hb0 := mul_pos criticalSlope_pos ht
  have hd : |u - criticalSlope * t| ≤ 3 * (t + u) := by
    rw [abs_le]
    constructor <;> linarith
  have hsq : (u - criticalSlope * t) ^ 2 ≤ 9 * (t + u) ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg _) hd
    rw [← sq, sq_abs] at h
    nlinarith
  apply le_min
  · rw [div_le_iff₀ (by positivity : 0 < 9 * (t + u))]
    nlinarith
  · exact div_le_div_of_nonneg_left (sq_nonneg _) ht (by linarith)

theorem one_le_criticalSlope : 1 ≤ criticalSlope := by
  have he : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num
  have hc : 0 < log 4 - 1 := by rw [he]; linarith [log_two_gt_d9]
  rw [criticalSlope, one_le_div hc, he]
  linarith [log_two_lt_d9]

/-- In the square-root coordinate the global quadratic profile dominates a
translated Gaussian exponent with no parameter-dependent coefficient. -/
theorem penalty_quadratic_ge_sqrt_distance {t u : ℝ} (ht : 0 < t) (hu : 0 ≤ u) :
    (sqrt u - sqrt (criticalSlope * t)) ^ 2 ≤ (u - criticalSlope * t) ^ 2 / (t + u) := by
  have hc := sq_sqrt (mul_pos criticalSlope_pos ht).le
  have hu' := sq_sqrt hu
  have hb := mul_le_mul_of_nonneg_right one_le_criticalSlope ht.le
  have hs : t + u ≤ (sqrt u + sqrt (criticalSlope * t)) ^ 2 := by
    nlinarith [mul_nonneg (sqrt_nonneg u) (sqrt_nonneg (criticalSlope * t))]
  have he : (u - criticalSlope * t) ^ 2 =
      (sqrt u - sqrt (criticalSlope * t)) ^ 2 * (sqrt u + sqrt (criticalSlope * t)) ^ 2 := by
    calc _ = ((sqrt u) ^ 2 - (sqrt (criticalSlope * t)) ^ 2) ^ 2 := by rw [hc, hu']
      _ = _ := by ring
  rw [le_div_iff₀ (by linarith : 0 < t + u), he]
  exact mul_le_mul_of_nonneg_left hs (sq_nonneg _)

/-- A Gaussian lower bound for the full clipped profile, valid at every scale. -/
theorem clipped_penalty_ge_sqrt_distance {t u : ℝ} (ht : 0 < t) (hu : 0 ≤ u) :
    (sqrt u - sqrt (criticalSlope * t)) ^ 2 / 9 ≤
      min (t + u) ((u - criticalSlope * t) ^ 2 / t) := by
  have h := div_le_div_of_nonneg_right (penalty_quadratic_ge_sqrt_distance ht hu) (by norm_num : (0 : ℝ) ≤ 9)
  refine h.trans ?_
  convert clipped_penalty_ge_quadratic ht hu using 1
  rw [div_div]
  congr 1
  ring

end BretecheTenenbaumMean
