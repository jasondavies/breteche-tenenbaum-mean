module

public import BretecheTenenbaumMean.GridThreshold

@[expose] public section

/-! # Uniform entropy lower bounds for the grid thresholds -/

namespace BretecheTenenbaumMean

open Real

/-- Bounded errors in the Poisson mean and the integer threshold only cost an
absolute additive error in the exponent, uniformly over every grid scale. -/
theorem grid_entropy_lower {δ t r u k K : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 1000000) (hK : 0 ≤ K)
    (ht : 100 * (K + 1) ≤ t) (hr : 0 ≤ r) (hu0 : 0 < u) (hu : |u - r| ≤ K)
    (hklo : (5 / 4 : ℝ) * (t + r) ≤ k) (hkhi : k ≤ 2 * (t + r))
    (he : |k * log 2 - (t + r - δ * min (t + r) ((r - criticalSlope * t) ^ 2 / t))| ≤ 7) :
    t + δ * min (t + r) ((r - criticalSlope * t) ^ 2 / t) - (K + 7) - (K + 7) ^ 2 ≤
      u * poissonRate (k / u) := by
  let S := t + r
  let E := K + 7
  let f := δ * min (t + r) ((r - criticalSlope * t) ^ 2 / t)
  let q := (r - criticalSlope * t) ^ 2 / S
  have ht0 : 0 < t := by nlinarith
  have hS : 1 ≤ S := by dsimp only [S]; nlinarith
  have hS0 : 0 < S := by linarith
  have hE : 0 ≤ E := by dsimp only [E]; linarith
  have hk0 : 0 < k := by dsimp only [S] at hS; nlinarith
  have huS : u ≤ S := by
    have h := (abs_le.1 hu).2
    dsimp only [S]
    nlinarith
  have hmax : max (2 * u) k ≤ 2 * S := max_le (by linarith) hkhi
  have hden : 0 < 2 * max (2 * u) k := by have := le_max_left (2 * u) k; linarith
  have hQ := poissonRate_scaled_global_lower hu0 hk0
  have hd := critical_distance_le_count_error hδ hδ1 ht0 hr hK hu he
  have hsquare : (r - criticalSlope * t) ^ 2 ≤ 18 * (k - 2 * u) ^ 2 + 72 * E ^ 2 := by
    have hsq := (sq_le_sq₀ (abs_nonneg (r - criticalSlope * t))
      (show 0 ≤ 3 * |k - 2 * u| + 6 * (K + 7) by positivity)).2 hd
    rw [sq_abs] at hsq
    have hg := sq_abs (k - 2 * u)
    dsimp only [E]
    nlinarith [sq_nonneg (3 * |k - 2 * u| - 6 * (K + 7))]
  have hrem : q / 144 - E ^ 2 / (2 * S) ≤ (k - 2 * u) ^ 2 / (8 * S) := by
    calc q / 144 - E ^ 2 / (2 * S) =
        ((r - criticalSlope * t) ^ 2 - 72 * E ^ 2) / (144 * S) := by dsimp only [q]; field_simp; ring
      _ ≤ (18 * (k - 2 * u) ^ 2) / (144 * S) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by field_simp; ring
  have herr : E ^ 2 / (2 * S) ≤ E ^ 2 := by
    rw [div_le_iff₀ (by positivity : 0 < 2 * S)]
    nlinarith [mul_nonneg (sq_nonneg E) (sub_nonneg.2 hS)]
  have hquad : (k - 2 * u) ^ 2 / (8 * S) ≤ (k - 2 * u) ^ 2 / (2 * max (2 * u) k) :=
    div_le_div_of_nonneg_left (sq_nonneg _) hden (by linarith)
  have hf : f ≤ 25 * δ * q := by
    have h := mul_le_mul_of_nonneg_left (clipped_penalty_le_quadratic ht0 hr) hδ
    convert h using 1
    dsimp only [q, S]
    ring
  have hq : 0 ≤ q := div_nonneg (sq_nonneg _) hS0.le
  have hδq := mul_le_mul_of_nonneg_right (show 50 * δ ≤ 1 / 144 by linarith) hq
  have hf2 : 2 * f ≤ q / 144 := by nlinarith
  have hlinear : t - f - (K + 7) ≤ k * log 2 - u := by
    have h1 := (abs_le.1 he).1
    have h2 := (abs_le.1 hu).2
    change -(7 : ℝ) ≤ k * log 2 - (t + r - f) at h1
    linarith
  change t + f - E - E ^ 2 ≤ _
  change t - f - E ≤ _ at hlinear
  linarith

end BretecheTenenbaumMean
