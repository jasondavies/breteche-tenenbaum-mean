module

public import BretecheTenenbaumMean.PoissonTail
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

@[expose] public section

/-! # Quantitative convexity of the Poisson rate function -/

namespace BretecheTenenbaumMean

open Real

@[simp] theorem poissonRate_two : poissonRate 2 = log 4 - 1 := by
  have he : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num
  rw [poissonRate, he]
  ring

theorem hasDerivAt_poissonRate {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt poissonRate (log v) v := by
  convert ((hasDerivAt_mul_log hv).sub (hasDerivAt_id v)).add_const 1 using 1
  · rfl
  · simp

/-- A quantitative lower tangent bound for the logarithm above two. -/
theorem log_sub_log_two_ge {v M : ℝ} (hv : 2 ≤ v) (hvM : v ≤ M) :
    (v - 2) / M ≤ log v - log 2 := by
  have hv0 : 0 < v := by linarith
  have h := log_le_sub_one_of_pos (div_pos (by norm_num : (0 : ℝ) < 2) hv0)
  rw [log_div (by norm_num : (2 : ℝ) ≠ 0) hv0.ne'] at h
  calc (v - 2) / M ≤ (v - 2) / v := div_le_div_of_nonneg_left (by linarith) hv0 hvM
    _ = 1 - 2 / v := by field_simp
    _ ≤ _ := by linarith

/-- The corresponding upper bound below two, with the same coefficient. -/
theorem log_sub_log_two_le {v M : ℝ} (hv : 0 < v) (hv2 : v ≤ 2) (hM : 2 ≤ M) :
    log v - log 2 ≤ (v - 2) / M := by
  have hM0 : 0 < M := by linarith
  have h := log_le_sub_one_of_pos (div_pos hv (by norm_num : (0 : ℝ) < 2))
  rw [log_div hv.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h
  calc log v - log 2 ≤ (v - 2) / 2 := by linarith
    _ ≤ (v - 2) / M := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hM0]
      nlinarith [mul_nonpos_of_nonpos_of_nonneg (by linarith : v - 2 ≤ 0) (by linarith : 0 ≤ M - 2)]

/-- Taylor's lower bound at two, with an explicit uniform quadratic remainder.
It remains valid arbitrarily close to the center; no error term is divided by
the distance to that center. -/
theorem poissonRate_quadratic_lower {v M : ℝ} (hv : 0 < v) (hvM : v ≤ M) (hM : 2 ≤ M) :
    poissonRate 2 + log 2 * (v - 2) + (v - 2) ^ 2 / (2 * M) ≤ poissonRate v := by
  let F := fun z : ℝ ↦ poissonRate z - poissonRate 2 - log 2 * (z - 2) - (z - 2) ^ 2 / (2 * M)
  let D := fun z : ℝ ↦ log z - log 2 - (z - 2) / M
  have hM0 : 0 < M := by linarith
  have hd : ∀ z : ℝ, 0 < z → HasDerivAt F (D z) z := by
    intro z hz
    have h := (((hasDerivAt_poissonRate hz.ne').sub_const (poissonRate 2)).sub
      (((hasDerivAt_id z).sub_const 2).const_mul (log 2))).sub
      ((((hasDerivAt_id z).sub_const 2).pow 2).div_const (2 * M))
    convert h using 1
    · rfl
    · dsimp only [D, id_eq]
      ring
  have hzero : F 2 = 0 := by simp [F]
  have hF : 0 ≤ F v := by
    rcases le_total (2 : ℝ) v with hv2 | hv2
    · have hm : MonotoneOn F (Set.Icc 2 v) := by
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
        · intro z hz
          exact (hd z (by linarith [hz.1])).continuousAt.continuousWithinAt
        · intro z hz
          have hz' := interior_subset hz
          exact (hd z (by linarith [hz'.1])).hasDerivWithinAt
        · intro z hz
          have hz' := interior_subset hz
          have h := log_sub_log_two_ge hz'.1 (hz'.2.trans hvM)
          dsimp only [D]
          linarith
      have h := hm ⟨le_rfl, hv2⟩ ⟨hv2, le_rfl⟩ hv2
      simpa only [hzero] using h
    · have hm : AntitoneOn F (Set.Icc v 2) := by
        apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
        · intro z hz
          exact (hd z (hv.trans_le hz.1)).continuousAt.continuousWithinAt
        · intro z hz
          have hz' := interior_subset hz
          exact (hd z (hv.trans_le hz'.1)).hasDerivWithinAt
        · intro z hz
          have hz' := interior_subset hz
          have h := log_sub_log_two_le (hv.trans_le hz'.1) hz'.2 hM
          dsimp only [D]
          linarith
      have h := hm ⟨le_rfl, hv2⟩ ⟨hv2, le_rfl⟩ hv2
      simpa only [hzero] using h
  dsimp only [F] at hF
  linarith

/-- The cancellation of the linear terms explains the critical scale
`log T / (log 4 - 1)` in the good-set penalty. -/
theorem poissonRate_scaled_quadratic_lower {u k M : ℝ}
    (hu : 0 < u) (hk : 0 < k) (hkM : k / u ≤ M) (hM : 2 ≤ M) :
    k * log 2 - u + (k - 2 * u) ^ 2 / (2 * M * u) ≤ u * poissonRate (k / u) := by
  have h := mul_le_mul_of_nonneg_left (poissonRate_quadratic_lower (div_pos hk hu) hkM hM) hu.le
  have h2 : poissonRate 2 = 2 * log 2 - 1 := by unfold poissonRate; ring
  rw [h2] at h
  convert h using 1
  field_simp
  ring

end BretecheTenenbaumMean
