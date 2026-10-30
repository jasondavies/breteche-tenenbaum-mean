module

public import BretecheTenenbaumMean.RecursionErrorProducts

@[expose] public section

/-! # The product sum in the third-moment base case -/

namespace BretecheTenenbaumMean

open Finset Real

/-- The positive saving in (2.18), equal to `(3 - sqrt 8)/2`. -/
noncomputable def thirdMomentSaving : ℝ := 3 / 2 - sqrt 2

theorem thirdMomentSaving_pos : 0 < thirdMomentSaving := by
  have h := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs := sqrt_nonneg (2 : ℝ)
  dsimp only [thirdMomentSaving]
  nlinarith

theorem thirdMomentSaving_pow_identity {L : ℝ} (hL : 0 < L) :
    sqrt L * L ^ (sqrt 2) * L ^ thirdMomentSaving = L ^ 2 := by
  rw [sqrt_eq_rpow, ← rpow_add hL, ← rpow_add hL]
  have he : (1 / 2 : ℝ) + sqrt 2 + thirdMomentSaving = 2 := by
    dsimp only [thirdMomentSaving]
    ring
  rw [he]
  norm_num

end BretecheTenenbaumMean
