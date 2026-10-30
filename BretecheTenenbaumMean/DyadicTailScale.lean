module

public import BretecheTenenbaumMean.AllMomentMaximum
public import BretecheTenenbaumMean.FiniteTailExpectation

@[expose] public section

/-! # Dyadic thresholds for summing the maximum tail -/

namespace BretecheTenenbaumMean

open Real

noncomputable def dyadicTailLevel (j : ℕ) : ℝ := 2 ^ (j + 2)

noncomputable def dyadicTailThreshold (A s : ℝ) (j : ℕ) : ℝ :=
  A * dyadicTailLevel j * sqrt (log (dyadicTailLevel j)) * s

theorem dyadicTailLevel_ge_four (j : ℕ) : 4 ≤ dyadicTailLevel j := by
  have h : (2 : ℝ) ^ 2 ≤ 2 ^ (j + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num only [Nat.reducePow] at h
  exact h

theorem dyadicTailLevel_pos (j : ℕ) : 0 < dyadicTailLevel j := by
  have := dyadicTailLevel_ge_four j
  linarith

theorem log_dyadicTailLevel (j : ℕ) : log (dyadicTailLevel j) = ((j : ℝ) + 2) * log 2 := by
  simp only [dyadicTailLevel, log_pow, Nat.cast_add, Nat.cast_ofNat]

theorem dyadicTailThreshold_ge_level {A s : ℝ} (hA : 1 ≤ A) (hs : 1 ≤ s) (j : ℕ) :
    dyadicTailLevel j ≤ dyadicTailThreshold A s j := by
  have hl : 1 ≤ log (dyadicTailLevel j) :=
    (show (1 : ℝ) ≤ log 3 by linarith [log_three_gt_d9]).trans
      (log_le_log (by norm_num) (by linarith [dyadicTailLevel_ge_four j]))
  have hroot : 1 ≤ sqrt (log (dyadicTailLevel j)) := by simpa only [sqrt_one] using sqrt_le_sqrt hl
  have hlevel := dyadicTailLevel_pos j
  unfold dyadicTailThreshold
  calc
    _ ≤ A * dyadicTailLevel j := by nlinarith
    _ ≤ A * dyadicTailLevel j * sqrt (log (dyadicTailLevel j)) := by
      have h := mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ A * dyadicTailLevel j)
      simpa only [mul_one] using h
    _ ≤ _ := by nlinarith [mul_pos (mul_pos (by linarith : 0 < A) hlevel) (by linarith : 0 < sqrt (log (dyadicTailLevel j)))]

theorem dyadicTailThreshold_pos {A s : ℝ} (hA : 1 ≤ A) (hs : 1 ≤ s) (j : ℕ) :
    0 < dyadicTailThreshold A s j := (dyadicTailLevel_pos j).trans_le (dyadicTailThreshold_ge_level hA hs j)

theorem dyadicTailThreshold_next_div (A s : ℝ) (j : ℕ) :
    dyadicTailThreshold A s (j + 1) / dyadicTailLevel j =
      2 * A * s * sqrt (((j : ℝ) + 3) * log 2) := by
  have hp := dyadicTailLevel_pos j
  have he : dyadicTailLevel (j + 1) = 2 * dyadicTailLevel j := by
    unfold dyadicTailLevel
    rw [show j + 1 + 2 = (j + 2) + 1 by omega, pow_succ]
    ring
  unfold dyadicTailThreshold
  rw [log_dyadicTailLevel, he]
  push_cast
  have hnum : (j : ℝ) + 1 + 2 = (j : ℝ) + 3 := by ring
  rw [hnum]
  field_simp

theorem dyadicTailThreshold_zero (A s : ℝ) :
    dyadicTailThreshold A s 0 = 4 * A * sqrt (log 4) * s := by
  unfold dyadicTailThreshold dyadicTailLevel
  norm_num only [Nat.zero_add]
  ring

/-- The number of relevant layers is proportional to the logarithmic size. -/
theorem dyadic_tail_cutoff_bounds {s : ℝ} (hs : 1 ≤ s) :
    (⌈3 * s / log 2⌉₊ : ℝ) ≤ (3 / log 2 + 3) * s ∧
    (⌈3 * s / log 2⌉₊ : ℝ) + 2 ≤ (3 / log 2 + 3) * s ∧
    exp (3 * s) ≤ dyadicTailLevel ⌈3 * s / log 2⌉₊ := by
  have hl : 0 < log 2 := log_pos (by norm_num)
  have harg : 0 ≤ 3 * s / log 2 := by positivity
  have hu := Nat.ceil_lt_add_one harg
  have hle := Nat.le_ceil (3 * s / log 2)
  have hmul := (div_le_iff₀ hl).1 hle
  refine ⟨?_, ?_, ?_⟩
  · have he : 3 * s / log 2 = (3 / log 2) * s := by ring
    conv at hu => rhs; rw [he]
    nlinarith
  · have he : 3 * s / log 2 = (3 / log 2) * s := by ring
    conv at hu => rhs; rw [he]
    nlinarith
  · have h : 3 * s ≤ ((⌈3 * s / log 2⌉₊ : ℝ) + 2) * log 2 := by linarith
    have he := exp_le_exp.2 h
    rw [← log_dyadicTailLevel, exp_log (dyadicTailLevel_pos _)] at he
    exact he

end BretecheTenenbaumMean
