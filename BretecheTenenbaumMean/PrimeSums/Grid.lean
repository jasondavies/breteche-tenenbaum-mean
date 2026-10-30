module

public import BretecheTenenbaumMean.GoodSetGrid
public import BretecheTenenbaumMean.PrimeCountTail
public import BretecheTenenbaumMean.PrimeSums.Product

@[expose] public section

/-! # Mertens estimates on the logarithmic grid -/

namespace BretecheTenenbaumMean

open Real Finset PrimeSums

/-- Every grid cutoff used for exceptional events includes the prime two. -/
theorem two_lt_goodSetGrid {j : ℕ} (hj : 1 ≤ j) : 2 < goodSetGrid j := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have he : 2 < exp (j : ℝ) := exp_one_gt_two.trans_le (exp_le_exp.2 hj')
  have h6 : 6 < exp (2 : ℝ) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
    nlinarith [exp_one_gt_d9]
  have h := h6.trans (exp_lt_exp.2 he)
  unfold goodSetGrid
  linarith

/-- Replacing `log log y` by the integer grid coordinate costs a bounded error. -/
theorem loglog_grid_bounds {j : ℕ} (hj : 1 ≤ j) :
    (j : ℝ) - log 2 ≤ log (log (goodSetGrid j)) ∧ log (log (goodSetGrid j)) ≤ j := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h3 : 0 < log 3 := log_pos (by norm_num)
  have he : exp 1 ≤ exp (j : ℝ) := exp_le_exp.2 hj'
  have hhalf : exp (j : ℝ) / 2 ≤ exp (j : ℝ) - log 3 := by
    linarith [exp_one_gt_d9, log_three_lt_d9]
  have hpos : 0 < exp (j : ℝ) / 2 := by positivity
  have hupper : exp (j : ℝ) - log 3 ≤ exp (j : ℝ) := by linarith
  have hlog : log (goodSetGrid j) = exp (j : ℝ) - log 3 := by
    rw [goodSetGrid, log_div (exp_ne_zero _) (by norm_num : (3 : ℝ) ≠ 0), log_exp]
  rw [hlog]
  constructor
  · have h := log_le_log hpos hhalf
    simpa only [log_div (exp_ne_zero _) (by norm_num : (2 : ℝ) ≠ 0), log_exp] using h
  · simpa only [log_exp] using log_le_log (hpos.trans_le hhalf) hupper

end BretecheTenenbaumMean
