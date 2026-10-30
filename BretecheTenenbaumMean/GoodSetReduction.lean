module

public import BretecheTenenbaumMean.GoodSetGrid
public import BretecheTenenbaumMean.SmallPrimeDistribution

@[expose] public section

/-! # Reduction of the good-set exception to one-cutoff divisor tails -/

namespace BretecheTenenbaumMean

open Real Finset

/-- The fixed loss from rounding a cutoff upward to the logarithmic grid. -/
noncomputable def gridDivisorThreshold (δ T : ℝ) (j : ℕ) : ℝ :=
  exp (-7) * goodEnvelope δ T (goodSetGrid (j + 1))

theorem gridDivisorThreshold_pos {δ T : ℝ} (hT : 0 < T) (j : ℕ) :
    0 < gridDivisorThreshold δ T j :=
  mul_pos (exp_pos _) (goodEnvelope_pos hT (goodSetGrid_ge_one (by omega)))

/-- Exact formula for the threshold in the Poisson large-deviation variables. -/
theorem gridDivisorThreshold_eq_exp {δ T : ℝ} (hT : 0 < T) (j : ℕ) :
    gridDivisorThreshold δ T j = exp (barrierProfile δ (log T) (j + 1) - 7) := by
  rw [gridDivisorThreshold, goodEnvelope_eq_exp_profile hT (goodSetGrid_ge_one (by omega)),
    loglog_goodSetGrid, ← exp_add]
  push_cast
  congr 1
  ring

theorem log_gridDivisorThreshold {δ T : ℝ} (hT : 0 < T) (j : ℕ) :
    log (gridDivisorThreshold δ T j) = barrierProfile δ (log T) (j + 1) - 7 := by
  rw [gridDivisorThreshold_eq_exp hT, log_exp]

end BretecheTenenbaumMean
