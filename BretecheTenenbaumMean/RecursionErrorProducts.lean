module

public import BretecheTenenbaumMean.SmoothSums
public import BretecheTenenbaumMean.HighFrequencyKernel

@[expose] public section

/-! # Trivial product bounds for the fourth-root recursion error -/

namespace BretecheTenenbaumMean

open Finset Real

/-- Dropping the nonnegative penalty gives the divisor-count envelope. -/
theorem tau_le_goodSet_log {δ T y : ℝ} (hδ : 0 ≤ δ) (hT : 1 ≤ T) (hy : 1 ≤ y)
    {m : ℕ} (hm : m ∈ smoothSupport y) (hE : m ∈ goodSet δ T) :
    tau m ≤ T * log (3 * y) := by
  have h := hE.2 y hy
  rw [smallPrimePart_eq_self (mem_smoothSupport.1 hm).1 (mem_smoothSupport.1 hm).2] at h
  have hp := exp_le_one_iff.2 (neg_nonpos.2 (penalty_nonneg hδ hT hy))
  exact h.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hp (mul_nonneg (by linarith : 0 ≤ T)
      (log_nonneg (by linarith))))

end BretecheTenenbaumMean
