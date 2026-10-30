module

public import BretecheTenenbaumMean.ThirdMomentProducts
public import BretecheTenenbaumMean.LogisticIntegral
public import BretecheTenenbaumMean.RecursionKernels

@[expose] public section

/-! # The third-moment base case -/

namespace BretecheTenenbaumMean

open Finset Real MeasureTheory

theorem log_one_add_sqrt_le_two_log {T : ℝ} (hT : 3 ≤ T) :
    log (1 + sqrt T) ≤ 2 * log T := by
  have hT0 : 0 < T := by linarith
  have hs : sqrt T ≤ T := (sqrt_le_left hT0.le).2 (by nlinarith)
  have h := log_le_log (by positivity : 0 < 1 + sqrt T)
    (show 1 + sqrt T ≤ T ^ 2 by nlinarith)
  simpa only [log_pow, Nat.cast_ofNat] using h

end BretecheTenenbaumMean
