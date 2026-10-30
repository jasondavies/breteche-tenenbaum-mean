module

public import BretecheTenenbaumMean.PrimeWindowAverage
public import BretecheTenenbaumMean.PrimeSmoothing

@[expose] public section

/-! # Prime averaging of the error in the largest-prime recursion -/

namespace BretecheTenenbaumMean

open Finset Real MeasureTheory

theorem mixedRemainder_nonneg (q n p : ℕ) : 0 ≤ mixedRemainder q n p :=
  sum_nonneg (fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (mixedMoment_nonneg _ _ _ _))

end BretecheTenenbaumMean
