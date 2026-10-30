module

public import BretecheTenenbaumMean.RecursionPrimeAverage
public import BretecheTenenbaumMean.RecursionErrorProducts
public import BretecheTenenbaumMean.LogPowerIntegral

@[expose] public section

/-! # Main and decaying parts of the moment recursion -/

namespace BretecheTenenbaumMean

open Finset Real MeasureTheory

theorem sum_choose_two_pow_half_le (q : ℕ) :
    (∑ j ∈ Icc 1 (q / 2), (q.choose j : ℝ) * 2 ^ j) ≤ 3 ^ q := by
  calc
    _ ≤ ∑ j ∈ range (q + 1), (q.choose j : ℝ) * 2 ^ j := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact mem_range.2 (by have := (mem_Icc.1 hj).2; omega)
      · intro j _ _
        positivity
    _ = (2 + 1 : ℝ) ^ q := by
      rw [add_pow]
      apply sum_congr rfl
      intro j _
      simp only [one_pow, mul_one]
      ring
    _ = _ := by norm_num

end BretecheTenenbaumMean
