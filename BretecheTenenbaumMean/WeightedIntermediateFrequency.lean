module

public import BretecheTenenbaumMean.WeightedPrimeEstimates
public import BretecheTenenbaumMean.WeightedEventBounds
public import BretecheTenenbaumMean.IntermediateFrequency
public import BretecheTenenbaumMean.Penalty

@[expose] public section

/-! # The weighted intermediate-frequency contribution

The integration starts at zero, giving an upper bound for the paper's interval
starting at `1/log x`. The singular power majorant is integrable for `δ > 0`.
-/

namespace BretecheTenenbaumMean.WeightedModel

open Real Finset MeasureTheory

/-- Finite expectation commutes with the frequency integral after restriction
to a fixed arithmetic set. -/
theorem expectation_indicator_frequencyIntegral (w : MultiplicativeWeight) (x a b : ℝ) (E : Set ℕ) :
    expectation w x (E.indicator (fun n ↦ frequencyIntegral n a b)) =
      ∫ θ in a..b, expectation w x (E.indicator (fun n ↦ normalizedPolynomial n θ)) := by
  classical
  rw [integral_expectation w x a b (fun n θ ↦ E.indicator (fun m ↦ normalizedPolynomial m θ) n)]
  · congr 1
    ext n
    by_cases hn : n ∈ E
    · simp only [Set.indicator_of_mem hn, frequencyIntegral]
    · simp only [Set.indicator_of_notMem hn, intervalIntegral.integral_zero]
  · intro n _
    by_cases hn : n ∈ E
    · simpa only [Set.indicator_of_mem hn] using intervalIntegrable_normalizedPolynomial n a b
    · simp only [Set.indicator_of_notMem hn]
      exact intervalIntegrable_const

end BretecheTenenbaumMean.WeightedModel
