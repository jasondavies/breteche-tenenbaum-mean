module

public import BretecheTenenbaumMean.HighFrequencyMean
public import BretecheTenenbaumMean.EventBounds
public import BretecheTenenbaumMean.IntermediateFrequency

@[expose] public section

/-! # The second-moment tail inside the good set -/

namespace BretecheTenenbaumMean

open Real MeasureTheory

/-- The Fourier majorant splits exactly at any intermediate cutoff. -/
theorem normalized_moment_two_le_frequency_split (n : ℕ) (a : ℝ) :
    moment 2 n / tau n ≤ (π ^ 2 / 2) * (frequencyIntegral n 0 a + frequencyIntegral n a 1) := by
  have he := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_normalizedPolynomial n 0 a) (intervalIntegrable_normalizedPolynomial n a 1)
  unfold frequencyIntegral
  rw [he]
  simpa only [normalizedPolynomial] using normalized_moment_two_le_fourier_integral n

end BretecheTenenbaumMean
