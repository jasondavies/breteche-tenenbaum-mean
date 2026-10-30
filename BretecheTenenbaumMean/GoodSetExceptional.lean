module

public import BretecheTenenbaumMean.GridTail
public import BretecheTenenbaumMean.GaussianGrid

@[expose] public section

/-! # The good-set exceptional probability (2.1) -/

namespace BretecheTenenbaumMean

open Real Finset

/-- The original good-set exception has probability `Oδ(1/T)`, uniformly
in the ambient cutoff. This proves (2.1) for an explicit interval of positive
penalty parameters. -/
theorem goodSet_exceptional_probability_bound {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 1000000) :
    ∃ C > 0, ∀ x T : ℝ, 1 < T → probability x (goodSet δ T)ᶜ ≤ C / T := by
  obtain ⟨A, hA, t₀, ht₀, htail⟩ := grid_divisor_tail_bound
  let B := 3 * exp (δ / 9) * sqrt (π / ((δ / 9) / 2))
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨A * B + exp t₀, by positivity, fun x T hT ↦ ?_⟩
  have hT0 : 0 < T := by linarith
  by_cases ht : t₀ ≤ log T
  · have hgrid : ∀ s : Finset ℕ,
        (∑ j ∈ s, probability (goodSetGrid (j + 1)) {n | gridDivisorThreshold δ T j ≤ tau n}) ≤
          (A * B) / T := by
      intro s
      calc
        _ ≤ ∑ j ∈ s, (A / T) *
            (exp (-(δ / 9) * (sqrt (j + 1 : ℝ) - sqrt (criticalSlope * log T)) ^ 2) /
              sqrt (j + 1 : ℝ)) := by
          apply sum_le_sum
          intro j _
          simpa only [mul_div_assoc] using htail δ T j hδ.le hδ1 hT0 ht
        _ = (A / T) * ∑ j ∈ s,
            exp (-(δ / 9) * (sqrt (j + 1 : ℝ) - sqrt (criticalSlope * log T)) ^ 2) /
              sqrt (j + 1 : ℝ) := by rw [mul_sum]
        _ ≤ (A / T) * B := mul_le_mul_of_nonneg_left
          (sum_gaussian_sqrt_grid_le (by positivity : 0 < δ / 9) _ s) (by positivity)
        _ = _ := by ring
    have h := probability_goodSet_compl_le_of_grid_sum hδ.le (by linarith) hT hgrid x
    exact h.trans (div_le_div_of_nonneg_right (by linarith [exp_pos t₀]) hT0.le)
  · have hTe : T ≤ exp t₀ := by
      calc T = exp (log T) := (exp_log hT0).symm
           _ ≤ exp t₀ := exp_le_exp.2 (le_of_not_ge ht)
    calc _ ≤ 1 := probability_le_one x _
      _ ≤ exp t₀ / T := (le_div_iff₀ hT0).2 (by simpa using hTe)
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [mul_pos hA hB]) hT0.le

end BretecheTenenbaumMean
