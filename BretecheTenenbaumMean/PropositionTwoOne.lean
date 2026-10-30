module

public import BretecheTenenbaumMean.UnitWeight

@[expose] public section

/-! # The upper exceptional-set estimate of Proposition 2.1 -/

namespace BretecheTenenbaumMean

/-- Proposition 2.1, equation (2.4), with constants uniform in `x,T`.
The lower-tail assertion (2.5) is a separate result. -/
theorem propositionTwoOneUpper : PropositionTwoOneUpper := by
  obtain ⟨h⟩ := WeightedModel.nonempty_primeEstimates_unitWeight
  obtain ⟨C, hC, hbound⟩ := WeightedModel.goodSetStar_exceptional_probability_bound
    WeightedModel.unitWeight h (δ := (1 : ℝ) / 1000000) (by norm_num) le_rfl
  refine ⟨(1 : ℝ) / 1000000, by norm_num, C, hC, fun x T hx hT ↦ ?_⟩
  simpa only [WeightedModel.probability_unit] using hbound x T hx (by linarith)

end BretecheTenenbaumMean
