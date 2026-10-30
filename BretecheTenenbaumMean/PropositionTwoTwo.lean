module

public import BretecheTenenbaumMean.UnitWeight

@[expose] public section

/-! # Proposition 2.2: uniform induction on the moment order -/

namespace BretecheTenenbaumMean

/-- Proposition 2.2, with the same admissible penalty choice as Proposition 2.1. -/
theorem propositionTwoTwo : PropositionTwoTwo := by
  obtain ⟨h⟩ := WeightedModel.nonempty_primeEstimates_unitWeight
  refine ⟨(1 : ℝ) / 1000000, by norm_num, ?_⟩
  simpa only [WeightedModel.truncatedMoment_unit] using
    WeightedModel.propositionTwoTwo_for_delta WeightedModel.unitWeight h
      (δ := (1 : ℝ) / 1000000) (by norm_num)

end BretecheTenenbaumMean
