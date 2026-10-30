module

public import BretecheTenenbaumMean.UnitWeight

@[expose] public section

/-! # The mean of the maximum in the finite squarefree model -/

namespace BretecheTenenbaumMean

open Real

/-- The final finite-model estimate in §2.4. Transferring it to the ordinary
mean over integers is a separate arithmetic step. -/
theorem hooleyDelta_expectation_bound : ∃ K > 0, ∀ x : ℝ, exp (exp 4) ≤ x →
    expectation x (fun n ↦ (hooleyDelta n : ℝ)) ≤ K * log (log x) ^ (5 / 2 : ℝ) := by
  obtain ⟨h⟩ := WeightedModel.nonempty_primeEstimates_unitWeight
  simpa only [WeightedModel.expectation_unit] using
    WeightedModel.hooleyDelta_expectation_bound WeightedModel.unitWeight h

end BretecheTenenbaumMean
