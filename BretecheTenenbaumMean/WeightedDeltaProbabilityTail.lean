module

public import BretecheTenenbaumMean.AllMomentMaximum
public import BretecheTenenbaumMean.WeightedAllMomentGoodSet

@[expose] public section

/-! # The weighted tail bound for the Delta function -/

namespace BretecheTenenbaumMean.WeightedModel

open Finset Real

theorem hooleyDelta_probability_tail_bound (w : MultiplicativeWeight) (hpw : PrimeEstimates w) : ∃ A > 0, ∃ C > 0, ∀ x T : ℝ,
    exp (exp 4) ≤ x → 3 ≤ T →
    probability w x {n | A * T * sqrt (log T) * log (log x) < (hooleyDelta n : ℝ)} ≤ C / T := by
  let δ : ℝ := 1 / 1000000
  have hδ : 0 < δ := by norm_num [δ]
  obtain ⟨C₀, hC₀, C, hC, hgood⟩ := allMomentGoodSet_probability_bound w hpw hδ (le_refl δ)
  obtain ⟨A, hA, hmax⟩ := allMomentGoodSet_max_bound hδ.le hC₀
  refine ⟨A, hA, C, hC, fun x T hx hT ↦ ?_⟩
  have hx2 : 2 ≤ x := by have h := (moment_order_floor_bounds hx).1; linarith
  calc
    _ ≤ probability w x (allMomentGoodSet δ T (explicitThreshold C₀ T))ᶜ := by
      apply probability_mono_on_support w
      intro n hn hlarge hE
      have h := hmax x T hx hT n hn hE
      exact (not_lt_of_ge h) hlarge
    _ ≤ _ := hgood x T hx2 hT


end BretecheTenenbaumMean.WeightedModel
