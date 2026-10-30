module

public import BretecheTenenbaumMean.GoodSetExceptional
public import BretecheTenenbaumMean.SecondMomentTail
public import BretecheTenenbaumMean.Targets

@[expose] public section

/-! # The upper exceptional-set estimate of Proposition 2.1 -/

namespace BretecheTenenbaumMean

/-- Proposition 2.1, equation (2.4), with constants uniform in `x,T`.
The lower-tail assertion (2.5) is a separate result. -/
theorem propositionTwoOneUpper : PropositionTwoOneUpper := by
  let δ : ℝ := 1 / 1000000
  have hδ : 0 < δ := by norm_num [δ]
  obtain ⟨C₀, hC₀, hgood⟩ := goodSet_exceptional_probability_bound hδ (le_refl δ)
  obtain ⟨C₁, hC₁, hmoment⟩ := probability_goodSetStar_compl_le hδ
  refine ⟨δ, hδ, C₀ + C₁, by positivity, fun x T hx hT ↦ ?_⟩
  have hT1 : 1 < T := by linarith
  calc
    _ ≤ probability x (goodSet δ T)ᶜ + C₁ / T := hmoment x T hx hT1
    _ ≤ C₀ / T + C₁ / T := add_le_add (hgood x T hT1) le_rfl
    _ = _ := by ring

end BretecheTenenbaumMean
