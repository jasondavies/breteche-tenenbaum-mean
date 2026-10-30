module

public import BretecheTenenbaumMean.HighFrequencyIntegration
public import BretecheTenenbaumMean.PenaltyIntegral
public import BretecheTenenbaumMean.FrequencyAverage

@[expose] public section

/-! # The high-frequency second moment -/

namespace BretecheTenenbaumMean

open Real MeasureTheory

/-- A continuous integrand has a continuous integral with variable lower endpoint. -/
theorem continuous_tail_integral {f : ℝ → ℝ} (hf : Continuous f) (b : ℝ) :
    Continuous (fun θ ↦ ∫ φ in θ..b, f φ) := by
  have hc : Continuous (fun θ ↦ ∫ φ in b..θ, f φ) :=
    continuous_iff_continuousAt.2 (fun θ ↦ (hf.integral_hasStrictDerivAt b θ).hasDerivAt.continuousAt)
  convert hc.neg using 1
  funext θ
  exact intervalIntegral.integral_symm b θ

/-- For a product integrand, the ordered triangle has exactly half the square's
integral. The proof uses the fundamental theorem of calculus. -/
theorem integral_product_triangle {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    (∫ θ in a..b, f θ * ∫ φ in θ..b, f φ) = (∫ θ in a..b, f θ) ^ 2 / 2 := by
  have hder : ∀ θ ∈ Set.uIcc a b,
      HasDerivAt (fun θ ↦ -(∫ φ in b..θ, f φ) ^ 2 / 2)
        (f θ * ∫ φ in θ..b, f φ) θ := by
    intro θ _
    have h := ((hf.integral_hasStrictDerivAt b θ).hasDerivAt.pow 2).neg.div_const 2
    convert h using 1
    rw [intervalIntegral.integral_symm b θ]
    ring
  have hi := (hf.mul (continuous_tail_integral hf b)).intervalIntegrable (μ := volume) a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hi]
  simp only [intervalIntegral.integral_same, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, neg_zero, zero_div, zero_sub, neg_div, neg_neg]
  rw [intervalIntegral.integral_symm a b]
  ring

end BretecheTenenbaumMean
