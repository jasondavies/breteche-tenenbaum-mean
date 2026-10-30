module

public import BretecheTenenbaumMean.PrimeCoefficientBounds
public import BretecheTenenbaumMean.PrimeLayers

@[expose] public section

/-! # Two-sided probabilities for fixed prime-count layers -/

namespace BretecheTenenbaumMean

open Real

/-- The Poisson-size estimate for the entire fixed-proportion range of orders. -/
theorem probability_prime_layer_bounds {A : ℝ} (hA : 0 < A) :
    ∃ c > 0, ∃ C > 0, ∃ L₀ > 0, ∀ y : ℝ, 2 ≤ y → L₀ ≤ log (log y) →
    ∀ k : ℕ, (k : ℝ) ≤ A * log (log y) →
      c * (log (log y) ^ k / (log y * (k.factorial : ℝ))) ≤
        probability y {n | n.primeFactors.card = k} ∧
      probability y {n | n.primeFactors.card = k} ≤
        C * (log (log y) ^ k / (log y * (k.factorial : ℝ))) := by
  obtain ⟨c, hc, C, hC, L₀, hL₀, hcoef⟩ := reciprocal_prime_coefficient_bounds hA
  obtain ⟨a, b, ha, hb, hnorm⟩ := PrimeSums.normalizer_bounds
  refine ⟨c / b, by positivity, C / a, by positivity, L₀, hL₀, fun y hy hL k hk ↦ ?_⟩
  have hl : 0 < log y := log_pos (by linarith)
  have hL0 : 0 ≤ log (log y) := hL₀.le.trans hL
  have hfac : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h := hcoef y hy hL k hk
  rw [probability_prime_layer_eq]
  constructor
  · calc
      _ = (c * log (log y) ^ k / (k.factorial : ℝ)) / (b * log y) := by ring
      _ ≤ _ := div_le_div₀ (distinctProductSum_nonneg _ _ _ (fun _ _ ↦ by positivity))
        h.1 (normalizer_pos y) (hnorm y hy).2
  · calc
      _ ≤ (C * log (log y) ^ k / (k.factorial : ℝ)) / (a * log y) :=
        div_le_div₀ (by positivity) h.2 (by positivity) (hnorm y hy).1
      _ = _ := by ring

end BretecheTenenbaumMean
