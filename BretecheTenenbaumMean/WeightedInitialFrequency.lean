module

public import BretecheTenenbaumMean.WeightedIntermediateFrequency

@[expose] public section

/-! # The weighted initial-frequency contribution -/

namespace BretecheTenenbaumMean.WeightedModel

open Real MeasureTheory

/-- The uniform one-frequency bound follows from the explicit prime estimates. -/
theorem expectation_normalizedPolynomial_le (w : MultiplicativeWeight) (h : PrimeEstimates w) :
    ∃ C > 0, ∀ x θ : ℝ, 2 ≤ x → 0 ≤ θ → θ ≤ 1 →
      expectation w x (fun n ↦ normalizedPolynomial n θ) ≤ C * (log x / (1 + θ * log x)) := by
  refine ⟨exp (h.primeBound ^ 2 + h.errorBound), exp_pos _, fun x θ hx hθ hθ1 ↦ ?_⟩
  apply expectation_normalizedPolynomial_le_of_cosine w hx hθ
    (fun p hp ↦ h.prime_le p (mem_primesLT.1 hp).1)
  have he := (abs_le.1 (h.cosine_error x θ hx (by rw [abs_of_nonneg hθ]; linarith))).2
  rw [abs_of_nonneg hθ] at he
  linarith

/-- The very low frequencies in §2.2 have bounded mean contribution. -/
theorem initial_frequency_integral_le (w : MultiplicativeWeight) (hp : PrimeEstimates w) : ∃ C > 0, ∀ x b,
    2 ≤ x → 0 ≤ b → b ≤ 1 → b * log x ≤ 1 →
    (∫ θ in (0 : ℝ)..b, expectation w x (fun n ↦ normalizedPolynomial n θ)) ≤ C := by
  obtain ⟨C, hC, h⟩ := expectation_normalizedPolynomial_le w hp
  refine ⟨C, hC, fun x b hx hb hb1 hbL ↦ ?_⟩
  have hl : 0 < log x := log_pos (by linarith)
  have hcont : ContinuousOn (fun θ ↦ C * (log x / (1 + θ * log x))) (Set.uIcc 0 b) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro θ hθ
    rw [Set.uIcc_of_le hb] at hθ
    have : 0 ≤ θ := hθ.1
    positivity
  calc _ ≤ ∫ θ in (0 : ℝ)..b, C * (log x / (1 + θ * log x)) := by
          apply intervalIntegral.integral_mono_on hb
            ((continuous_expectation_normalizedPolynomial w x).intervalIntegrable _ _)
            hcont.intervalIntegrable
          intro θ hθ
          exact h x θ hx hθ.1 (hθ.2.trans hb1)
       _ = C * log (1 + b * log x) := by
          rw [intervalIntegral.integral_const_mul, integral_log_div_one_add hx hb]
       _ ≤ C := by
          have hp : 0 < 1 + b * log x := by positivity
          have hlog := log_le_sub_one_of_pos hp
          nlinarith

/-- The initial frequency interval has a uniform first-moment tail. -/
theorem initial_frequency_probability_bound (w : MultiplicativeWeight) (hp : PrimeEstimates w) : ∃ C > 0, ∀ x b R,
    2 ≤ x → 0 ≤ b → b ≤ 1 → b * log x ≤ 1 → 0 < R →
    probability w x {n | R < frequencyIntegral n 0 b} ≤ C / R := by
  obtain ⟨C, hC, hmean⟩ := initial_frequency_integral_le w hp
  refine ⟨C, hC, fun x b R hx hb hb1 hbL hR ↦ ?_⟩
  have hE : expectation w x (fun n ↦ frequencyIntegral n 0 b) ≤ C := by
    have he := expectation_indicator_frequencyIntegral w x 0 b Set.univ
    simp only [Set.indicator_univ] at he
    rw [he]
    exact hmean x b hx hb hb1 hbL
  exact (probability_gt_le w x _ (fun n _ ↦ frequencyIntegral_nonneg n hb) hR).trans
    (div_le_div_of_nonneg_right hE hR.le)

end BretecheTenenbaumMean.WeightedModel
