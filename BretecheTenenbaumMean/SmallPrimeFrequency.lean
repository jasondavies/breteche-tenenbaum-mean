module

public import BretecheTenenbaumMean.SmallPrimePolynomial
public import BretecheTenenbaumMean.FrequencyEstimates

@[expose] public section

/-! # Uniform bound for the small-prime-weighted frequency mean

The factor `τ(n_{exp(1/θ)})` removes the growing low-frequency part. A possible
prime exactly at the cutoff is retained with an explicit bounded error.
-/

namespace BretecheTenenbaumMean

open Real Finset MeasureTheory
open PrimeSums

/-- At most one natural prime can sit exactly at a real cutoff. -/
theorem sum_cutoff_reciprocal_le_one (s : Finset ℕ) {y : ℝ} (hy : 1 ≤ y) :
    (∑ p ∈ s, if (p : ℝ) = y then (p : ℝ)⁻¹ else 0) ≤ 1 := by
  classical
  by_cases h : ∃ p ∈ s, (p : ℝ) = y
  · obtain ⟨p, hp, hpy⟩ := h
    have he : ∀ q : ℕ, (if (q : ℝ) = y then (q : ℝ)⁻¹ else 0) =
        if q = p then (p : ℝ)⁻¹ else 0 := by
      intro q
      by_cases hqp : q = p
      · subst q
        simp only [hpy, ite_true]
      · have hqy : (q : ℝ) ≠ y := by
          intro hqy
          apply hqp
          exact_mod_cast hqy.trans hpy.symm
        simp only [hqy, hqp, ite_false]
    simp_rw [he]
    rw [sum_ite_eq']
    simp only [hp, ite_true, hpy]
    exact inv_le_one_of_one_le₀ hy
  · have he : ∀ p ∈ s, (p : ℝ) ≠ y := by simpa only [not_exists, not_and] using h
    rw [sum_eq_zero (fun p hp ↦ by simp only [he p hp, ite_false])]
    norm_num

/-- Nonnegative weights permit changing a strict upper cutoff to a weak one. -/
theorem sum_primesLT_le_weak (x : ℝ) (w : ℕ → ℝ) (hw : ∀ p, 0 ≤ w p) :
    (∑ p ∈ primesLT x, w p / p) ≤
      ∑ p ∈ range (⌊x⌋₊ + 1), if p.Prime then w p / p else 0 := by
  rw [primesLT, sum_filter]
  apply sum_le_sum
  intro p _
  by_cases hp : p.Prime
  · by_cases hpx : (p : ℝ) < x
    · simp only [hp, hpx, and_self, ite_true, le_refl]
    · simp only [hp, hpx, and_false, ite_false, ite_true]
      exact div_nonneg (hw p) (Nat.cast_nonneg p)
  · simp [hp]

/-- The weighted prime sum is a reciprocal prime sum plus an oscillatory tail,
up to one at the strict small-prime cutoff. No ordering of `x` and `y` is required. -/
theorem sum_smallPrime_weight_le (x θ : ℝ) {y : ℝ} (hy : 1 ≤ y) :
    (∑ p ∈ primesLT x,
      (if (p : ℝ) < y then (1 + cos (θ * log p)) / 2 else 1 + cos (θ * log p)) / p) ≤
      S x + primeInterval y x (fun p ↦ cos (θ * log p)) + 1 := by
  let w : ℕ → ℝ := fun p ↦ if (p : ℝ) < y then (1 + cos (θ * log p)) / 2 else 1 + cos (θ * log p)
  have hw (p : ℕ) : 0 ≤ w p := by
    have := neg_one_le_cos (θ * log p)
    dsimp only [w]
    split_ifs <;> linarith
  have h := sum_primesLT_le_weak x w hw
  have hsum : (∑ p ∈ range (⌊x⌋₊ + 1), if p.Prime then w p / p else 0) ≤
      S x + primeInterval y x (fun p ↦ cos (θ * log p)) +
        ∑ p ∈ range (⌊x⌋₊ + 1), if (p : ℝ) = y then (p : ℝ)⁻¹ else 0 := by
    rw [S_eq_sum, primeInterval_eq_sum_range (by linarith), ← sum_add_distrib, ← sum_add_distrib]
    apply sum_le_sum
    intro p _
    by_cases hp : p.Prime
    · have hc := cos_le_one (θ * log p)
      have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
      rcases lt_trichotomy (p : ℝ) y with hpy | hpy | hpy
      · simp only [hp, hpy, not_lt.mpr hpy.le, ne_of_lt hpy, true_and, ite_true, ite_false, w]
        rw [div_eq_mul_inv]
        nlinarith [mul_nonneg (show 0 ≤ 1 - cos (θ * log p) by linarith) (inv_nonneg.2 hp0.le)]
      · simp only [hp, hpy, lt_self_iff_false, true_and, ite_false, ite_true, w]
        have hy0 : 0 < y := by linarith
        rw [div_eq_mul_inv]
        have hc' := cos_le_one (θ * log y)
        nlinarith [mul_nonneg (show 0 ≤ 1 - cos (θ * log y) by linarith) (inv_nonneg.2 hy0.le)]
      · simp only [hp, hpy, not_lt.mpr hpy.le, ne_of_gt hpy, true_and, ite_true, ite_false, w]
        exact le_of_eq (by ring)
    · simp only [hp, false_and, ite_false, zero_add]
      split_ifs <;> positivity
  exact h.trans (hsum.trans (by linarith [sum_cutoff_reciprocal_le_one (range (⌊x⌋₊ + 1)) hy]))

/-- The weighted Euler product is at most `C log x`, uniformly in the frequency. -/
theorem smallPrime_euler_bound : ∃ C > 0, ∀ x θ,
    2 ≤ x → 0 < θ → θ ≤ 1 →
    (∏ p ∈ primesLT x,
      (1 + (if (p : ℝ) < exp θ⁻¹ then (1 + cos (θ * log p)) / 2
        else 1 + cos (θ * log p)) / p)) ≤ C * log x := by
  obtain ⟨K₁, _, hK₁⟩ := abs_S_sub_loglog_le
  obtain ⟨K₂, hK₂0, hK₂⟩ := primeInterval_cos_tail
  refine ⟨exp (K₁ + K₂ + 1), exp_pos _, fun x θ hx hθ hθ1 ↦ ?_⟩
  have hy := two_le_exp_inv hθ hθ1
  have hl : 0 < log x := log_pos (by linarith)
  let w : ℕ → ℝ := fun p ↦ if (p : ℝ) < exp θ⁻¹ then
    (1 + cos (θ * log p)) / 2 else 1 + cos (θ * log p)
  have hw (p : ℕ) : 0 ≤ w p := by
    have := neg_one_le_cos (θ * log p)
    dsimp only [w]
    split_ifs <;> linarith
  have hp : ∀ p ∈ primesLT x, 0 < 1 + w p / p := fun p _ ↦ by
    have := div_nonneg (hw p) (Nat.cast_nonneg p)
    linarith
  have htail : primeInterval (exp θ⁻¹) x (fun p ↦ cos (θ * log p)) ≤ K₂ := by
    rcases le_total (exp θ⁻¹) x with hyx | hxy
    · exact (abs_le.1 (hK₂ _ _ θ hy hyx hθ (by linarith) (by
        rw [log_exp, mul_inv_cancel₀ hθ.ne']))).2
    · have he : Ioc ⌊exp θ⁻¹⌋₊ ⌊x⌋₊ = ∅ := Ioc_eq_empty_of_le (Nat.floor_mono hxy)
      simpa only [primeInterval, he, sum_empty] using hK₂0
  have hlog : log (∏ p ∈ primesLT x, (1 + w p / p)) ≤ K₁ + K₂ + 1 + log (log x) := by
    rw [log_prod (fun p hp' ↦ (hp p hp').ne')]
    have hterm : ∀ p ∈ primesLT x, log (1 + w p / p) ≤ w p / p := by
      intro p hp'
      have := log_le_sub_one_of_pos (hp p hp')
      linarith
    have hsum := sum_smallPrime_weight_le x θ (y := exp θ⁻¹) (by linarith)
    have hS := (abs_le.1 (hK₁ x hx)).2
    exact (sum_le_sum hterm).trans (by change (∑ p ∈ primesLT x, w p / p) ≤ _; dsimp only [w]; linarith)
  calc _ = exp (log (∏ p ∈ primesLT x, (1 + w p / p))) :=
          (exp_log (prod_pos hp)).symm
       _ ≤ exp (K₁ + K₂ + 1 + log (log x)) := exp_le_exp.2 hlog
       _ = exp (K₁ + K₂ + 1) * log x := by rw [exp_add, exp_log hl]

/-- The uniform multiplicative expectation used for the intermediate frequency
range in §2.2, before applying the good-set inequality. -/
theorem expectation_smallPrimePolynomial_le : ∃ C > 0, ∀ x θ,
    2 ≤ x → 0 < θ → θ ≤ 1 →
    expectation x (fun n ↦ smallPrimePolynomial n (exp θ⁻¹) θ) ≤ C := by
  obtain ⟨C, hC, hprod⟩ := smallPrime_euler_bound
  obtain ⟨c, _, hc, _, hnorm⟩ := normalizer_bounds
  refine ⟨C / c, div_pos hC hc, fun x θ hx hθ hθ1 ↦ ?_⟩
  have hl : 0 < log x := log_pos (by linarith)
  rw [expectation_smallPrimePolynomial]
  calc _ ≤ (C * log x) / (c * log x) :=
          div_le_div₀ (by positivity) (hprod x θ hx hθ hθ1) (mul_pos hc hl) (hnorm x hx).1
       _ = C / c := by field_simp

/-- Applying the defining small-prime constraint of the good set to the
frequency integrand. This step is pointwise before taking finite expectations. -/
theorem expectation_goodSet_normalizedPolynomial_le {δ T x y θ : ℝ}
    (hT : 0 ≤ T) (hy : 1 ≤ y) :
    expectation x ((goodSet δ T).indicator (fun n ↦ normalizedPolynomial n θ)) ≤
      (T * log (3 * y) * exp (-penalty δ T y)) *
        expectation x (fun n ↦ smallPrimePolynomial n y θ) := by
  classical
  let B := T * log (3 * y) * exp (-penalty δ T y)
  have hB : 0 ≤ B := by
    have hl : 0 < log (3 * y) := log_pos (by linarith)
    dsimp only [B]
    positivity
  calc _ ≤ expectation x (fun n ↦ B * smallPrimePolynomial n y θ) := by
          apply expectation_mono
          intro n _
          by_cases hn : n ∈ goodSet δ T
          · rw [Set.indicator_of_mem hn]
            have hτ := tau_pos (smallPrimePart_ne_zero n y)
            have he : normalizedPolynomial n θ = tau (smallPrimePart n y) * smallPrimePolynomial n y θ := by
              rw [smallPrimePolynomial]
              field_simp
            rw [he]
            exact mul_le_mul_of_nonneg_right (hn.2 y hy) (smallPrimePolynomial_nonneg n y θ)
          · rw [Set.indicator_of_notMem hn]
            exact mul_nonneg hB (smallPrimePolynomial_nonneg n y θ)
       _ = _ := expectation_const_mul _ _ _

/-- The good-set frequency estimate with its full penalty retained, used to
bound the intermediate frequency integral in §2.2. -/
theorem goodSet_frequency_bound : ∃ C > 0, ∀ δ T x θ,
    0 ≤ T → 2 ≤ x → 0 < θ → θ ≤ 1 →
    expectation x ((goodSet δ T).indicator (fun n ↦ normalizedPolynomial n θ)) ≤
      C * T * log (3 * exp θ⁻¹) * exp (-penalty δ T (exp θ⁻¹)) := by
  obtain ⟨C, hC, h⟩ := expectation_smallPrimePolynomial_le
  refine ⟨C, hC, fun δ T x θ hT hx hθ hθ1 ↦ ?_⟩
  have hy : 1 ≤ exp θ⁻¹ := (by norm_num : (1 : ℝ) ≤ 2).trans (two_le_exp_inv hθ hθ1)
  have hl : 0 < log (3 * exp θ⁻¹) := log_pos (by linarith)
  calc _ ≤ (T * log (3 * exp θ⁻¹) * exp (-penalty δ T (exp θ⁻¹))) *
          expectation x (fun n ↦ smallPrimePolynomial n (exp θ⁻¹) θ) :=
            expectation_goodSet_normalizedPolynomial_le hT hy
       _ ≤ (T * log (3 * exp θ⁻¹) * exp (-penalty δ T (exp θ⁻¹))) * C :=
            mul_le_mul_of_nonneg_left (h x θ hx hθ hθ1) (by positivity)
       _ = _ := by ring

end BretecheTenenbaumMean
