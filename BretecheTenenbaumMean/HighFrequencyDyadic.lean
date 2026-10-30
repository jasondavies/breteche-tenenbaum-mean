module

public import BretecheTenenbaumMean.DyadicGoodSets
public import BretecheTenenbaumMean.HighFrequencyPrimeBound

@[expose] public section

/-! # The two-frequency estimate on each dyadic good-set layer -/

namespace BretecheTenenbaumMean

open Real Finset PrimeSums

/-- The complete finite-expectation estimate before the two-variable integration.
The exact good-set envelopes and the geometric decay in `j` are retained. -/
theorem high_frequency_dyadic_bound : ∃ C > 0, ∀ δ T x θ φ (j : ℕ),
    0 < T → 0 < θ → θ ≤ φ → φ ≤ 1 → exp θ⁻¹ ≤ x →
    expectation x ((dyadicGoodSet δ T (exp φ⁻¹) j).indicator
      (fun n ↦ normalizedPolynomial n θ * normalizedPolynomial n φ)) ≤
      C * (sqrt (goodEnvelope δ T (exp φ⁻¹) * goodEnvelope δ T (exp θ⁻¹)) /
        sqrt ((2 : ℝ) ^ j)) *
      ((φ / θ) ^ sqrt 2 * (1 + θ * log x) *
        sqrt (φ * log x / (1 + (φ - θ) * log x)) /
        (φ ^ 2 * sqrt (log (3 / φ)) * log x)) := by
  obtain ⟨C, hC, hbound⟩ := high_frequency_layer_bound
  obtain ⟨c, _, hc, _, hnorm⟩ := normalizer_bounds
  refine ⟨C / c, div_pos hC hc, fun δ T x θ φ j hT hθ hθφ hφ1 hx ↦ ?_⟩
  have hφ := hθ.trans_le hθφ
  have hθ1 := hθφ.trans hφ1
  have ha : 1 ≤ exp φ⁻¹ := one_le_exp_iff.2 (inv_nonneg.2 hφ.le)
  have hb : 1 ≤ exp θ⁻¹ := one_le_exp_iff.2 (inv_nonneg.2 hθ.le)
  have hx2 := (two_le_exp_inv hθ hθ1).trans hx
  have hl : 0 < log x := log_pos (by linarith)
  obtain ⟨r, hr⟩ := dyadicGoodSet_expectation_le_layer
    (x := x) (θ := θ) (φ := φ) j hT ha hb
  refine hr.trans ?_
  have hs : 0 ≤ (∑ n ∈ smoothSupport x,
      if (smallPrimePart n (exp φ⁻¹)).primeFactors.card = r
      then twoFrequencyWeight n (exp φ⁻¹) (exp θ⁻¹) θ φ / n else 0) := by
    apply sum_nonneg
    intro n _
    split_ifs
    · exact div_nonneg (twoFrequencyWeight_nonneg n _ _ _ _) (Nat.cast_nonneg n)
    · rfl
  have hdiv := div_le_div₀ (hs.trans (hbound x θ φ r hθ hθφ hφ1 hx))
    (hbound x θ φ r hθ hθφ hφ1 hx)
    (mul_pos hc hl) (hnorm x hx2).1
  have hmul := mul_le_mul_of_nonneg_left hdiv
    (show 0 ≤ sqrt (goodEnvelope δ T (exp φ⁻¹) * goodEnvelope δ T (exp θ⁻¹)) /
      sqrt ((2 : ℝ) ^ j) from div_nonneg (sqrt_nonneg _) (sqrt_nonneg _))
  convert hmul using 1; ring

/-- A uniform comparison of the exact logarithmic envelope with `1/θ`. -/
theorem frequency_log_le {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    log (3 * exp θ⁻¹) ≤ 4 / θ := by
  rw [log_mul (by norm_num : (3 : ℝ) ≠ 0) (exp_ne_zero _), log_exp]
  have h3 := log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
  have hinv : 1 ≤ θ⁻¹ := (one_le_inv₀ hθ).2 hθ1
  rw [div_eq_mul_inv]
  linarith

/-- The envelope coefficient has the form used in the paper, with an explicit
constant absorbing `log (3 exp (1/θ))` rather than replacing it by an equality. -/
theorem frequency_sqrt_envelope_le {δ T θ φ : ℝ} (hT : 0 ≤ T)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    sqrt (goodEnvelope δ T (exp φ⁻¹) * goodEnvelope δ T (exp θ⁻¹)) ≤
      4 * T * exp (-(penalty δ T (exp θ⁻¹) + penalty δ T (exp φ⁻¹)) / 2) /
        sqrt (θ * φ) := by
  let E := exp (-(penalty δ T (exp θ⁻¹) + penalty δ T (exp φ⁻¹)) / 2)
  have hE : 0 < E := exp_pos _
  have hsq : exp (-penalty δ T (exp φ⁻¹)) * exp (-penalty δ T (exp θ⁻¹)) = E ^ 2 := by
    dsimp only [E]
    rw [pow_two, ← exp_add, ← exp_add]
    congr 1
    ring
  have he : goodEnvelope δ T (exp φ⁻¹) * goodEnvelope δ T (exp θ⁻¹) =
      (T * E) ^ 2 * (log (3 * exp φ⁻¹) * log (3 * exp θ⁻¹)) := by
    unfold goodEnvelope
    calc _ = T ^ 2 * (exp (-penalty δ T (exp φ⁻¹)) * exp (-penalty δ T (exp θ⁻¹))) *
        (log (3 * exp φ⁻¹) * log (3 * exp θ⁻¹)) := by ring
      _ = _ := by rw [hsq]; ring
  have hLθ : 0 ≤ log (3 * exp θ⁻¹) := log_nonneg (by
    have := one_le_exp_iff.2 (inv_nonneg.2 hθ.le); linarith)
  have hL := mul_le_mul (frequency_log_le hφ hφ1) (frequency_log_le hθ hθ1)
    hLθ (by positivity : (0 : ℝ) ≤ 4 / φ)
  have hL' : log (3 * exp φ⁻¹) * log (3 * exp θ⁻¹) ≤ 16 / (θ * φ) := by
    convert hL using 1; ring
  have hs : sqrt (log (3 * exp φ⁻¹) * log (3 * exp θ⁻¹)) ≤ 4 / sqrt (θ * φ) := by
    have := sqrt_le_sqrt hL'
    rw [sqrt_div (by norm_num : (0 : ℝ) ≤ 16)] at this
    norm_num at this ⊢
    exact this
  rw [he, sqrt_mul (sq_nonneg _), sqrt_sq (mul_nonneg hT hE.le)]
  calc _ ≤ (T * E) * (4 / sqrt (θ * φ)) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg hT hE.le)
    _ = _ := by ring

/-- The dyadic two-frequency estimate with the full penalty and `2^(-j/2)`
saving, ready for integration on the ordered frequency triangle. -/
theorem high_frequency_dyadic_penalty_bound : ∃ C > 0, ∀ δ T x θ φ (j : ℕ),
    0 < T → 0 < θ → θ ≤ φ → φ ≤ 1 → exp θ⁻¹ ≤ x →
    expectation x ((dyadicGoodSet δ T (exp φ⁻¹) j).indicator
      (fun n ↦ normalizedPolynomial n θ * normalizedPolynomial n φ)) ≤
      C * T * exp (-(penalty δ T (exp θ⁻¹) + penalty δ T (exp φ⁻¹)) / 2) /
        sqrt ((2 : ℝ) ^ j) *
      ((φ / θ) ^ sqrt 2 * (1 + θ * log x) *
        sqrt (φ * log x / (1 + (φ - θ) * log x)) /
        (sqrt (θ * φ) * φ ^ 2 * sqrt (log (3 / φ)) * log x)) := by
  obtain ⟨C, hC, hbound⟩ := high_frequency_dyadic_bound
  refine ⟨4 * C, by positivity, fun δ T x θ φ j hT hθ hθφ hφ1 hx ↦ ?_⟩
  have hφ := hθ.trans_le hθφ
  have hl : 0 < log x := log_pos (by
    have := (two_le_exp_inv hθ (hθφ.trans hφ1)).trans hx; linarith)
  have hlog : 0 < log (3 / φ) := log_pos ((lt_div_iff₀ hφ).2 (by linarith))
  have hcoef := div_le_div_of_nonneg_right
    (frequency_sqrt_envelope_le (δ := δ) hT.le hθ (hθφ.trans hφ1) hφ hφ1)
    (sqrt_nonneg ((2 : ℝ) ^ j))
  refine (hbound δ T x θ φ j hT hθ hθφ hφ1 hx).trans ?_
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef hC.le)
    (show 0 ≤ (φ / θ) ^ sqrt 2 * (1 + θ * log x) *
      sqrt (φ * log x / (1 + (φ - θ) * log x)) /
      (φ ^ 2 * sqrt (log (3 / φ)) * log x) by positivity)
  convert hm using 1; ring

/-- The positive analytic kernel left after good-set extraction. -/
noncomputable def highFrequencyKernel (x θ φ : ℝ) : ℝ :=
  (φ / θ) ^ sqrt 2 * (1 + θ * log x) *
    sqrt (φ * log x / (1 + (φ - θ) * log x)) /
    (sqrt (θ * φ) * φ ^ 2 * sqrt (log (3 / φ)) * log x)

theorem highFrequencyKernel_nonneg {x θ φ : ℝ} (hx : 1 ≤ x) (hθ : 0 ≤ θ)
    (hφ : 0 ≤ φ) : 0 ≤ highFrequencyKernel x θ φ := by
  have hl := log_nonneg hx
  unfold highFrequencyKernel
  positivity

/-- Summing all dyadic layers gives the full good-set two-frequency estimate.
This is uniform in `δ,T,x,θ,φ`; the next analytic step is integration of the kernel. -/
theorem high_frequency_goodSet_bound : ∃ C > 0, ∀ δ T x θ φ,
    0 < T → 0 < θ → θ ≤ φ → φ ≤ 1 → exp θ⁻¹ ≤ x →
    expectation x ((goodSet δ T).indicator
      (fun n ↦ normalizedPolynomial n θ * normalizedPolynomial n φ)) ≤
      C * T * exp (-(penalty δ T (exp θ⁻¹) + penalty δ T (exp φ⁻¹)) / 2) *
        highFrequencyKernel x θ φ := by
  obtain ⟨C, hC, hbound⟩ := high_frequency_dyadic_penalty_bound
  refine ⟨4 * C, by positivity, fun δ T x θ φ hT hθ hθφ hφ1 hx ↦ ?_⟩
  have hφ := hθ.trans_le hθφ
  have hx1 : 1 ≤ x := (one_le_exp_iff.2 (inv_nonneg.2 hθ.le)).trans hx
  have hy : 1 ≤ exp φ⁻¹ := one_le_exp_iff.2 (inv_nonneg.2 hφ.le)
  have hk := highFrequencyKernel_nonneg hx1 hθ.le hφ.le
  let A := C * T * exp (-(penalty δ T (exp θ⁻¹) + penalty δ T (exp φ⁻¹)) / 2) *
    highFrequencyKernel x θ φ
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have h := goodSet_expectation_le_of_dyadic (δ := δ) (T := T) (x := x) hy hA
    (fun n ↦ normalizedPolynomial n θ * normalizedPolynomial n φ) (fun j ↦ ?_)
  · convert h using 1
    dsimp only [A]
    ring
  · convert hbound δ T x θ φ j hT hθ hθφ hφ1 hx using 1
    dsimp only [A, highFrequencyKernel]
    ring

end BretecheTenenbaumMean
