module

public import BretecheTenenbaumMean.WeightedTwoFrequency
public import BretecheTenenbaumMean.WeightedPrimeIntervals
public import BretecheTenenbaumMean.HighFrequencyPrimeBound
public import BretecheTenenbaumMean.PrimeSums.Endpoints

@[expose] public section

/-! # Weighted prime-sum bounds for the high-frequency majorant -/

namespace BretecheTenenbaumMean.WeightedModel

open Real Finset


/-- The logarithm of the remaining Euler product splits into the middle and
large prime sums, with no endpoint term omitted. -/
theorem threeRangeWeight_sum_eq (w : MultiplicativeWeight) (x a b θ φ : ℝ) (hab : a ≤ b) (hbx : b ≤ x) :
    (∑ p ∈ primesLT x \ (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < a),
      w p * threeRangeWeight p a b θ φ / p) =
      sqrt 2 * halfOpenPrimeSum w a b (fun p ↦ 1 + cos (φ * log p)) +
        halfOpenPrimeSum w b x (fun p ↦ (1 + cos (θ * log p)) * (1 + cos (φ * log p))) := by
  have he : primesLT x \ (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < a) =
      (primesLT x).filter (fun p : ℕ ↦ a ≤ (p : ℝ)) := by
    ext p
    simp only [mem_sdiff, mem_filter]
    by_cases hp : p ∈ primesLT x <;> simp [hp, not_lt]
  rw [he, halfOpenPrimeSum, halfOpenPrimeSum, ← filter_primesLT_of_le hbx]
  simp_rw [sum_filter]
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  by_cases hpa : (p : ℝ) < a
  · have hpb : (p : ℝ) < b := hpa.trans_le hab
    simp only [hpb, not_le.mpr hpa, not_le.mpr hpb, ite_false, ite_true, mul_zero, zero_add]
  · have hpa' : a ≤ (p : ℝ) := not_lt.1 hpa
    by_cases hpb : (p : ℝ) < b
    · simp only [hpa', hpa, hpb, not_le.mpr hpb, ite_true, ite_false, threeRangeWeight, add_zero]
      ring
    · have hpb' : b ≤ (p : ℝ) := not_lt.1 hpb
      simp only [hpa', hpa, hpb', hpb, ite_true, ite_false, threeRangeWeight, mul_zero, zero_add]

/-- The two oscillatory prime ranges have the logarithmic upper bound required
in the high-frequency integrand estimate. -/
theorem high_frequency_remaining_prime_sum (w : MultiplicativeWeight) (hp : PrimeEstimates w) : ∃ K ≥ 0, ∀ x θ φ,
    0 < θ → θ ≤ φ → φ ≤ 1 → exp θ⁻¹ ≤ x →
    (∑ p ∈ primesLT x \ (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < exp φ⁻¹),
      w p * threeRangeWeight p (exp φ⁻¹) (exp θ⁻¹) θ φ / p) ≤
      sqrt 2 * log (φ / θ) + log (1 + θ * log x) +
        (1 / 2) * log (φ * log x / (1 + (φ - θ) * log x)) + K := by
  obtain ⟨K₂, hK₂0, hK₂⟩ := hp.halfOpen_U2
  obtain ⟨K₃, hK₃0, hK₃⟩ := hp.halfOpen_U3
  refine ⟨sqrt 2 * K₂ + K₃, by positivity, fun x θ φ hθ hθφ hφ1 hx ↦ ?_⟩
  have hab : exp φ⁻¹ ≤ exp θ⁻¹ := exp_le_exp.2 (inv_anti₀ hθ hθφ)
  rw [threeRangeWeight_sum_eq w _ _ _ _ _ hab hx]
  have h2 := mul_le_mul_of_nonneg_left (hK₂ θ φ hθ hθφ hφ1) (sqrt_nonneg (2 : ℝ))
  have h3 := hK₃ x θ φ hθ hθφ hφ1 hx
  linarith

/-- Converting the small-prime square-root saving to the frequency variable.
Both sides of Mertens' estimate are used, so a small reciprocal sum is not
silently substituted for a larger logarithmic denominator. -/
theorem small_prime_prefactor_bound (w : MultiplicativeWeight) (hp : PrimeEstimates w) : ∃ C > 0, ∀ φ,
    0 < φ → φ ≤ 1 →
    8 * exp (2 * primeSum w (exp φ⁻¹)) / sqrt (1 + 2 * primeSum w (exp φ⁻¹)) ≤
      C / (φ ^ 2 * sqrt (log (3 / φ))) := by
  let K := hp.errorBound
  have hK0 : 0 ≤ K := hp.errorBound_nonneg
  have hK (x : ℝ) (hx : 2 ≤ x) : |primeSum w x - log (log x)| ≤ K := hp.prime_sum_error hx
  let D := K + log 3 + 1
  have h3 : 0 < log 3 := log_pos (by norm_num)
  have hD : 0 < D := by dsimp only [D]; linarith
  refine ⟨8 * exp (2 * K) * sqrt D, by positivity, fun φ hφ hφ1 ↦ ?_⟩
  let L := primeSum w (exp φ⁻¹)
  have hL : 0 ≤ L := sum_nonneg (fun p _ ↦ div_nonneg (w.nonneg p) (Nat.cast_nonneg _))
  have hM := abs_le.1 (hK (exp φ⁻¹) (PrimeSums.two_le_exp_inv hφ hφ1))
  rw [log_exp, log_inv] at hM
  change -K ≤ L - -log φ ∧ L - -log φ ≤ K at hM
  have hlog : 0 < log (3 / φ) := log_pos ((lt_div_iff₀ hφ).2 (by linarith))
  have hden : 0 < sqrt (1 + 2 * L) := sqrt_pos.2 (by linarith)
  have hden' : 0 < sqrt (log (3 / φ)) := sqrt_pos.2 hlog
  have hcmp : log (3 / φ) ≤ D * (1 + 2 * L) := by
    rw [log_div (by norm_num : (3 : ℝ) ≠ 0) hφ.ne']
    dsimp only [D]
    nlinarith [mul_nonneg hK0 hL, mul_nonneg h3.le hL]
  have hs := sqrt_le_sqrt hcmp
  rw [sqrt_mul hD.le] at hs
  have hrec : (sqrt (1 + 2 * L))⁻¹ ≤ sqrt D / sqrt (log (3 / φ)) := by
    rw [inv_eq_one_div, div_le_div_iff₀ hden hden']
    simpa only [one_mul] using hs
  have hexp : exp (2 * L) ≤ exp (2 * K) / φ ^ 2 := by
    calc exp (2 * L) ≤ exp (2 * K - 2 * log φ) := exp_le_exp.2 (by linarith [hM.2])
         _ = exp (2 * K) / φ ^ 2 := by
            rw [exp_sub, show (2 : ℝ) * log φ = (2 : ℕ) * log φ by norm_num,
              exp_nat_mul, exp_log hφ]
  change 8 * exp (2 * L) / sqrt (1 + 2 * L) ≤ _
  calc 8 * exp (2 * L) / sqrt (1 + 2 * L)
      ≤ (8 * (exp (2 * K) / φ ^ 2)) * (sqrt D / sqrt (log (3 / φ))) := by
          rw [div_eq_mul_inv]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hexp (by norm_num)) hrec
            (inv_nonneg.2 hden.le) (by positivity)
    _ = (8 * exp (2 * K) * sqrt D) / (φ ^ 2 * sqrt (log (3 / φ))) := by ring

/-- The three-range bound in frequency variables, uniformly in the fixed layer
index. This is the estimate for `G` preceding the two-variable integration in §2.2. -/
theorem high_frequency_layer_bound (w : MultiplicativeWeight) (hp : PrimeEstimates w) : ∃ C > 0, ∀ x θ φ (r : ℕ),
    0 < θ → θ ≤ φ → φ ≤ 1 → exp θ⁻¹ ≤ x →
    (∑ n ∈ smoothSupport x, if (smallPrimePart n (exp φ⁻¹)).primeFactors.card = r
      then w n * twoFrequencyWeight n (exp φ⁻¹) (exp θ⁻¹) θ φ / n else 0) ≤
      C * ((φ / θ) ^ sqrt 2 * (1 + θ * log x) *
        sqrt (φ * log x / (1 + (φ - θ) * log x)) / (φ ^ 2 * sqrt (log (3 / φ)))) := by
  obtain ⟨C, hC, hsmall⟩ := small_prime_prefactor_bound w hp
  obtain ⟨K, _, hremaining⟩ := high_frequency_remaining_prime_sum w hp
  refine ⟨C * exp K, mul_pos hC (exp_pos K), fun x θ φ r hθ hθφ hφ1 hx ↦ ?_⟩
  have hφ : 0 < φ := hθ.trans_le hθφ
  have hab : exp φ⁻¹ ≤ exp θ⁻¹ := exp_le_exp.2 (inv_anti₀ hθ hθφ)
  have hax := hab.trans hx
  have hx2 := (PrimeSums.two_le_exp_inv hθ (hθφ.trans hφ1)).trans hx
  have hl : 0 < log x := log_pos (by linarith)
  have hratio : 0 < φ / θ := div_pos hφ hθ
  have hd : 0 < 1 + θ * log x := by positivity
  have hd' : 0 < 1 + (φ - θ) * log x := by
    have : 0 ≤ φ - θ := sub_nonneg.2 hθφ
    positivity
  have hq : 0 < φ * log x / (1 + (φ - θ) * log x) := div_pos (mul_pos hφ hl) hd'
  have hlog : 0 < log (3 / φ) := log_pos ((lt_div_iff₀ hφ).2 (by linarith))
  let R := ∑ p ∈ primesLT x \ (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < exp φ⁻¹),
    w p * threeRangeWeight p (exp φ⁻¹) (exp θ⁻¹) θ φ / p
  have hR := hremaining x θ φ hθ hθφ hφ1 hx
  have he1 : exp (sqrt 2 * log (φ / θ)) = (φ / θ) ^ sqrt 2 := by
    rw [rpow_def_of_pos hratio]
    congr 1
    ring
  have he2 : exp ((1 / 2) * log (φ * log x / (1 + (φ - θ) * log x))) =
      sqrt (φ * log x / (1 + (φ - θ) * log x)) := by
    rw [sqrt_eq_rpow, rpow_def_of_pos hq]
    congr 1
    ring
  have hER : exp R ≤ exp K * ((φ / θ) ^ sqrt 2 * (1 + θ * log x) *
      sqrt (φ * log x / (1 + (φ - θ) * log x))) := by
    calc exp R ≤ exp (sqrt 2 * log (φ / θ) + log (1 + θ * log x) +
        (1 / 2) * log (φ * log x / (1 + (φ - θ) * log x)) + K) := exp_le_exp.2 hR
      _ = _ := by rw [exp_add, exp_add, exp_add, he1, he2, exp_log hd]; ring
  have hlow : (∑ p ∈ (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < exp φ⁻¹), w p / p) =
      primeSum w (exp φ⁻¹) := by rw [filter_primesLT_of_le hax]; rfl
  have hbase := twoFrequency_layer_uniform w x (exp φ⁻¹) (exp θ⁻¹) θ φ r hab
  rw [hlow] at hbase
  refine hbase.trans ?_
  calc (8 * exp (2 * primeSum w (exp φ⁻¹)) / sqrt (1 + 2 * primeSum w (exp φ⁻¹))) * exp R
      ≤ (C / (φ ^ 2 * sqrt (log (3 / φ)))) *
        (exp K * ((φ / θ) ^ sqrt 2 * (1 + θ * log x) *
          sqrt (φ * log x / (1 + (φ - θ) * log x)))) :=
            mul_le_mul (hsmall φ hφ hφ1) hER (exp_pos R).le (by positivity)
    _ = _ := by ring

end BretecheTenenbaumMean.WeightedModel
