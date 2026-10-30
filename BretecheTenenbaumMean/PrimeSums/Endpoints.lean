module

public import BretecheTenenbaumMean.SmallPrimeFrequency

@[expose] public section

/-! # Changing the endpoints of nonnegative prime sums

The analytic estimates use `(a,b]`; the small-prime factorization uses `[a,b)`.
The discrepancy costs at most one bounded prime term.
-/

namespace BretecheTenenbaumMean.PrimeSums

open Real Finset

noncomputable def halfOpenPrimeSum (a b : ℝ) (w : ℕ → ℝ) : ℝ :=
  ∑ p ∈ (primesLT b).filter (fun p : ℕ ↦ a ≤ (p : ℝ)), w p / p

/-- A bounded nonnegative weight permits changing `[a,b)` to `(a,b]` with
an additive error independent of both endpoints. -/
theorem halfOpenPrimeSum_le {a b A : ℝ} (ha : 1 ≤ a) (hA : 0 ≤ A)
    (w : ℕ → ℝ) (hw : ∀ p, 0 ≤ w p) (hwA : ∀ p, w p ≤ A) :
    halfOpenPrimeSum a b w ≤ primeInterval a b w + A := by
  classical
  let v := fun p : ℕ ↦ if a ≤ (p : ℝ) then w p else 0
  have hv : ∀ p, 0 ≤ v p := by
    intro p
    dsimp only [v]
    split_ifs
    · exact hw p
    · exact le_rfl
  have he : halfOpenPrimeSum a b w = ∑ p ∈ primesLT b, v p / p := by
    rw [halfOpenPrimeSum, sum_filter]
    apply sum_congr rfl
    intro p _
    dsimp only [v]
    split_ifs <;> simp only [zero_div]
  rw [he]
  refine (sum_primesLT_le_weak b v hv).trans ?_
  have hsum : (∑ p ∈ range (⌊b⌋₊ + 1), if p.Prime then v p / p else 0) ≤
      primeInterval a b w + A * (∑ p ∈ range (⌊b⌋₊ + 1), if (p : ℝ) = a then (p : ℝ)⁻¹ else 0) := by
    rw [primeInterval_eq_sum_range (by linarith), mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro p _
    by_cases hp : p.Prime
    · have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
      rcases lt_trichotomy (p : ℝ) a with hpa | hpa | hpa
      · simp only [hp, true_and, not_le.mpr hpa, not_lt.mpr hpa.le, ne_of_lt hpa,
          v, ite_true, ite_false, zero_div, mul_zero, zero_add, le_refl]
      · simp only [hp, true_and, hpa, v, le_refl, lt_self_iff_false, ite_true, ite_false, zero_add]
        have h := mul_le_mul_of_nonneg_right (hwA p) (inv_nonneg.2 hp0)
        simpa only [div_eq_mul_inv, hpa] using h
      · simp only [hp, true_and, hpa.le, hpa, ne_of_gt hpa, v, ite_true, ite_false,
          mul_zero, add_zero, le_refl]
    · simp only [hp, false_and, ite_false, zero_add]
      split_ifs <;> positivity
  have hend := sum_cutoff_reciprocal_le_one (range (⌊b⌋₊ + 1)) ha
  refine hsum.trans ?_
  have h := mul_le_mul_of_nonneg_left hend hA
  linarith

/-- The middle-range sum in the exact strict-cutoff convention. -/
theorem halfOpen_U2 : ∃ K ≥ 0, ∀ θ φ,
    0 < θ → θ ≤ φ → φ ≤ 1 →
    halfOpenPrimeSum (exp φ⁻¹) (exp θ⁻¹) (fun p ↦ 1 + cos (φ * log p)) ≤
      log (φ / θ) + K := by
  obtain ⟨K, hK0, hK⟩ := primeSum_U2
  refine ⟨K + 2, by positivity, fun θ φ hθ hθφ hφ1 ↦ ?_⟩
  have hy := two_le_exp_inv (hθ.trans_le hθφ) hφ1
  have h := halfOpenPrimeSum_le (b := exp θ⁻¹) (by linarith : 1 ≤ exp φ⁻¹)
    (by norm_num : (0 : ℝ) ≤ 2) (fun p ↦ 1 + cos (φ * log p))
    (fun p ↦ by linarith [neg_one_le_cos (φ * log p)])
    (fun p ↦ by linarith [cos_le_one (φ * log p)])
  have h' := hK θ φ hθ hθφ hφ1
  linarith

/-- The large-prime sum in the exact strict-cutoff convention. -/
theorem halfOpen_U3 : ∃ K ≥ 0, ∀ x θ φ,
    0 < θ → θ ≤ φ → φ ≤ 1 → exp θ⁻¹ ≤ x →
    halfOpenPrimeSum (exp θ⁻¹) x
      (fun p ↦ (1 + cos (θ * log p)) * (1 + cos (φ * log p))) ≤
      log (1 + θ * log x) + (1 / 2) * log (φ * log x / (1 + (φ - θ) * log x)) + K := by
  obtain ⟨K, hK0, hK⟩ := primeSum_U3
  refine ⟨K + 4, by positivity, fun x θ φ hθ hθφ hφ1 hx ↦ ?_⟩
  have hy := two_le_exp_inv hθ (hθφ.trans hφ1)
  have h := halfOpenPrimeSum_le (b := x) (by linarith : 1 ≤ exp θ⁻¹)
    (by norm_num : (0 : ℝ) ≤ 4)
    (fun p ↦ (1 + cos (θ * log p)) * (1 + cos (φ * log p)))
    (fun p ↦ mul_nonneg (by linarith [neg_one_le_cos (θ * log p)])
      (by linarith [neg_one_le_cos (φ * log p)]))
    (fun p ↦ by
      have hθ0 : 0 ≤ 1 + cos (θ * log p) := by linarith [neg_one_le_cos (θ * log p)]
      have hφ0 : 0 ≤ 1 + cos (φ * log p) := by linarith [neg_one_le_cos (φ * log p)]
      have hθ2 : 1 + cos (θ * log p) ≤ 2 := by linarith [cos_le_one (θ * log p)]
      have hφ2 : 1 + cos (φ * log p) ≤ 2 := by linarith [cos_le_one (φ * log p)]
      nlinarith [mul_le_mul hθ2 hφ2 hφ0 (by norm_num : (0 : ℝ) ≤ 2)])
  have h' := hK x θ φ hθ hθφ hφ1 hx
  linarith

end BretecheTenenbaumMean.PrimeSums
