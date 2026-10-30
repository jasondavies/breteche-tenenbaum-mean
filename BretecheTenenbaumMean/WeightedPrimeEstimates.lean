module

public import BretecheTenenbaumMean.WeightedEulerEstimates
public import BretecheTenenbaumMean.SmallPrimeFrequency

@[expose] public section

/-! # Explicit prime-sum hypotheses for the weighted upper-bound argument

This structure records analytic estimates that must be proved for the chosen
weight. It contains no assumption about Delta or its moments.
-/

namespace BretecheTenenbaumMean.WeightedModel

open Real Finset

/-- Bounded prime weights and the uniform cosine estimate on the frequency
range used in (2.9)–(2.12). The strict prime cutoff matches the finite model. -/
structure PrimeEstimates (w : MultiplicativeWeight) where
  primeBound : ℝ
  primeBound_nonneg : 0 ≤ primeBound
  prime_le : ∀ p : ℕ, p.Prime → w p ≤ primeBound
  errorBound : ℝ
  errorBound_nonneg : 0 ≤ errorBound
  cosine_error : ∀ x θ : ℝ, 2 ≤ x → |θ| ≤ 2 →
    |cosinePrimeSum w x θ - log (log x / (1 + |θ| * log x))| ≤ errorBound

/-- Frequency zero gives the weighted Mertens estimate needed by the good set. -/
theorem PrimeEstimates.prime_sum_error {w : MultiplicativeWeight} (h : PrimeEstimates w)
    {x : ℝ} (hx : 2 ≤ x) : |primeSum w x - log (log x)| ≤ h.errorBound := by
  simpa only [cosinePrimeSum, primeSum, zero_mul, cos_zero, mul_one, abs_zero,
    zero_add, add_zero, div_one] using h.cosine_error x 0 hx (by norm_num)

/-- The finite prime tail is the difference of two strict-cutoff cosine sums. -/
theorem cosine_tail_eq_sub (w : MultiplicativeWeight) {x y : ℝ} (hyx : y ≤ x) (θ : ℝ) :
    (∑ p ∈ (primesLT x).filter (fun p : ℕ ↦ y ≤ (p : ℝ)), w p * cos (θ * log p) / p) =
      cosinePrimeSum w x θ - cosinePrimeSum w y θ := by
  have hsub := PrimeSums.primesLT_mono hyx
  have he : (primesLT x).filter (fun p : ℕ ↦ y ≤ (p : ℝ)) = primesLT x \ primesLT y := by
    ext p
    simp only [mem_filter, mem_sdiff, mem_primesLT]
    constructor
    · rintro ⟨⟨hp, hpx⟩, hpy⟩
      exact ⟨⟨hp, hpx⟩, fun h ↦ (not_lt_of_ge hpy) h.2⟩
    · rintro ⟨⟨hp, hpx⟩, hy⟩
      exact ⟨⟨hp, hpx⟩, le_of_not_gt (fun hpy ↦ hy ⟨hp, hpy⟩)⟩
  rw [he]
  have hs := sum_sdiff (f := fun p : ℕ ↦ w p * cos (θ * log p) / p) hsub
  change _ + cosinePrimeSum w y θ = cosinePrimeSum w x θ at hs
  linarith

/-- A general nonnegative multiplicative test function is bounded by its
linear prime sum, with only the normalizer's quadratic correction. -/
theorem expectation_multiplicative_le_exp (w : MultiplicativeWeight) (x : ℝ)
    (f : ℕ → ℝ) (hf1 : f 1 = 1)
    (hfm : ∀ m n, m.Coprime n → f (m * n) = f m * f n)
    (hf : ∀ p ∈ primesLT x, 0 ≤ f p) {A : ℝ}
    (hw : ∀ p ∈ primesLT x, w p ≤ A) :
    expectation w x f ≤ exp (A ^ 2 + ∑ p ∈ primesLT x, w p * (f p - 1) / p) := by
  let P := ∏ p ∈ primesLT x, (1 + w p * f p / p)
  have hlocal : ∀ p ∈ primesLT x, 0 < 1 + w p * f p / p := by
    intro p hp
    have hn := div_nonneg (mul_nonneg (w.nonneg p) (hf p hp)) (Nat.cast_nonneg p)
    linarith
  have hP : 0 < P := prod_pos hlocal
  have hlog : log P ≤ ∑ p ∈ primesLT x, w p * f p / p := by
    dsimp only [P]
    rw [log_prod (fun p hp ↦ (hlocal p hp).ne')]
    apply sum_le_sum
    intro p hp
    linarith [log_le_sub_one_of_pos (hlocal p hp)]
  have hnorm := (abs_le.1 (abs_log_normalizer_sub_primeSum_le w hw)).1
  have he : (∑ p ∈ primesLT x, w p * (f p - 1) / p) =
      (∑ p ∈ primesLT x, w p * f p / p) - primeSum w x := by
    simp only [mul_sub, mul_one, sub_div, sum_sub_distrib, primeSum]
  rw [expectation_multiplicative w x f hf1 hfm]
  change P / normalizer w x ≤ _
  rw [← exp_log hP, ← exp_log (normalizer_pos w x), ← exp_sub]
  apply exp_le_exp.2
  rw [he]
  linarith

end BretecheTenenbaumMean.WeightedModel
