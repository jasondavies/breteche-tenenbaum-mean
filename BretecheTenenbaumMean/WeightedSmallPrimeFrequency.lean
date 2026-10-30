module

public import BretecheTenenbaumMean.WeightedPrimeEstimates

@[expose] public section

/-! # Small-prime frequency averages with multiplicative weights -/

namespace BretecheTenenbaumMean.WeightedModel

open Real Finset

/-- The multiplicative average after dividing by the small-prime divisor count. -/
theorem expectation_smallPrimePolynomial (w : MultiplicativeWeight) (x y θ : ℝ) :
    expectation w x (fun n ↦ smallPrimePolynomial n y θ) =
      (∏ p ∈ primesLT x, (1 + w p *
        (if (p : ℝ) < y then (1 + cos (θ * log p)) / 2 else 1 + cos (θ * log p)) / p)) /
      normalizer w x := by
  rw [expectation_multiplicative w x _ (smallPrimePolynomial_one y θ)
    (fun _ _ h ↦ smallPrimePolynomial_mul h y θ)]
  congr 1
  apply prod_congr rfl
  intro p hp
  rw [smallPrimePolynomial_prime (mem_primesLT.1 hp).1]

/-- Small primes have nonpositive contribution after normalization; the
remaining contribution is exactly a strict-cutoff prime cosine tail. -/
theorem smallPrime_linear_sum_le (w : MultiplicativeWeight) (x y θ : ℝ) :
    (∑ p ∈ primesLT x, w p * (smallPrimePolynomial p y θ - 1) / p) ≤
      ∑ p ∈ (primesLT x).filter (fun p : ℕ ↦ y ≤ (p : ℝ)),
        w p * cos (θ * log p) / p := by
  rw [sum_filter]
  apply sum_le_sum
  intro p hp
  rw [smallPrimePolynomial_prime (mem_primesLT.1 hp).1]
  by_cases hpy : (p : ℝ) < y
  · simp only [hpy, ite_true, not_le_of_gt hpy, ite_false]
    apply div_nonpos_of_nonpos_of_nonneg _ (Nat.cast_nonneg _)
    exact mul_nonpos_of_nonneg_of_nonpos (w.nonneg p) (by linarith [cos_le_one (θ * log p)])
  · simp only [hpy, ite_false, le_of_not_gt hpy, ite_true]
    exact le_of_eq (by ring)

/-- The normalized small-prime frequency mean is uniformly bounded. -/
theorem expectation_smallPrimePolynomial_le (w : MultiplicativeWeight) (h : PrimeEstimates w) :
    ∃ C > 0, ∀ x θ : ℝ, 2 ≤ x → 0 < θ → θ ≤ 1 →
      expectation w x (fun n ↦ smallPrimePolynomial n (exp θ⁻¹) θ) ≤ C := by
  refine ⟨exp (h.primeBound ^ 2 + 2 * h.errorBound + log 2), exp_pos _, fun x θ _ hθ hθ1 ↦ ?_⟩
  have he := expectation_multiplicative_le_exp w x
    (fun n ↦ smallPrimePolynomial n (exp θ⁻¹) θ) (smallPrimePolynomial_one _ _)
    (fun _ _ hmn ↦ smallPrimePolynomial_mul hmn _ _)
    (fun p _ ↦ smallPrimePolynomial_nonneg p _ _)
    (fun p hp ↦ h.prime_le p (mem_primesLT.1 hp).1)
  have hs := (smallPrime_linear_sum_le w x (exp θ⁻¹) θ).trans (h.cosine_tail_le x hθ hθ1)
  exact he.trans (exp_le_exp.2 (by linarith))

/-- The pointwise good-set constraint is valid under every nonnegative weight. -/
theorem expectation_goodSet_normalizedPolynomial_le (w : MultiplicativeWeight)
    {δ T x y θ : ℝ} (hT : 0 ≤ T) (hy : 1 ≤ y) :
    expectation w x ((goodSet δ T).indicator (fun n ↦ normalizedPolynomial n θ)) ≤
      (T * log (3 * y) * exp (-penalty δ T y)) *
        expectation w x (fun n ↦ smallPrimePolynomial n y θ) := by
  classical
  let B := T * log (3 * y) * exp (-penalty δ T y)
  have hB : 0 ≤ B := by
    have hl : 0 < log (3 * y) := log_pos (by linarith)
    dsimp only [B]
    positivity
  calc
    _ ≤ expectation w x (fun n ↦ B * smallPrimePolynomial n y θ) := by
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
    _ = _ := expectation_const_mul _ _ _ _

theorem goodSet_frequency_bound (w : MultiplicativeWeight) (h : PrimeEstimates w) :
    ∃ C > 0, ∀ δ T x θ : ℝ, 0 ≤ T → 2 ≤ x → 0 < θ → θ ≤ 1 →
    expectation w x ((goodSet δ T).indicator (fun n ↦ normalizedPolynomial n θ)) ≤
      C * T * log (3 * exp θ⁻¹) * exp (-penalty δ T (exp θ⁻¹)) := by
  obtain ⟨C, hC, hbound⟩ := expectation_smallPrimePolynomial_le w h
  refine ⟨C, hC, fun δ T x θ hT hx hθ hθ1 ↦ ?_⟩
  have hy : 1 ≤ exp θ⁻¹ := (by norm_num : (1 : ℝ) ≤ 2).trans (PrimeSums.two_le_exp_inv hθ hθ1)
  have hl : 0 < log (3 * exp θ⁻¹) := log_pos (by linarith)
  calc
    _ ≤ (T * log (3 * exp θ⁻¹) * exp (-penalty δ T (exp θ⁻¹))) *
        expectation w x (fun n ↦ smallPrimePolynomial n (exp θ⁻¹) θ) :=
      expectation_goodSet_normalizedPolynomial_le w hT hy
    _ ≤ (T * log (3 * exp θ⁻¹) * exp (-penalty δ T (exp θ⁻¹))) * C :=
      mul_le_mul_of_nonneg_left (hbound x θ hx hθ hθ1) (by positivity)
    _ = _ := by ring

end BretecheTenenbaumMean.WeightedModel
