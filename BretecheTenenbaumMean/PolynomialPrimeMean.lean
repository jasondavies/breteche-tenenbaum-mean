module

public import BretecheTenenbaumMean.WeightedDeltaExpectation
public import BretecheTenenbaumMean.PolynomialMeanTransfer

@[expose] public section

/-! # The polynomial consequence from root-count prime estimates

The weighted probability and moment arguments are now proved. This module gives reusable reductions from the arithmetic prime-estimate
structure. `PolynomialPrimeCosine` proves that input and the unconditional
polynomial consequence.
-/

namespace BretecheTenenbaumMean

open Polynomial NairTenenbaum Real

/-- The prime root-count bound is already available from the polynomial
root bound over the residue field. -/
theorem polynomialRootWeight_prime_le_degree (F : ℤ[X])
    (hF : NoFixedPrimeDivisor F) {p : ℕ} (hp : p.Prime) :
    polynomialRootWeight F p ≤ (F.natDegree : ℝ) := by
  change (rootCount F p : ℝ) ≤ (F.natDegree : ℝ)
  exact_mod_cast rootCount_le_degree hF hp

/-- The arithmetic analytic statement, isolated from the proved bound on
individual prime root counts. The constant may depend on the polynomial. -/
def PolynomialPrimeCosineEstimates : Prop :=
  ∀ F : ℤ[X], Irreducible F → NoFixedPrimeDivisor F →
    ∃ B ≥ (0 : ℝ), ∀ x θ : ℝ, 2 ≤ x → |θ| ≤ 2 →
      |WeightedModel.cosinePrimeSum (polynomialRootWeight F) x θ -
        log (log x / (1 + |θ| * log x))| ≤ B

/-- The arithmetic input: bounded prime root counts and a uniform
cosine prime-sum estimate for each irreducible polynomial without a fixed
prime divisor. No conclusion about Delta or its moments is assumed. -/
def PolynomialPrimeEstimates : Prop :=
  ∀ F : ℤ[X], Irreducible F → NoFixedPrimeDivisor F →
    Nonempty (WeightedModel.PrimeEstimates (polynomialRootWeight F))

/-- A uniform cosine prime-sum estimate constructs the
prime-estimate structure for polynomial root weights. -/
theorem polynomialPrimeEstimates_of_cosine_estimates
    (hcos : PolynomialPrimeCosineEstimates) : PolynomialPrimeEstimates := by
  intro F hI hF
  obtain ⟨B, hB, hbound⟩ := hcos F hI hF
  exact ⟨{
    primeBound := F.natDegree
    primeBound_nonneg := Nat.cast_nonneg _
    prime_le := fun p hp ↦ polynomialRootWeight_prime_le_degree F hF hp
    errorBound := B
    errorBound_nonneg := hB
    cosine_error := hbound }⟩

/-- The full weighted mean follows from the root-count prime estimates. -/
theorem polynomialWeightedExpectationBound_of_prime_estimates
    (hprime : PolynomialPrimeEstimates) : PolynomialWeightedExpectationBound := by
  intro F hI hF
  obtain ⟨hp⟩ := hprime F hI hF
  obtain ⟨A, hA, hmean⟩ := WeightedModel.hooleyDelta_expectation_bound
    (polynomialRootWeight F) hp
  refine ⟨A, hA, exp (exp 4), ?_, hmean⟩
  exact (moment_order_floor_bounds (le_refl (exp (exp 4)))).1

/-- The complete printed polynomial statement, conditional only on the
explicit arithmetic prime estimates. -/
theorem polynomialMeanBound_of_prime_estimates
    (hprime : PolynomialPrimeEstimates) : PolynomialMeanBound :=
  polynomialMeanBound_of_weighted_expectation
    (polynomialWeightedExpectationBound_of_prime_estimates hprime)
/-- Equation (1.7) reduced to the uniform root-count cosine prime sum. -/
theorem polynomialMeanBound_of_prime_cosine_estimates
    (hcos : PolynomialPrimeCosineEstimates) : PolynomialMeanBound :=
  polynomialMeanBound_of_prime_estimates
    (polynomialPrimeEstimates_of_cosine_estimates hcos)


end BretecheTenenbaumMean
