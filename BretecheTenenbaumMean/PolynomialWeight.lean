module

public import BretecheTenenbaumMean.PolynomialShortSum
public import BretecheTenenbaumMean.WeightedProbability

@[expose] public section

/-! # Polynomial root weights and cancellation of the sieve normalization -/

namespace BretecheTenenbaumMean

open Finset Polynomial Real

/-- Polynomial root counts are a nonnegative multiplicative weight by CRT. -/
noncomputable def polynomialRootWeight (F : ℤ[X]) : MultiplicativeWeight where
  toFun := fun n ↦ (NairTenenbaum.rootCount F n : ℝ)
  nonneg := fun _ ↦ Nat.cast_nonneg _
  map_one := by simp
  map_mul := fun m n h ↦ by
    rw [NairTenenbaum.rootCount_mul F h, Nat.cast_mul]

@[simp] theorem polynomialRootWeight_apply (F : ℤ[X]) (n : ℕ) :
    polynomialRootWeight F n = (NairTenenbaum.rootCount F n : ℝ) := rfl

/-- On squarefree support the weighted numerator is exactly the root-weighted
Hooley sum. No analytic information about root counts is used. -/
theorem squarefree_polynomial_root_sum (F : ℤ[X]) (x : ℝ) :
    (∑ n ∈ smoothSupport x,
      (hooleyDelta n : ℝ) * (NairTenenbaum.rootCount F n : ℝ) / n) =
    WeightedModel.normalizer (polynomialRootWeight F) x *
      WeightedModel.expectation (polynomialRootWeight F) x (fun n ↦ (hooleyDelta n : ℝ)) := by
  unfold WeightedModel.expectation
  rw [mul_div_cancel₀ _ (WeightedModel.normalizer_pos _ _).ne']
  apply sum_congr rfl
  intro n _
  rw [polynomialRootWeight_apply, mul_comm (hooleyDelta n : ℝ)]

/-- The Nair–Tenenbaum sieve product cancels the weighted squarefree
normalizer, even with the weak/strict prime-cutoff discrepancy retained. -/
theorem sieveProduct_mul_weightedNormalizer_le_one_of_cutoff (F : ℤ[X])
    (hF : NairTenenbaum.NoFixedPrimeDivisor F) (x z : ℝ)
    (hsub : primesLT z ⊆ (range (⌊x⌋₊ + 1)).filter Nat.Prime) :
    NairTenenbaum.sieveProduct F x * WeightedModel.normalizer (polynomialRootWeight F) z ≤ 1 := by
  classical
  let P := (range (⌊x⌋₊ + 1)).filter Nat.Prime
  have hw : WeightedModel.normalizer (polynomialRootWeight F) z ≤
      ∏ p ∈ P, (1 + (NairTenenbaum.rootCount F p : ℝ) / p) := by
    unfold WeightedModel.normalizer
    simp only [polynomialRootWeight_apply]
    apply prod_le_prod_of_subset_of_one_le₀ hsub
    · intro p _
      positivity
    · intro p _ _
      have : 0 ≤ (NairTenenbaum.rootCount F p : ℝ) / p := by positivity
      linarith
  calc
    _ ≤ NairTenenbaum.sieveProduct F x *
        ∏ p ∈ P, (1 + (NairTenenbaum.rootCount F p : ℝ) / p) :=
      mul_le_mul_of_nonneg_left hw (NairTenenbaum.sieveProduct_pos hF x).le
    _ = ∏ p ∈ P, ((1 - (NairTenenbaum.rootCount F p : ℝ) / p) *
        (1 + (NairTenenbaum.rootCount F p : ℝ) / p)) := by
      exact (prod_mul_distrib ..).symm
    _ ≤ 1 := by
      apply prod_le_one₀
      · intro p hp
        have hpprime := (mem_filter.1 hp).2
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
        have hr : (NairTenenbaum.rootCount F p : ℝ) / p < 1 :=
          (div_lt_one hp0).2 (by exact_mod_cast hF p hpprime)
        exact mul_nonneg (by linarith) (by positivity)
      · intro p _
        nlinarith [sq_nonneg ((NairTenenbaum.rootCount F p : ℝ) / p)]

/-- The cutoff `floor(x)+1` includes every integer at most `x` while matching
exactly the primes used by the sieve product. -/
theorem sieveProduct_mul_weightedNormalizer_floor_le_one (F : ℤ[X])
    (hF : NairTenenbaum.NoFixedPrimeDivisor F) (x : ℝ) :
    NairTenenbaum.sieveProduct F x *
      WeightedModel.normalizer (polynomialRootWeight F) ((⌊x⌋₊ : ℝ) + 1) ≤ 1 := by
  apply sieveProduct_mul_weightedNormalizer_le_one_of_cutoff F hF
  intro p hp
  obtain ⟨hpprime, hpx⟩ := mem_primesLT.1 hp
  have hpn : p < ⌊x⌋₊ + 1 := by exact_mod_cast hpx
  exact mem_filter.2 ⟨mem_range.2 hpn, hpprime⟩

end BretecheTenenbaumMean
