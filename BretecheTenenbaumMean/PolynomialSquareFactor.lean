module

public import BretecheTenenbaumMean.PolynomialWeight
public import BretecheTenenbaumMean.DivisorPowerSums
public import BretecheTenenbaumMean.SquarefreeTransfer

@[expose] public section

/-! # Removing square factors from polynomial root weights

A uniform bound on prime-power root counts gives a divisor-power weight for
the square part. Vanishing prime root counts are retained; this is essential
when the square part and the squarefree part have common prime factors.
-/

namespace BretecheTenenbaumMean

open Finset Polynomial Real

/-- Multiplicativity over any finite set containing the prime factors. -/
theorem rootCount_eq_prod (F : ℤ[X]) {n : ℕ} (hn : n ≠ 0) (S : Finset ℕ)
    (hS : n.primeFactors ⊆ S) :
    NairTenenbaum.rootCount F n =
      ∏ p ∈ S, NairTenenbaum.rootCount F (p ^ n.factorization p) := by
  rw [Nat.multiplicative_factorization (NairTenenbaum.rootCount F)
    (fun _ _ h ↦ NairTenenbaum.rootCount_mul F h) (by simp) hn]
  exact Finsupp.prod_of_support_subset _ (by simpa only [Nat.support_factorization] using hS)
    _ (by simp)

/-- Enlarging the divisor-count product adds only factors equal to one. -/
theorem card_divisors_eq_prod (n : ℕ) (hn : n ≠ 0) (S : Finset ℕ)
    (hS : n.primeFactors ⊆ S) :
    n.divisors.card = ∏ p ∈ S, (n.factorization p + 1) := by
  rw [Nat.card_divisors hn]
  apply prod_subset hS
  intro p _ hp
  have hz : n.factorization p = 0 := by
    apply Finsupp.notMem_support_iff.1
    simpa only [Nat.support_factorization] using hp
  simp [hz]

/-- Local root counts can be charged to the square part even when it shares
primes with the squarefree part. -/
theorem rootCount_squareFactor_le (F : ℤ[X]) (k : ℕ)
    (hroot : ∀ p : ℕ, p.Prime → ∀ ν : ℕ, NairTenenbaum.rootCount F (p ^ ν) ≤ 2 ^ k)
    {b a : ℕ} (hb : b ≠ 0) (ha : Squarefree a) :
    NairTenenbaum.rootCount F (b ^ 2 * a) ≤ b.divisors.card ^ k * NairTenenbaum.rootCount F a := by
  classical
  let S := b.primeFactors ∪ a.primeFactors
  have ha0 := ha.ne_zero
  have hn0 : b ^ 2 * a ≠ 0 := mul_ne_zero (pow_ne_zero _ hb) ha0
  have hS : (b ^ 2 * a).primeFactors ⊆ S := by
    rw [Nat.primeFactors_mul (pow_ne_zero _ hb) ha0, Nat.primeFactors_pow b (by norm_num : 2 ≠ 0)]
  rw [rootCount_eq_prod F hn0 S hS,
    rootCount_eq_prod F ha0 S subset_union_right,
    card_divisors_eq_prod b hb S subset_union_left, ← prod_pow, ← prod_mul_distrib]
  apply prod_le_prod
  intro p hp
  have hpprime : p.Prime := by
    rcases mem_union.1 hp with h | h <;> exact Nat.prime_of_mem_primeFactors h
  have hv : (b ^ 2 * a).factorization p = 2 * b.factorization p + a.factorization p := by
    simp [Nat.factorization_mul (pow_ne_zero _ hb) ha0, Nat.factorization_pow]
  rw [hv]
  by_cases hbp : b.factorization p = 0
  · simp [hbp]
  · have hB : 2 ^ k ≤ (b.factorization p + 1) ^ k :=
      Nat.pow_le_pow_left (by omega) k
    have hlocal := hroot p hpprime (2 * b.factorization p + a.factorization p)
    have hav := ha.natFactorization_le_one p
    by_cases hap : a.factorization p = 0
    · simpa [hap] using hlocal.trans hB
    · have hap1 : a.factorization p = 1 := by omega
      rw [hap1, pow_one]
      by_cases hz : NairTenenbaum.rootCount F p = 0
      · rw [NairTenenbaum.rootCount_eq_zero_of_dvd hpprime.ne_zero
          (dvd_pow_self p (by omega : 2 * b.factorization p + 1 ≠ 0)) hz, hz, mul_zero]
      · have hρ : 1 ≤ NairTenenbaum.rootCount F p := by omega
        calc
          _ ≤ 2 ^ k := by simpa only [hap1] using hlocal
          _ ≤ (b.factorization p + 1) ^ k := hB
          _ = (b.factorization p + 1) ^ k * 1 := (mul_one _).symm
          _ ≤ _ := Nat.mul_le_mul_left _ hρ

/-- A fixed prime-power root bound makes the complete harmonic root sum
at most a constant times its squarefree counterpart. -/
theorem polynomialRootSum_le_squarefree_cutoff (F : ℤ[X]) (k : ℕ)
    (hroot : ∀ p : ℕ, p.Prime → ∀ ν : ℕ, NairTenenbaum.rootCount F (p ^ ν) ≤ 2 ^ k)
    {x z : ℝ} (hz : (⌊x⌋₊ : ℝ) < z) :
    polynomialDeltaRootSum F x ≤
      (∑ a ∈ smoothSupport z,
        (hooleyDelta a : ℝ) * (NairTenenbaum.rootCount F a : ℝ) / a) *
      (π ^ 2 / 6) ^ (2 ^ (k + 2)) := by
  have hmul (b a : ℕ) (hb : b ≠ 0) (ha : Squarefree a) :
      (hooleyDelta (b ^ 2 * a) : ℝ) * NairTenenbaum.rootCount F (b ^ 2 * a) ≤
        tau b ^ (k + 2) * ((hooleyDelta a : ℝ) * NairTenenbaum.rootCount F a) := by
    have hρ : (NairTenenbaum.rootCount F (b ^ 2 * a) : ℝ) ≤
        tau b ^ k * (NairTenenbaum.rootCount F a : ℝ) := by
      have hr := rootCount_squareFactor_le F k hroot hb ha
      change (_ : ℝ) ≤ (b.divisors.card : ℝ) ^ k * _
      exact_mod_cast hr
    have htb : 0 ≤ tau b := Nat.cast_nonneg _
    have htb2 : 0 ≤ tau (b ^ 2) := Nat.cast_nonneg _
    have hΔ := hooleyDelta_mul_le_tau (b ^ 2) a
    have ht : tau (b ^ 2) ≤ tau b ^ 2 := by
      simpa only [pow_two] using tau_mul_le b b
    calc
      _ ≤ (tau (b ^ 2) * (hooleyDelta a : ℝ)) *
          (tau b ^ k * (NairTenenbaum.rootCount F a : ℝ)) :=
        mul_le_mul hΔ hρ (Nat.cast_nonneg _) (by positivity)
      _ ≤ (tau b ^ 2 * (hooleyDelta a : ℝ)) *
          (tau b ^ k * (NairTenenbaum.rootCount F a : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg _)) (by positivity)
      _ = _ := by rw [pow_add]; ring
  have h := harmonic_squareFactor_bound_cutoff
    (fun n ↦ (hooleyDelta n : ℝ) * (NairTenenbaum.rootCount F n : ℝ))
    (fun b ↦ tau b ^ (k + 2)) (fun _ ↦ by positivity)
    (fun b ↦ pow_nonneg (show 0 ≤ tau b from Nat.cast_nonneg _) _)
    hmul (fun N ↦ sum_tau_pow_div_sq_le (k + 1) N) hz
  have he : Ioc 0 ⌊x⌋₊ = Icc 1 ⌊x⌋₊ := by
    ext n
    simp only [mem_Ioc, mem_Icc]
    omega
  simpa only [polynomialDeltaRootSum, he, Nat.add_assoc] using h

/-- Irreducibility and the absence of a fixed prime divisor supply the local
prime-power bound unconditionally through the discriminant estimates. -/
theorem exists_rootCount_prime_power_bound (F : ℤ[X])
    (hF : NairTenenbaum.NoFixedPrimeDivisor F) (hI : Irreducible F) :
    ∃ k : ℕ, ∀ p : ℕ, p.Prime → ∀ ν : ℕ,
      NairTenenbaum.rootCount F (p ^ ν) ≤ 2 ^ k := by
  let P : NairTenenbaum.PolynomialSystem 1 1 :=
    NairTenenbaum.PolynomialSystem.ofIrreducible (fun _ ↦ F)
      (fun _ ↦ hF.irreducible_map hI)
      (fun i j hij ↦ (hij (Subsingleton.elim i j)).elim)
      (by simpa using hF)
  let k := max F.natDegree (P.badDiscriminant ^ 3)
  refine ⟨k, fun p hp ν ↦ ?_⟩
  have h : NairTenenbaum.rootCount F (p ^ ν) ≤ k :=
    P.factor_rootCount_prime_pow_uniform hp ν 0
  exact h.trans Nat.lt_two_pow_self.le

/-- The complete root-weighted harmonic sum, after its sieve factor, is
controlled by the weighted finite-model expectation. -/
theorem sieved_polynomialRootSum_le_expectation (F : ℤ[X])
    (hF : NairTenenbaum.NoFixedPrimeDivisor F) (k : ℕ)
    (hroot : ∀ p : ℕ, p.Prime → ∀ ν : ℕ, NairTenenbaum.rootCount F (p ^ ν) ≤ 2 ^ k)
    (x : ℝ) :
    NairTenenbaum.sieveProduct F x * polynomialDeltaRootSum F x ≤
      (π ^ 2 / 6) ^ (2 ^ (k + 2)) *
        WeightedModel.expectation (polynomialRootWeight F) ((⌊x⌋₊ : ℝ) + 1)
          (fun n ↦ (hooleyDelta n : ℝ)) := by
  let z := (⌊x⌋₊ : ℝ) + 1
  let C := (π ^ 2 / 6) ^ (2 ^ (k + 2))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hE : 0 ≤ WeightedModel.expectation (polynomialRootWeight F) z
      (fun n ↦ (hooleyDelta n : ℝ)) :=
    WeightedModel.expectation_nonneg _ _ (fun _ _ ↦ Nat.cast_nonneg _)
  calc
    _ ≤ NairTenenbaum.sieveProduct F x *
        ((∑ a ∈ smoothSupport z,
          (hooleyDelta a : ℝ) * (NairTenenbaum.rootCount F a : ℝ) / a) * C) :=
      mul_le_mul_of_nonneg_left
        (polynomialRootSum_le_squarefree_cutoff F k hroot (lt_add_one _))
        (NairTenenbaum.sieveProduct_pos hF x).le
    _ = C * ((NairTenenbaum.sieveProduct F x *
        WeightedModel.normalizer (polynomialRootWeight F) z) *
        WeightedModel.expectation (polynomialRootWeight F) z
          (fun n ↦ (hooleyDelta n : ℝ))) := by
      rw [squarefree_polynomial_root_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left hE (sieveProduct_mul_weightedNormalizer_floor_le_one F hF x)) hC

/-- The short-sum input for (1.7), reduced entirely to the weighted Delta
expectation. Its remaining analytic mean estimate is not assumed here. -/
theorem polynomial_short_sum_weighted_bound (F : ℤ[X])
    (hF : NairTenenbaum.NoFixedPrimeDivisor F) (hI : Irreducible F)
    {α : ℝ} (hα : 0 < α) :
    ∃ x₀ > 0, ∃ C > 0, ∀ x y : ℝ, x₀ < x → x ^ α ≤ y → y ≤ x →
      polynomialDeltaShortSum F x y ≤
        C * y * WeightedModel.expectation (polynomialRootWeight F) ((⌊x⌋₊ : ℝ) + 1)
          (fun n ↦ (hooleyDelta n : ℝ)) := by
  have hdeg : 0 < F.natDegree := by
    have h := (hF.irreducible_map hI).natDegree_pos
    simpa only [natDegree_map_eq_of_injective (f := Int.castRingHom ℚ) Int.cast_injective] using h
  obtain ⟨x₀, hx₀, C₀, hC₀, hbound⟩ := polynomial_short_sum_root_bound F hF hdeg hα
  obtain ⟨k, hk⟩ := exists_rootCount_prime_power_bound F hF hI
  let A := (π ^ 2 / 6) ^ (2 ^ (k + 2))
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨x₀, hx₀, C₀ * A, mul_pos hC₀ hA, fun x y hx hy hyx ↦ ?_⟩
  have hxpos : 0 < x := hx₀.trans hx
  have hypos : 0 ≤ y := (rpow_nonneg hxpos.le α).trans hy
  calc
    _ ≤ C₀ * (y * NairTenenbaum.sieveProduct F x * polynomialDeltaRootSum F x) :=
      hbound x y hx hy hyx
    _ = (C₀ * y) * (NairTenenbaum.sieveProduct F x * polynomialDeltaRootSum F x) := by ring
    _ ≤ (C₀ * y) * (A *
        WeightedModel.expectation (polynomialRootWeight F) ((⌊x⌋₊ : ℝ) + 1)
          (fun n ↦ (hooleyDelta n : ℝ))) :=
      mul_le_mul_of_nonneg_left (sieved_polynomialRootSum_le_expectation F hF k hk x)
        (mul_nonneg hC₀.le hypos)
    _ = _ := by ring

end BretecheTenenbaumMean
