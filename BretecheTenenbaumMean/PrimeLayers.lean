module

public import BretecheTenenbaumMean.Probability
public import BretecheTenenbaumMean.DistinctProductSum

@[expose] public section

/-! # Fixed prime-factor-count layers of the squarefree probability space -/

namespace BretecheTenenbaumMean

open Real Finset

/-- Squarefree smooth integers are in bijection with subsets of the allowed primes. -/
theorem sum_smoothSupport_eq_powerset (x : ℝ) (f : ℕ → ℝ) :
    (∑ n ∈ smoothSupport x, f n) = ∑ s ∈ (primesLT x).powerset, f (∏ p ∈ s, p) := by
  rw [smoothSupport, ← Nat.divisors_filter_squarefree_of_squarefree (primeProduct_squarefree x),
    Nat.sum_divisors_filter_squarefree (primeProduct_ne_zero x)]
  have he : (UniqueFactorizationMonoid.normalizedFactors (primeProduct x)).toFinset =
      (primeProduct x).primeFactors := by
    ext p
    simp only [Nat.factors_eq, Nat.primeFactors, Multiset.mem_toFinset, Multiset.mem_coe, List.mem_toFinset]
  rw [he, primeFactors_primeProduct]
  simp only [Finset.prod_val, Function.id_def]

/-- The reciprocal sum on a fixed `ω`-layer is an elementary-symmetric sum. -/
theorem reciprocal_prime_layer_eq (x : ℝ) (r : ℕ) :
    (∑ n ∈ smoothSupport x, if n.primeFactors.card = r then (n : ℝ)⁻¹ else 0) =
      distinctProductSum (primesLT x) (fun p ↦ (p : ℝ)⁻¹) r := by
  classical
  rw [sum_smoothSupport_eq_powerset, distinctProductSum, powersetCard_eq_filter, sum_filter]
  apply sum_congr rfl
  intro s hs
  have hprime : ∀ p ∈ s, p.Prime := fun p hp ↦ (mem_primesLT.1 ((mem_powerset.1 hs) hp)).1
  rw [Nat.primeFactors_prod hprime]
  split_ifs
  · rw [Nat.cast_prod, prod_inv_distrib]
  · rfl

/-- Exact probability of a prescribed number of distinct prime factors. -/
theorem probability_prime_layer_eq (x : ℝ) (r : ℕ) :
    probability x {n | n.primeFactors.card = r} =
      distinctProductSum (primesLT x) (fun p ↦ (p : ℝ)⁻¹) r / normalizer x := by
  classical
  unfold probability expectation
  congr 1
  rw [← reciprocal_prime_layer_eq]
  apply sum_congr rfl
  intro n _
  by_cases hn : n.primeFactors.card = r <;> simp [Set.indicator, hn]

/-- The factorial upper bound for a reciprocal prime layer, uniform in its index. -/
theorem reciprocal_prime_layer_le (x : ℝ) (r : ℕ) :
    (∑ n ∈ smoothSupport x, if n.primeFactors.card = r then (n : ℝ)⁻¹ else 0) ≤
      (∑ p ∈ primesLT x, (p : ℝ)⁻¹) ^ r / (r.factorial : ℝ) := by
  rw [reciprocal_prime_layer_eq]
  exact distinctProductSum_le _ _ _ (fun _ _ ↦ by positivity)

/-- The square-root saving for every layer simultaneously. -/
theorem probability_prime_layer_uniform (x : ℝ) (r : ℕ) :
    probability x {n | n.primeFactors.card = r} ≤
      (8 * exp (∑ p ∈ primesLT x, (p : ℝ)⁻¹)) /
        (sqrt (1 + ∑ p ∈ primesLT x, (p : ℝ)⁻¹) * normalizer x) := by
  rw [probability_prime_layer_eq, ← div_div]
  exact div_le_div_of_nonneg_right
    (distinctProductSum_uniform _ _ _ (fun _ _ ↦ by positivity)) (normalizer_pos x).le

/-- A squarefree integer has two divisor choices for each prime factor. -/
theorem tau_squarefree {n : ℕ} (hn : Squarefree n) : tau n = (2 : ℝ) ^ n.primeFactors.card := by
  have h : n.divisors.card = 2 ^ n.primeFactors.card := by
    rw [Nat.card_divisors hn.ne_zero]
    calc (∏ p ∈ n.primeFactors, (n.factorization p + 1)) = ∏ _ ∈ n.primeFactors, (2 : ℕ) := by
            apply prod_congr rfl
            intro p hp
            rw [Nat.factorization_eq_one_of_squarefree hn
              (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
         _ = _ := by simp
  unfold tau
  exact_mod_cast h

/-- The divisor-weighted layer is the reciprocal layer times `2^r`. -/
theorem tau_prime_layer_eq (x : ℝ) (r : ℕ) :
    (∑ n ∈ smoothSupport x, if n.primeFactors.card = r then tau n / n else 0) =
      (2 : ℝ) ^ r * distinctProductSum (primesLT x) (fun p ↦ (p : ℝ)⁻¹) r := by
  classical
  rw [← reciprocal_prime_layer_eq, mul_sum]
  apply sum_congr rfl
  intro n hn
  by_cases hr : n.primeFactors.card = r
  · simp only [hr, ite_true, tau_squarefree (mem_smoothSupport.1 hn).1, div_eq_mul_inv]
  · simp only [hr, ite_false, mul_zero]

/-- The factorial estimate for `∑_{ω(n)=r} τ(n)/n` used in the high-frequency argument. -/
theorem tau_prime_layer_le (x : ℝ) (r : ℕ) :
    (∑ n ∈ smoothSupport x, if n.primeFactors.card = r then tau n / n else 0) ≤
      (2 * ∑ p ∈ primesLT x, (p : ℝ)⁻¹) ^ r / (r.factorial : ℝ) := by
  rw [tau_prime_layer_eq, mul_pow, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left
    (distinctProductSum_le _ _ _ (fun _ _ ↦ by positivity)) (by positivity)

/-- The saving from the prescribed prime-factor count in the dyadic layers. -/
theorem tau_prime_layer_uniform (x : ℝ) (r : ℕ) :
    (∑ n ∈ smoothSupport x, if n.primeFactors.card = r then tau n / n else 0) ≤
      8 * exp (2 * ∑ p ∈ primesLT x, (p : ℝ)⁻¹) /
        sqrt (1 + 2 * ∑ p ∈ primesLT x, (p : ℝ)⁻¹) :=
  (tau_prime_layer_le x r).trans (factorial_term_uniform (by positivity) r)

end BretecheTenenbaumMean
