module

public import BretecheTenenbaumMean.SecondMoment

@[expose] public section

/-! # The finite probability space of squarefree smooth integers

The support is the divisors of the product of primes strictly below the real
cutoff. This is finite even though its elements need not be below the cutoff.
The weights are exactly those in §2.1, with `y = 2`.
-/

namespace BretecheTenenbaumMean

open Finset Real

theorem mem_primesLT {p : ℕ} {x : ℝ} : p ∈ primesLT x ↔ p.Prime ∧ (p : ℝ) < x := by
  classical
  simp only [primesLT, mem_filter, mem_range]
  exact ⟨fun h => h.2, fun h => ⟨Nat.lt_succ_of_le (Nat.le_floor h.2.le), h⟩⟩

theorem primeProduct_ne_zero (x : ℝ) : primeProduct x ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  exact fun p hp => (mem_primesLT.mp hp).1.ne_zero

theorem primeProduct_squarefree (x : ℝ) : Squarefree (primeProduct x) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (mem_primesLT.mp hp).1 (mem_primesLT.mp hq).1).mpr hpq
  · exact fun p hp => (mem_primesLT.mp hp).1.squarefree

theorem primeFactors_primeProduct (x : ℝ) : (primeProduct x).primeFactors = primesLT x :=
  Nat.primeFactors_prod (fun _ hp => (mem_primesLT.mp hp).1)

theorem mem_smoothSupport {n : ℕ} {x : ℝ} :
    n ∈ smoothSupport x ↔ Squarefree n ∧ ∀ p ∈ n.primeFactors, (p : ℝ) < x := by
  constructor
  · intro hn
    have hd := Nat.dvd_of_mem_divisors hn
    refine ⟨(primeProduct_squarefree x).squarefree_of_dvd hd, ?_⟩
    intro p hp
    have hsub := Nat.primeFactors_mono hd (primeProduct_ne_zero x)
    rw [primeFactors_primeProduct] at hsub
    exact (mem_primesLT.mp (hsub hp)).2
  · rintro ⟨hn, h⟩
    apply Nat.mem_divisors.mpr
    refine ⟨?_, primeProduct_ne_zero x⟩
    rw [← Nat.prod_primeFactors_of_squarefree hn]
    apply Finset.prod_dvd_prod_of_subset
    intro p hp
    exact mem_primesLT.mpr ⟨Nat.prime_of_mem_primeFactors hp, h p hp⟩

theorem normalizer_pos (x : ℝ) : 0 < normalizer x := by
  apply Finset.prod_pos
  intro p _
  positivity

/-- Finite Euler-product identity, proving that the probability is normalized. -/
theorem sum_reciprocal_smoothSupport (x : ℝ) :
    ∑ n ∈ smoothSupport x, (n : ℝ)⁻¹ = normalizer x := by
  let f : ArithmeticFunction ℝ := ⟨fun n => (n : ℝ)⁻¹, by simp⟩
  have hf : f.IsMultiplicative := by
    constructor
    · norm_num [f]
    · intro m n _
      simp [f, Nat.cast_mul, mul_comm]
  have h := hf.prodPrimeFactors_one_add_of_squarefree (primeProduct_squarefree x)
  rw [primeFactors_primeProduct] at h
  exact h.symm

@[simp] theorem expectation_one (x : ℝ) : expectation x (fun _ => 1) = 1 := by
  simp only [expectation, one_div, sum_reciprocal_smoothSupport, div_self (normalizer_pos x).ne']

theorem expectation_nonneg (x : ℝ) {f : ℕ → ℝ}
    (hf : ∀ n ∈ smoothSupport x, 0 ≤ f n) : 0 ≤ expectation x f := by
  apply div_nonneg _ (normalizer_pos x).le
  exact Finset.sum_nonneg fun n hn => div_nonneg (hf n hn) (Nat.cast_nonneg n)

theorem expectation_mono (x : ℝ) {f g : ℕ → ℝ}
    (h : ∀ n ∈ smoothSupport x, f n ≤ g n) : expectation x f ≤ expectation x g := by
  apply div_le_div_of_nonneg_right _ (normalizer_pos x).le
  exact Finset.sum_le_sum fun n hn => div_le_div_of_nonneg_right (h n hn) (Nat.cast_nonneg n)

theorem expectation_add (x : ℝ) (f g : ℕ → ℝ) :
    expectation x (fun n => f n + g n) = expectation x f + expectation x g := by
  simp [expectation, add_div, Finset.sum_add_distrib]

theorem expectation_const_mul (x c : ℝ) (f : ℕ → ℝ) :
    expectation x (fun n => c * f n) = c * expectation x f := by
  simp [expectation, mul_div_assoc, ← Finset.mul_sum]

/-- Euler product for the expectation of any coprime-multiplicative weight.
The weight need not vanish at zero: zero never belongs to the support. -/
theorem expectation_multiplicative (x : ℝ) (f : ℕ → ℝ) (h1 : f 1 = 1)
    (hmul : ∀ m n, m.Coprime n → f (m * n) = f m * f n) :
    expectation x f = (∏ p ∈ primesLT x, (1 + f p / p)) / normalizer x := by
  let g : ArithmeticFunction ℝ := ⟨fun n => f n / n, by simp⟩
  have hg : g.IsMultiplicative := by
    constructor
    · simpa [g] using h1
    · intro m n hmn
      simp only [g, ArithmeticFunction.coe_mk, hmul m n hmn, Nat.cast_mul]
      exact mul_div_mul_comm _ _ _ _
  have h := hg.prodPrimeFactors_one_add_of_squarefree (primeProduct_squarefree x)
  rw [primeFactors_primeProduct] at h
  exact congrArg (fun a => a / normalizer x) h.symm

theorem tau_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n) :
    tau (m * n) = tau m * tau n := by
  simp [tau, hmn.card_divisors_mul]

@[simp] theorem tau_one : tau 1 = 1 := by simp [tau]

theorem tau_prime {p : ℕ} (hp : p.Prime) : tau p = 2 := by
  simp [tau, hp.divisors, hp.ne_one.symm]

/-- Exact divisor-count moments of the squarefree probability model. -/
theorem expectation_tau_pow (x : ℝ) (k : ℕ) :
    expectation x (fun n => tau n ^ k) =
      (∏ p ∈ primesLT x, (1 + (2 : ℝ) ^ k / p)) / normalizer x := by
  rw [expectation_multiplicative x _ (by simp) (fun m n h => by
    rw [tau_mul_of_coprime h, mul_pow])]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [tau_prime (mem_primesLT.mp hp).1]

theorem probability_nonneg (x : ℝ) (E : Set ℕ) : 0 ≤ probability x E := by
  apply expectation_nonneg
  intro n _
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) n

@[simp] theorem probability_univ (x : ℝ) : probability x Set.univ = 1 := by
  simp [probability]

theorem probability_le_one (x : ℝ) (E : Set ℕ) : probability x E ≤ 1 := by
  rw [← expectation_one x]
  apply expectation_mono
  intro n _
  exact Set.indicator_le_self' (fun _ _ => zero_le_one) n

/-- Markov's inequality in the paper's finite probability space. -/
theorem probability_gt_le (x : ℝ) {f : ℕ → ℝ} (hf : ∀ n ∈ smoothSupport x, 0 ≤ f n)
    {T : ℝ} (hT : 0 < T) : probability x {n | T < f n} ≤ expectation x f / T := by
  rw [le_div_iff₀ hT, mul_comm, probability, ← expectation_const_mul]
  apply expectation_mono
  intro n hn
  by_cases h : T < f n
  · simpa [Set.indicator, h] using h.le
  · simpa [Set.indicator, h] using hf n hn

end BretecheTenenbaumMean
