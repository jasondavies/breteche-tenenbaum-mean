module

public import BretecheTenenbaumMean.WeightedMangoldt
public import BretecheTenenbaumMean.Sieve.SelbergDenominator
public import BretecheTenenbaumMean.PrimeSums.ProductLower

@[expose] public section

/-! # The weight `3^ω(n)` for the lower quadratic mean -/

namespace BretecheTenenbaumMean

open Finset Real
open scoped ArithmeticFunction.zeta

/-- The value at zero is the arithmetic-function extension. -/
noncomputable def omegaThree : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n = 0 then 0 else (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors n, by simp⟩

lemma omegaThree_nonneg (n : ℕ) : 0 ≤ omegaThree n := by
  unfold omegaThree
  simp only [ArithmeticFunction.coe_mk]
  split_ifs <;> positivity

@[simp] lemma omegaThree_one : omegaThree 1 = 1 := by simp [omegaThree]

lemma omegaThree_multiplicative : omegaThree.IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.2
  refine ⟨omegaThree_one, fun {m n} hm hn hmn ↦ ?_⟩
  simp [omegaThree, hm, hn, ArithmeticFunction.cardDistinctFactors_mul hmn, pow_add]

lemma omegaThree_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    omegaThree (p ^ k) = 3 := by
  simp [omegaThree, hp.ne_zero, ArithmeticFunction.cardDistinctFactors_apply_prime_pow hp hk]

lemma omegaThree_prime {p : ℕ} (hp : p.Prime) : omegaThree p = 3 := by
  simpa using omegaThree_prime_pow hp (show (1 : ℕ) ≠ 0 by omega)

lemma omegaThree_convolution_zeta_nonneg (n : ℕ) : 0 ≤ (omegaThree * ζ) n := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  exact sum_nonneg (fun d _ ↦ omegaThree_nonneg d)

/-- At a prime power the divisor sum is `1+3k`, at most `(k+1)²`. -/
theorem omegaThree_convolution_le_tau_sq (n : ℕ) :
    (omegaThree * ζ) n ≤ tau n ^ 2 := by
  have hmult := omegaThree_multiplicative.mul ArithmeticFunction.isMultiplicative_zeta.natCast (R := ℝ)
  refine Nat.recOnPrimeCoprime ?_ ?_ ?_ n
  · simp [tau]
  · intro p k hp
    rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp, sum_range_succ', tau_prime_pow hp]
    simp only [pow_zero, omegaThree_one, omegaThree_prime_pow hp (Nat.succ_ne_zero _), sum_const,
      card_range, nsmul_eq_mul]
    cases k with
    | zero => norm_num
    | succ k => push_cast; nlinarith [sq_nonneg (k : ℝ)]
  · intro a b _ _ hab ha hb
    rw [hmult.map_mul_of_coprime hab, tau_mul_of_coprime hab, mul_pow]
    exact mul_le_mul ha hb (omegaThree_convolution_zeta_nonneg b) (sq_nonneg _)

noncomputable def omegaThreeHarmonic : ArithmeticFunction ℝ :=
  ⟨fun n ↦ omegaThree n / n, by simp⟩

@[simp] lemma omegaThreeHarmonic_apply (n : ℕ) : omegaThreeHarmonic n = omegaThree n / n := rfl

lemma omegaThreeHarmonic_multiplicative : omegaThreeHarmonic.IsMultiplicative := by
  refine ⟨by simp [omegaThreeHarmonic], fun hmn ↦ ?_⟩
  simp only [omegaThreeHarmonic_apply, omegaThree_multiplicative.map_mul_of_coprime hmn, Nat.cast_mul]
  exact mul_div_mul_comm _ _ _ _

noncomputable def omegaThreeProduct (y : ℝ) : ℝ :=
  ∑ n ∈ smoothSupport y, omegaThree n / n

lemma omegaThreeProduct_eq (y : ℝ) :
    omegaThreeProduct y = ∏ p ∈ primesLT y, (1 + (3 : ℝ) / p) := by
  have h := omegaThreeHarmonic_multiplicative.prodPrimeFactors_one_add_of_squarefree (primeProduct_squarefree y)
  rw [primeFactors_primeProduct] at h
  change (∑ n ∈ (primeProduct y).divisors, omegaThreeHarmonic n) = _
  rw [← h]
  apply prod_congr rfl
  intro p hp
  simp [omegaThree_prime (mem_primesLT.1 hp).1]

lemma omegaThreeProduct_pos (y : ℝ) : 0 < omegaThreeProduct y := by
  rw [omegaThreeProduct_eq]
  exact prod_pos (fun _ _ ↦ by positivity)

/-- Exact logarithmic mean of the finite Euler product. -/
lemma omegaThreeProduct_log_moment (y : ℝ) :
    (∑ n ∈ smoothSupport y, omegaThree n / n * log n) =
      omegaThreeProduct y * ∑ p ∈ primesLT y, (3 / (p + 3 : ℝ)) * log p := by
  have h := Sieve.squarefree_divisor_log_moment omegaThreeHarmonic omegaThreeHarmonic_multiplicative
    (primeProduct_squarefree y) (fun p hp ↦ by
      have hp' := Nat.prime_of_mem_primeFactors hp
      simp only [omegaThreeHarmonic_apply, omegaThree_prime hp']
      positivity)
  rw [primeFactors_primeProduct] at h
  change (∑ n ∈ (primeProduct y).divisors, omegaThreeHarmonic n * log n) =
    (∑ n ∈ (primeProduct y).divisors, omegaThreeHarmonic n) * _
  rw [h]
  congr 1
  apply sum_congr rfl
  intro p hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (mem_primesLT.1 hp).1.ne_zero
  simp only [omegaThreeHarmonic_apply, omegaThree_prime (mem_primesLT.1 hp).1]
  field_simp

end BretecheTenenbaumMean
