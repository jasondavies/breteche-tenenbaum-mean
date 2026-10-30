module

public import BretecheTenenbaumMean.WeightedMangoldt
public import BretecheTenenbaumMean.InverseSquareConvolution

@[expose] public section

/-! # The bounded harmonic contribution of square factors -/

namespace BretecheTenenbaumMean

open Finset Real
open scoped ArithmeticFunction ArithmeticFunction.zeta

noncomputable def tauArithmetic : ArithmeticFunction ℝ :=
  ⟨tau, by simp [tau]⟩

@[simp] lemma tauArithmetic_apply (n : ℕ) : tauArithmetic n = tau n := rfl

lemma tauArithmetic_multiplicative : tauArithmetic.IsMultiplicative :=
  ⟨tau_one, fun h ↦ tau_mul_of_coprime h⟩

noncomputable def tripleDivisor : ArithmeticFunction ℝ := tauArithmetic * ζ

lemma tripleDivisor_apply (n : ℕ) : tripleDivisor n = ∑ d ∈ n.divisors, tau d :=
  ArithmeticFunction.coe_mul_zeta_apply

lemma tripleDivisor_nonneg (n : ℕ) : 0 ≤ tripleDivisor n := by
  rw [tripleDivisor_apply]
  exact sum_nonneg (fun _ _ ↦ by unfold tau; positivity)

lemma tripleDivisor_multiplicative : tripleDivisor.IsMultiplicative :=
  tauArithmetic_multiplicative.mul ArithmeticFunction.isMultiplicative_zeta.natCast

/-- At a prime power the two sides are `2k+1` and `(k+1)(k+2)/2`. -/
lemma tau_square_le_tripleDivisor (n : ℕ) : tau (n ^ 2) ≤ tripleDivisor n := by
  refine Nat.recOnPrimeCoprime ?_ ?_ ?_ n
  · simp [tau]
  · intro p k hp
    rw [← pow_mul, tau_prime_pow hp, tripleDivisor_apply, Nat.sum_divisors_prime_pow hp]
    simp only [tau_prime_pow hp, Nat.cast_mul, Nat.cast_ofNat]
    induction k with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ]
      push_cast
      nlinarith
  · intro a b _ _ hab ha hb
    rw [mul_pow, tau_mul_of_coprime (hab.pow 2 2),
      tripleDivisor_multiplicative.map_mul_of_coprime hab]
    exact mul_le_mul ha hb (by unfold tau; positivity) (tripleDivisor_nonneg a)

lemma tauArithmetic_eq_zeta_mul_zeta : tauArithmetic = (ζ : ArithmeticFunction ℝ) * ζ := by
  ext n
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  simp only [tauArithmetic_apply, tau]
  have : (∑ d ∈ n.divisors, (ζ : ArithmeticFunction ℝ) d) = ∑ _ ∈ n.divisors, (1 : ℝ) := by
    apply sum_congr rfl
    intro d hd
    simp [Nat.ne_zero_of_lt (Nat.pos_of_mem_divisors hd)]
  rw [this]
  simp

/-- Divide an arithmetic function by the square of its argument. -/
noncomputable def divideSquare (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ f n / (n : ℝ) ^ 2, by simp⟩

@[simp] lemma divideSquare_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    divideSquare f n = f n / (n : ℝ) ^ 2 := rfl

lemma divideSquare_mul (f g : ArithmeticFunction ℝ) :
    divideSquare (f * g) = divideSquare f * divideSquare g := by
  ext n
  simp only [divideSquare_apply, ArithmeticFunction.mul_apply, sum_div]
  apply sum_congr rfl
  intro d hd
  have h := (Nat.mem_divisorsAntidiagonal.1 hd).1
  rw [← h, Nat.cast_mul, mul_pow, div_mul_div_comm]

lemma sum_convolution_le_product (f g : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (f * g) n) ≤ (∑ n ∈ Ioc 0 N, f n) * ∑ n ∈ Ioc 0 N, g n := by
  rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter, sum_mul_sum, ← sum_product']
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    (fun d _ _ ↦ mul_nonneg (hf d.1) (hg d.2))

lemma divideSquare_zeta_sum_le (N : ℕ) :
    (∑ n ∈ Ioc 0 N, divideSquare (ζ : ArithmeticFunction ℝ) n) ≤ π ^ 2 / 6 := by
  calc
    _ = ∑ n ∈ Ioc 0 N, 1 / (n : ℝ) ^ 2 := by
      apply sum_congr rfl
      intro n hn
      simp [Nat.ne_zero_of_lt (mem_Ioc.1 hn).1]
    _ ≤ _ := sum_inv_sq_le_pi_sq_div_six _

/-- An absolute bound, sufficient to sum all square factors in the arithmetic transfer. -/
theorem sum_tau_square_div_sq_le (N : ℕ) :
    (∑ b ∈ Ioc 0 N, tau (b ^ 2) / (b : ℝ) ^ 2) ≤ (π ^ 2 / 6) ^ 3 := by
  let f := divideSquare (ζ : ArithmeticFunction ℝ)
  have hf : ∀ n, 0 ≤ f n := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hff : ∀ n, 0 ≤ (f * f) n := by
    intro n
    rw [ArithmeticFunction.mul_apply]
    exact sum_nonneg (fun _ _ ↦ mul_nonneg (hf _) (hf _))
  have hbound := divideSquare_zeta_sum_le N
  have hsum : 0 ≤ ∑ n ∈ Ioc 0 N, f n := sum_nonneg (fun n _ ↦ hf n)
  have htriple : divideSquare tripleDivisor = (f * f) * f := by
    simp only [tripleDivisor, tauArithmetic_eq_zeta_mul_zeta, divideSquare_mul, f]
  calc
    _ ≤ ∑ b ∈ Ioc 0 N, tripleDivisor b / (b : ℝ) ^ 2 := by
      apply sum_le_sum
      intro b _
      exact div_le_div_of_nonneg_right (tau_square_le_tripleDivisor b) (sq_nonneg _)
    _ = ∑ b ∈ Ioc 0 N, ((f * f) * f) b := by
      change (∑ b ∈ Ioc 0 N, divideSquare tripleDivisor b) = _
      rw [htriple]
    _ ≤ (∑ b ∈ Ioc 0 N, (f * f) b) * ∑ b ∈ Ioc 0 N, f b :=
      sum_convolution_le_product _ _ hff hf N
    _ ≤ ((∑ b ∈ Ioc 0 N, f b) * ∑ b ∈ Ioc 0 N, f b) * ∑ b ∈ Ioc 0 N, f b :=
      mul_le_mul_of_nonneg_right (sum_convolution_le_product f f hf hf N) hsum
    _ = (∑ b ∈ Ioc 0 N, f b) ^ 3 := by ring
    _ ≤ _ := pow_le_pow_left₀ hsum hbound 3

end BretecheTenenbaumMean
