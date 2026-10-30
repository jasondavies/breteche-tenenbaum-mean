module

public import BretecheTenenbaumMean.SquareDivisorSum

@[expose] public section

/-! # Convergent inverse-square sums of divisor-count powers -/

namespace BretecheTenenbaumMean

open Finset Real
open scoped ArithmeticFunction.zeta

/-- Positive powers, indexed from zero to preserve the value at zero. -/
noncomputable def tauPower (k : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ tau n ^ (k + 1), by simp [tau]⟩

@[simp] lemma tauPower_apply (k n : ℕ) : tauPower k n = tau n ^ (k + 1) := rfl

lemma tauPower_nonneg (k n : ℕ) : 0 ≤ tauPower k n := by
  exact pow_nonneg (Nat.cast_nonneg _) _

lemma tauPower_zero : tauPower 0 = tauArithmetic := by ext n; simp

/-- Submultiplicativity gives a lower bound for every divisor summand. -/
lemma tauPower_succ_le_convolution (k n : ℕ) :
    tauPower (k + 1) n ≤ (tauPower k * tauPower k) n := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b ↦ tauPower k a * tauPower k b)]
  calc
    _ = ∑ _ ∈ n.divisors, tau n ^ (k + 1) := by
      simp only [tauPower_apply, sum_const, nsmul_eq_mul]
      change tau n ^ (k + 1 + 1) = tau n * tau n ^ (k + 1)
      rw [pow_succ']
    _ ≤ _ := by
      apply sum_le_sum
      intro d hd
      have h := tau_mul_le d (n / d)
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)] at h
      simpa only [mul_pow, tauPower_apply] using
        pow_le_pow_left₀ (show 0 ≤ tau n from Nat.cast_nonneg _) h (k + 1)

/-- Every fixed power of the divisor function has a bounded inverse-square sum.
An explicit but non-optimal bound is enough for the square-factor transfer. -/
theorem sum_tau_pow_div_sq_le (k N : ℕ) :
    (∑ n ∈ Ioc 0 N, tau n ^ (k + 1) / (n : ℝ) ^ 2) ≤
      (π ^ 2 / 6) ^ (2 ^ (k + 1)) := by
  let Z := π ^ 2 / 6
  induction k with
  | zero =>
    let f := divideSquare (ζ : ArithmeticFunction ℝ)
    have hf : ∀ n, 0 ≤ f n := fun n ↦ div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have he : divideSquare tauArithmetic = f * f := by
      rw [tauArithmetic_eq_zeta_mul_zeta, divideSquare_mul]
    have hb : (∑ n ∈ Ioc 0 N, f n) ≤ Z := divideSquare_zeta_sum_le N
    have h0 : 0 ≤ ∑ n ∈ Ioc 0 N, f n := sum_nonneg (fun n _ ↦ hf n)
    calc
      _ = ∑ n ∈ Ioc 0 N, (f * f) n := by
        change (∑ n ∈ Ioc 0 N, divideSquare (tauPower 0) n) = _
        rw [tauPower_zero, he]
      _ ≤ (∑ n ∈ Ioc 0 N, f n) * ∑ n ∈ Ioc 0 N, f n := sum_convolution_le_product _ _ hf hf N
      _ ≤ Z * Z := mul_self_le_mul_self h0 hb
      _ = _ := by norm_num [Z, pow_two]
  | succ k ih =>
    let f := divideSquare (tauPower k)
    have hf : ∀ n, 0 ≤ f n := fun n ↦ div_nonneg (tauPower_nonneg k n) (sq_nonneg _)
    have h0 : 0 ≤ ∑ n ∈ Ioc 0 N, f n := sum_nonneg (fun n _ ↦ hf n)
    calc
      _ ≤ ∑ n ∈ Ioc 0 N, (tauPower k * tauPower k) n / (n : ℝ) ^ 2 := by
        apply sum_le_sum
        intro n _
        exact div_le_div_of_nonneg_right (tauPower_succ_le_convolution k n) (sq_nonneg _)
      _ = ∑ n ∈ Ioc 0 N, (f * f) n := by
        change (∑ n ∈ Ioc 0 N, divideSquare (tauPower k * tauPower k) n) = _
        rw [divideSquare_mul]
      _ ≤ (∑ n ∈ Ioc 0 N, f n) * ∑ n ∈ Ioc 0 N, f n := sum_convolution_le_product _ _ hf hf N
      _ ≤ Z ^ (2 ^ (k + 1)) * Z ^ (2 ^ (k + 1)) := mul_self_le_mul_self h0 ih
      _ = _ := by
        change Z ^ (2 ^ (k + 1)) * Z ^ (2 ^ (k + 1)) = Z ^ (2 ^ (k + 1 + 1))
        rw [← pow_two, ← pow_mul]
        exact congrArg (fun j : ℕ ↦ Z ^ j) (pow_succ 2 (k + 1)).symm

/-- The square factors required for the ordinary quadratic mean contribute
at most an absolute constant. -/
theorem sum_tau_square_sq_div_sq_le (N : ℕ) :
    (∑ b ∈ Ioc 0 N, tau (b ^ 2) ^ 2 / (b : ℝ) ^ 2) ≤ (π ^ 2 / 6) ^ 16 := by
  calc
    _ ≤ ∑ b ∈ Ioc 0 N, tau b ^ 4 / (b : ℝ) ^ 2 := by
      apply sum_le_sum
      intro b _
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      have h := tau_mul_le b b
      rw [← pow_two] at h
      have hh := mul_self_le_mul_self (show 0 ≤ tau (b ^ 2) from Nat.cast_nonneg _) h
      nlinarith
    _ ≤ _ := by simpa using sum_tau_pow_div_sq_le 3 N

end BretecheTenenbaumMean
