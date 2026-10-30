module

public import BretecheTenenbaumMean.DeltaSubmultiplicative
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

@[expose] public section

/-! # A Chebyshev bound weighted by the divisor function -/

namespace BretecheTenenbaumMean

open Finset Real
open scoped ArithmeticFunction

lemma tau_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    tau (p ^ k) = (k : ℝ) + 1 := by
  unfold tau
  exact_mod_cast (ArithmeticFunction.sigma_zero_apply (p ^ k)).symm.trans
    (ArithmeticFunction.sigma_zero_apply_prime_pow hp)

/-- On prime powers, the divisor function grows at most logarithmically. -/
lemma tau_primePower_le_log {n : ℕ} (hn : IsPrimePow n) :
    tau n ≤ 1 + log n / log 2 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := hn
  have hp' := hp.nat_prime
  rw [tau_prime_pow hp', Nat.cast_pow, log_pow]
  have hl : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlp : log (2 : ℝ) ≤ log p := log_le_log (by norm_num) (by exact_mod_cast hp'.two_le)
  have h := (le_div_iff₀ hl).2 (mul_le_mul_of_nonneg_left hlp (Nat.cast_nonneg k))
  linarith

/-- The prime-power weight needed to remove logarithmic averaging. -/
noncomputable def divisorMangoldt : ArithmeticFunction ℝ :=
  ⟨fun n ↦ tau n * Λ n, by simp⟩

@[simp] lemma divisorMangoldt_apply (n : ℕ) : divisorMangoldt n = tau n * Λ n := rfl

lemma divisorMangoldt_nonneg (n : ℕ) : 0 ≤ divisorMangoldt n := by
  simp only [divisorMangoldt_apply]
  exact mul_nonneg (by unfold tau; positivity) ArithmeticFunction.vonMangoldt_nonneg

lemma sum_divisorMangoldt_le_theta_psi {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, divisorMangoldt n) ≤
      2 * Chebyshev.theta x + (1 + log x / log 2) *
        (Chebyshev.psi x - Chebyshev.theta x) := by
  classical
  have hsplit := sum_filter_add_sum_filter_not (Ioc 0 ⌊x⌋₊) Nat.Prime divisorMangoldt
  rw [← hsplit]
  have hprime : (∑ n ∈ Ioc 0 ⌊x⌋₊ with n.Prime, divisorMangoldt n) =
      2 * Chebyshev.theta x := by
    rw [Chebyshev.theta, mul_sum]
    apply sum_congr rfl
    intro n hn
    have hp := (mem_filter.1 hn).2
    simp [tau_prime hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  rw [hprime, Chebyshev.psi_sub_theta_eq_sum_not_prime, mul_sum]
  apply add_le_add_right
  apply sum_le_sum
  intro n hn
  by_cases hp : IsPrimePow n
  · have hn' := (mem_Ioc.1 (mem_filter.1 hn).1)
    have hnx : (n : ℝ) ≤ x := (Nat.cast_le.2 hn'.2).trans (Nat.floor_le (by linarith))
    have hlog : log n ≤ log x := log_le_log (by exact_mod_cast hn'.1) hnx
    have ht := (tau_primePower_le_log hp).trans
      (add_le_add_right (div_le_div_of_nonneg_right hlog (le_of_lt (log_pos (show (1 : ℝ) < 2 by norm_num)))) 1)
    exact mul_le_mul_of_nonneg_right ht ArithmeticFunction.vonMangoldt_nonneg
  · simp [divisorMangoldt_apply, ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hp]

/-- A linear bound for the summatory divisor-weighted von Mangoldt function. -/
theorem sum_divisorMangoldt_le : ∃ C > 0, ∀ x : ℝ, 1 ≤ x →
    (∑ n ∈ Ioc 0 ⌊x⌋₊, divisorMangoldt n) ≤ C * x := by
  obtain ⟨B, hB⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let D := |B| + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hBD : B ≤ D := (le_abs_self B).trans (by dsimp [D]; linarith)
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  refine ⟨2 * log 4 + D * (1 + 2 / log 2), by positivity, fun x hx ↦ ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hs0 : 0 ≤ sqrt x := sqrt_nonneg x
  have hs1 : 1 ≤ sqrt x := one_le_sqrt.2 hx
  have hsq := sq_sqrt hx0
  have hsx : sqrt x ≤ x := by nlinarith
  have hlog : log x ≤ 2 * sqrt x := by
    have h := log_le_rpow_div hx0 (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← sqrt_eq_rpow] at h
    linarith
  have hprod : (1 + log x / log 2) * sqrt x ≤ (1 + 2 / log 2) * x := by
    have h := mul_le_mul_of_nonneg_right hlog hs0
    have hd := (div_le_div_of_nonneg_right h hl2.le)
    field_simp at hd ⊢
    nlinarith
  have hcoef : 0 ≤ 1 + log x / log 2 := by
    have := log_nonneg hx
    positivity
  calc
    _ ≤ 2 * Chebyshev.theta x + (1 + log x / log 2) *
        (Chebyshev.psi x - Chebyshev.theta x) := sum_divisorMangoldt_le_theta_psi hx
    _ ≤ 2 * (log 4 * x) + (1 + log x / log 2) * (D * sqrt x) := by
      gcongr
      · exact Chebyshev.theta_le_log4_mul_x hx0
      · exact (hB x).trans (mul_le_mul_of_nonneg_right hBD hs0)
    _ ≤ 2 * (log 4 * x) + D * ((1 + 2 / log 2) * x) := by
      nlinarith [mul_le_mul_of_nonneg_left hprod hD.le]
    _ = _ := by ring

end BretecheTenenbaumMean
