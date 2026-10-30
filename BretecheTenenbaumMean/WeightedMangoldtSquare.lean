module

public import BretecheTenenbaumMean.WeightedMangoldt

@[expose] public section

/-! # Chebyshev estimates with the squared divisor weight -/

namespace BretecheTenenbaumMean

open Finset Real
open scoped ArithmeticFunction

/-- The prime-power weight needed to remove logarithmic averaging. -/
noncomputable def divisorSquareMangoldt : ArithmeticFunction ℝ :=
  ⟨fun n ↦ tau n ^ 2 * Λ n, by simp⟩

@[simp] lemma divisorSquareMangoldt_apply (n : ℕ) : divisorSquareMangoldt n = tau n ^ 2 * Λ n := rfl

lemma sum_divisorSquareMangoldt_le_theta_psi {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, divisorSquareMangoldt n) ≤
      4 * Chebyshev.theta x + (1 + log x / log 2) ^ 2 *
        (Chebyshev.psi x - Chebyshev.theta x) := by
  classical
  have hsplit := sum_filter_add_sum_filter_not (Ioc 0 ⌊x⌋₊) Nat.Prime divisorSquareMangoldt
  rw [← hsplit]
  have hprime : (∑ n ∈ Ioc 0 ⌊x⌋₊ with n.Prime, divisorSquareMangoldt n) =
      4 * Chebyshev.theta x := by
    rw [Chebyshev.theta, mul_sum]
    apply sum_congr rfl
    intro n hn
    have hp := (mem_filter.1 hn).2
    norm_num [tau_prime hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
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
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (show 0 ≤ tau n from Nat.cast_nonneg _) ht 2)
      ArithmeticFunction.vonMangoldt_nonneg
  · simp [divisorSquareMangoldt_apply, ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hp]

/-- The squared divisor weight still has a linear Chebyshev bound. -/
theorem sum_divisorSquareMangoldt_le : ∃ C > 0, ∀ x : ℝ, 1 ≤ x →
    (∑ n ∈ Ioc 0 ⌊x⌋₊, divisorSquareMangoldt n) ≤ C * x := by
  obtain ⟨B, hB⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let D := |B| + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hBD : B ≤ D := (le_abs_self B).trans (by dsimp [D]; linarith)
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  refine ⟨4 * log 4 + D * (2 + 32 / log 2 ^ 2), by positivity, fun x hx ↦ ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hs0 : 0 ≤ sqrt x := sqrt_nonneg x
  have hs1 : 1 ≤ sqrt x := one_le_sqrt.2 hx
  have hsq := sq_sqrt hx0
  have hsx : sqrt x ≤ x := by nlinarith
  have hlog : log x ≤ 4 * sqrt (sqrt x) := by
    have h := log_le_rpow_div hs0 (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← sqrt_eq_rpow, log_sqrt hx0] at h
    linarith
  have hlog0 := log_nonneg hx
  have hlog2 : log x ^ 2 ≤ 16 * sqrt x := by
    have h := mul_self_le_mul_self hlog0 hlog
    nlinarith [sq_sqrt hs0]
  have hprod : (1 + log x / log 2) ^ 2 * sqrt x ≤ (2 + 32 / log 2 ^ 2) * x := by
    have hab : (log 2 + log x) ^ 2 ≤ 2 * log 2 ^ 2 + 2 * log x ^ 2 := by
      nlinarith [sq_nonneg (log 2 - log x)]
    have hm := mul_le_mul_of_nonneg_right hab hs0
    have hn : log x ^ 2 * sqrt x ≤ 16 * x := by
      nlinarith [mul_le_mul_of_nonneg_right hlog2 hs0]
    have hs := mul_le_mul_of_nonneg_left hsx (sq_nonneg (log 2))
    have he : (1 + log x / log 2) ^ 2 * sqrt x =
        ((log 2 + log x) ^ 2 * sqrt x) / log 2 ^ 2 := by field_simp
    rw [he]
    apply (div_le_iff₀ (sq_pos_of_pos hl2)).2
    have he' : ((2 + 32 / log 2 ^ 2) * x) * log 2 ^ 2 = (2 * log 2 ^ 2 + 32) * x := by
      field_simp
    rw [he']
    nlinarith
  calc
    _ ≤ 4 * Chebyshev.theta x + (1 + log x / log 2) ^ 2 *
        (Chebyshev.psi x - Chebyshev.theta x) := sum_divisorSquareMangoldt_le_theta_psi hx
    _ ≤ 4 * (log 4 * x) + (1 + log x / log 2) ^ 2 * (D * sqrt x) := by
      gcongr
      · exact Chebyshev.theta_le_log4_mul_x hx0
      · exact (hB x).trans (mul_le_mul_of_nonneg_right hBD hs0)
    _ ≤ 4 * (log 4 * x) + D * ((2 + 32 / log 2 ^ 2) * x) := by
      nlinarith [mul_le_mul_of_nonneg_left hprod hD.le]
    _ = _ := by ring

end BretecheTenenbaumMean
