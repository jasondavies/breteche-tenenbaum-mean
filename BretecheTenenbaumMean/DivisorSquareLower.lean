module

public import BretecheTenenbaumMean.OmegaTruncation

@[expose] public section

/-! # A lower bound for the average square of the divisor function -/

namespace BretecheTenenbaumMean

open Finset Real
open scoped ArithmeticFunction.zeta

lemma nat_quotient_ge_half {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
    (N : ℝ) / (2 * d) ≤ (N / d : ℕ) := by
  have hq : 1 ≤ N / d := (Nat.one_le_div_iff hd).2 hdN
  have hlt := Nat.lt_mul_div_succ N hd
  have hN : N ≤ 2 * (N / d) * d := by nlinarith
  apply (div_le_iff₀ (show (0 : ℝ) < 2 * d by positivity)).2
  exact_mod_cast (by nlinarith [hN] : N ≤ (N / d) * (2 * d))

/-- Counting multiples turns the harmonic weight into a lower summatory bound. -/
theorem divisor_square_sum_ge_harmonic (N : ℕ) :
    (N : ℝ) / 2 * (∑ d ∈ Ioc 0 N, omegaThree d / d) ≤
      ∑ n ∈ Ioc 0 N, tau n ^ 2 := by
  calc
    _ ≤ ∑ d ∈ Ioc 0 N, omegaThree d * (N / d : ℕ) := by
      rw [mul_sum]
      apply sum_le_sum
      intro d hd
      have hd' := mem_Ioc.1 hd
      have h := mul_le_mul_of_nonneg_left (nat_quotient_ge_half hd'.1 hd'.2) (omegaThree_nonneg d)
      convert h using 1; ring
    _ = ∑ n ∈ Ioc 0 N, (omegaThree * ζ) n :=
      (ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum omegaThree N).symm
    _ ≤ _ := sum_le_sum (fun n _ ↦ omegaThree_convolution_le_tau_sq n)

lemma real_half_le_floor {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
  have h1' : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast h1
  linarith [Nat.lt_floor_add_one x]

/-- The classical lower order `x(log x)^3`, proved from a finite Euler product. -/
theorem divisor_square_sum_lower : ∃ c > 0, ∃ x₀ ≥ (2 : ℝ), ∀ x : ℝ, x₀ ≤ x →
    c * x * log x ^ 3 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, tau n ^ 2 := by
  obtain ⟨c, hc, x₀, hx₀, h⟩ := omegaThree_harmonic_lower
  refine ⟨c / 4, by positivity, x₀, hx₀, fun x hx ↦ ?_⟩
  have hx2 := hx₀.trans hx
  have hx0 : 0 ≤ x := by linarith
  have hsum : 0 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, omegaThree n / n :=
    sum_nonneg (fun n _ ↦ div_nonneg (omegaThree_nonneg _) (Nat.cast_nonneg _))
  calc
    _ = x / 4 * (c * log x ^ 3) := by ring
    _ ≤ x / 4 * ∑ n ∈ Ioc 0 ⌊x⌋₊, omegaThree n / n :=
      mul_le_mul_of_nonneg_left (h x hx) (by positivity)
    _ ≤ (⌊x⌋₊ : ℝ) / 2 * ∑ n ∈ Ioc 0 ⌊x⌋₊, omegaThree n / n := by
      apply mul_le_mul_of_nonneg_right _ hsum
      linarith [real_half_le_floor hx2]
    _ ≤ _ := divisor_square_sum_ge_harmonic _

end BretecheTenenbaumMean
