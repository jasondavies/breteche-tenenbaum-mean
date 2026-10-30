module

public import BretecheTenenbaumMean.WindowBounds

@[expose] public section

/-! # Log-convexity of the moments

Integrating `Δ(n,u)^q (Δ(n,u)-t)^2 ≥ 0` gives a quadratic in `t`.
Its nonnegativity proves the adjacent moment inequality without additional
regularity assumptions. In particular this supplies the `q=4,j=2` step in §2.3.
-/

namespace BretecheTenenbaumMean

open Real MeasureTheory

@[simp] theorem moment_zero (q : ℕ) (hq : 1 ≤ q) : moment q 0 = 0 := by
  simp [moment, delta, divisorWindow, Nat.ne_of_gt hq]

theorem moment_pos {n q : ℕ} (hn : n ≠ 0) (hq : 1 ≤ q) : 0 < moment q n := by
  have hm := max_pow_le_moment n q hq
  have hd : (0 : ℝ) < hooleyDelta n := by
    exact_mod_cast (one_le_hooleyDelta hn)
  have hpow := pow_pos hd q
  have h2 : (0 : ℝ) < 2 ^ q := by positivity
  nlinarith

theorem moment_quadratic_nonneg (n q : ℕ) (hq : 1 ≤ q) (t : ℝ) :
    0 ≤ moment (q + 2) n - 2 * t * moment (q + 1) n + t ^ 2 * moment q n := by
  have h (u : ℝ) : delta n u ^ q * (delta n u - t) ^ 2 =
      delta n u ^ (q + 2) - 2 * t * delta n u ^ (q + 1) + t ^ 2 * delta n u ^ q := by
    rw [pow_add, pow_succ]
    ring
  have hiq := integrable_delta_pow n q hq
  have hi1 := integrable_delta_pow n (q + 1) (by omega)
  have hi2 := integrable_delta_pow n (q + 2) (by omega)
  have hnonneg : 0 ≤ ∫ u, delta n u ^ q * (delta n u - t) ^ 2 :=
    integral_nonneg fun u => mul_nonneg (pow_nonneg (delta_nonneg n u) _) (sq_nonneg _)
  simp_rw [h] at hnonneg
  rw [integral_add (f := fun u => delta n u ^ (q + 2) - 2 * t * delta n u ^ (q + 1))
      (g := fun u => t ^ 2 * delta n u ^ q)
      (hi2.sub (hi1.const_mul (2 * t))) (hiq.const_mul (t ^ 2)),
    integral_sub (f := fun u => delta n u ^ (q + 2))
      (g := fun u => 2 * t * delta n u ^ (q + 1))
      hi2 (hi1.const_mul (2 * t)), integral_const_mul, integral_const_mul] at hnonneg
  exact hnonneg

theorem moment_logConvex (n q : ℕ) (hq : 1 ≤ q) :
    moment (q + 1) n ^ 2 ≤ moment q n * moment (q + 2) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [moment_zero _ hq, moment_zero _ (show 1 ≤ q + 1 by omega),
      moment_zero _ (show 1 ≤ q + 2 by omega)]
  have hpos := moment_pos hn hq
  have h := moment_quadratic_nonneg n q hq (moment (q + 1) n / moment q n)
  have he : moment (q + 2) n - 2 * (moment (q + 1) n / moment q n) * moment (q + 1) n +
      (moment (q + 1) n / moment q n) ^ 2 * moment q n =
      (moment q n * moment (q + 2) n - moment (q + 1) n ^ 2) / moment q n := by
    field_simp
    ring
  rw [he] at h
  have hnum : 0 ≤ moment q n * moment (q + 2) n - moment (q + 1) n ^ 2 := by
    simpa using (le_div_iff₀ hpos).mp h
  exact sub_nonneg.mp hnum

/-- The special interpolation inequality used for `q=4,j=2`. -/
theorem moment_two_sq_le (n : ℕ) : moment 2 n ^ 2 ≤ moment 3 n * tau n := by
  simpa [moment_one, mul_comm] using moment_logConvex n 1 le_rfl

end BretecheTenenbaumMean
