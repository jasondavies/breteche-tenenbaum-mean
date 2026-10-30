module

public import BretecheTenenbaumMean.DivisorSquareLower
public import BretecheTenenbaumMean.WindowBounds
public import BretecheTenenbaumMean.Targets

@[expose] public section

/-! # The lower bound in Theorem 1.2 -/

namespace BretecheTenenbaumMean

open Finset Real

lemma quadraticSum_eq_Ioc (x : ℝ) :
    quadraticSum x = ∑ n ∈ Ioc 0 ⌊x⌋₊, (hooleyDelta n : ℝ) ^ 2 := by
  unfold quadraticSum
  congr 1

lemma divisor_square_sum_le_quadratic {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, tau n ^ 2) ≤ (log x + 1) ^ 2 * quadraticSum x := by
  rw [quadraticSum_eq_Ioc, mul_sum]
  apply sum_le_sum
  intro n hn
  have hn' := mem_Ioc.1 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn'.1
  have hnx : (n : ℝ) ≤ x := (Nat.cast_le.2 hn'.2).trans (Nat.floor_le (by linarith))
  have hlog := log_le_log hn0 hnx
  have h := (tau_le_max_mul_log n).trans
    (mul_le_mul_of_nonneg_left (by linarith : log n + 1 ≤ log x + 1) (Nat.cast_nonneg (α := ℝ) (hooleyDelta n)))
  have hh := pow_le_pow_left₀ (show 0 ≤ tau n from Nat.cast_nonneg _) h 2
  simpa only [mul_pow, mul_comm] using hh

lemma quadraticSum_nonneg (x : ℝ) : 0 ≤ quadraticSum x :=
  sum_nonneg (fun _ _ ↦ sq_nonneg _)

lemma quadraticSum_ge_half {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ quadraticSum x := by
  apply (real_half_le_floor hx).trans
  rw [quadraticSum_eq_Ioc]
  calc
    (⌊x⌋₊ : ℝ) = ∑ _ ∈ Ioc 0 ⌊x⌋₊, (1 : ℝ) := by simp
    _ ≤ _ := by
      apply sum_le_sum
      intro n hn
      have h : (1 : ℝ) ≤ hooleyDelta n := by
        exact_mod_cast one_le_hooleyDelta (Nat.ne_zero_of_lt (mem_Ioc.1 hn).1)
      nlinarith

lemma quadraticSum_lower_eventually : ∃ c > 0, ∃ x₀ ≥ (3 : ℝ), ∀ x : ℝ, x₀ ≤ x →
    c * x * log x ≤ quadraticSum x := by
  obtain ⟨c, hc, R, hR, hdiv⟩ := divisor_square_sum_lower
  let x₀ := max 3 (max R (exp 2))
  refine ⟨c / 4, by positivity, x₀, le_max_left _ _, fun x hx ↦ ?_⟩
  have hx3 : 3 ≤ x := (le_max_left _ _).trans hx
  have hxR : R ≤ x := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hx
  have hxe : exp 2 ≤ x := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hx
  have hlx : 2 ≤ log x := by
    have h := log_le_log (exp_pos (2 : ℝ)) hxe
    simpa only [log_exp] using h
  have hcoef : (log x + 1) ^ 2 ≤ 4 * log x ^ 2 := by nlinarith
  have h := (hdiv x hxR).trans ((divisor_square_sum_le_quadratic (by linarith : 1 ≤ x)).trans
    (mul_le_mul_of_nonneg_right hcoef (quadraticSum_nonneg x)))
  have hp : 0 < 4 * log x ^ 2 := by positivity
  apply (mul_le_mul_iff_right₀ hp).1
  nlinarith [h]

/-- The lower half of Theorem 1.2 on the whole range `x ≥ 3`. -/
theorem theoremTwo_lower : ∃ c > 0, ∀ x : ℝ, 3 ≤ x →
    c * x * log x ≤ quadraticSum x := by
  obtain ⟨c, hc, x₀, hx₀, hlarge⟩ := quadraticSum_lower_eventually
  have hl₀ : 0 < log x₀ := log_pos (by linarith)
  let d := min c (1 / (2 * log x₀))
  have hd : 0 < d := lt_min hc (by positivity)
  refine ⟨d, hd, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hlx : 0 < log x := log_pos (by linarith)
  by_cases hxx : x₀ ≤ x
  · calc
      _ ≤ c * x * log x := by
        gcongr
        exact min_le_left _ _
      _ ≤ _ := hlarge x hxx
  · have hlog : log x ≤ log x₀ := log_le_log hx0 (le_of_not_ge hxx)
    calc
      _ ≤ (1 / (2 * log x₀)) * x * log x₀ := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (min_le_right _ _) hx0.le
        · exact hlog
        · exact hlx.le
        · positivity
      _ = x / 2 := by field_simp
      _ ≤ _ := quadraticSum_ge_half (by linarith)

end BretecheTenenbaumMean
