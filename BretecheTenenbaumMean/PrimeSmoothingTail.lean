module

public import BretecheTenenbaumMean.PrimeSmoothing
public import BretecheTenenbaumMean.PrimeSums.LogTail

@[expose] public section

/-! # Integrating the reciprocal-logarithmic prime tail -/

namespace BretecheTenenbaumMean

open Finset Real MeasureTheory

/-- Truncation of an interval-integrable function at a closed upper endpoint. -/
theorem intervalIntegrable_indicator_Iic {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable ((Set.Iic c).indicator f) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at hf ⊢
  exact hf.indicator measurableSet_Iic

theorem log_three_mul_le_four_log {x y : ℝ} (hx : 2 ≤ x)
    (hy : 1 ≤ y) (hyx : y ≤ x ^ 2) : log (3 * y) ≤ 4 * log x := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have h1 := log_le_log hy0 hyx
  have h2 := log_le_log (by norm_num : (0 : ℝ) < 3)
    (show (3 : ℝ) ≤ x ^ 2 by nlinarith)
  rw [log_pow] at h1 h2
  rw [log_mul (by norm_num) hy0.ne']
  norm_num only [Nat.cast_ofNat] at h1 h2
  linarith

/-- Finite summation and integration yield the extra logarithmic denominator
in the transition from `V_q` to `S_q`. -/
theorem prime_integral_tail_bound : ∃ C > 0, ∀ x : ℝ, 2 ≤ x →
    ∀ f : ℝ → ℝ, IntervalIntegrable f volume 1 (x ^ 2) →
    (∀ y ∈ Set.Icc 1 (x ^ 2), 0 ≤ f y) →
    (∫ y in 1..x ^ 2, f y) / log x +
      (∑ p ∈ primesLT x, (∫ y in 1..(p : ℝ) ^ 2, f y) / ((p : ℝ) * log p)) ≤
    C * ∫ y in 1..x ^ 2, f y / log (3 * y) := by
  classical
  obtain ⟨C, hC, htail⟩ := PrimeSums.prime_inv_log_sqrt_tail_bound
  refine ⟨4 + C, by linarith, fun x hx f hi hf ↦ ?_⟩
  have hx2 : 1 ≤ x ^ 2 := by nlinarith
  have hlx : 0 < log x := log_pos (by linarith)
  have hc : ContinuousOn (fun y : ℝ ↦ (log (3 * y))⁻¹) (Set.uIcc 1 (x ^ 2)) := by
    rw [Set.uIcc_of_le hx2]
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    have hly : 0 < log (3 * y) := log_pos (by linarith [hy.1])
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have hiL : IntervalIntegrable (fun y ↦ f y / log (3 * y)) volume 1 (x ^ 2) := by
    simpa only [div_eq_mul_inv] using hi.mul_continuousOn hc
  have hfirst : (∫ y in 1..x ^ 2, f y) / log x ≤
      4 * ∫ y in 1..x ^ 2, f y / log (3 * y) := by
    rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hx2 (hi.div_const _) (hiL.const_mul _)
    intro y hy
    have hly : 0 < log (3 * y) := log_pos (by linarith [hy.1])
    have hlog := log_three_mul_le_four_log hx hy.1 hy.2
    have hdiv : 1 / log x ≤ 4 / log (3 * y) := (div_le_div_iff₀ hlx hly).2 (by linarith)
    have h := mul_le_mul_of_nonneg_left hdiv (hf y hy)
    convert h using 1 <;> ring
  let F := fun p : ℕ ↦ (Set.Iic ((p : ℝ) ^ 2)).indicator f
  have hiF : ∀ p : ℕ, IntervalIntegrable (F p) volume 1 (x ^ 2) :=
    fun p ↦ intervalIntegrable_indicator_Iic hx2 hi
  have hsum : (∑ p ∈ primesLT x, (∫ y in 1..(p : ℝ) ^ 2, f y) / ((p : ℝ) * log p)) =
      ∫ y in 1..x ^ 2, ∑ p ∈ primesLT x, F p y / ((p : ℝ) * log p) := by
    rw [intervalIntegral.integral_finsetSum (fun p _ ↦ (hiF p).div_const _)]
    apply sum_congr rfl
    intro p hp
    rw [intervalIntegral.integral_div]
    congr 1
    symm
    apply intervalIntegral.integral_indicator
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesLT.1 hp).1.two_le
    have hpx := (mem_primesLT.1 hp).2
    constructor <;> nlinarith
  have hiSum : IntervalIntegrable
      (fun y ↦ ∑ p ∈ primesLT x, F p y / ((p : ℝ) * log p)) volume 1 (x ^ 2) := by
    have h := IntervalIntegrable.sum (primesLT x) (fun p _ ↦ (hiF p).div_const ((p : ℝ) * log p))
    convert h using 1
    ext y
    simp only [Finset.sum_apply]
  have hsecond : (∑ p ∈ primesLT x, (∫ y in 1..(p : ℝ) ^ 2, f y) / ((p : ℝ) * log p)) ≤
      C * ∫ y in 1..x ^ 2, f y / log (3 * y) := by
    rw [hsum, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hx2 hiSum (hiL.const_mul C)
    intro y hy
    let s := (primesLT x).filter (fun p : ℕ ↦ y ≤ (p : ℝ) ^ 2)
    have he : (∑ p ∈ primesLT x, F p y / ((p : ℝ) * log p)) =
        f y * ∑ p ∈ s, 1 / ((p : ℝ) * log p) := by
      dsimp only [s, F]
      rw [sum_filter, mul_sum]
      apply sum_congr rfl
      intro p _
      simp only [Set.indicator_apply, Set.mem_Iic]
      split_ifs <;> ring
    rw [he]
    have ht := htail y hy.1 s (fun p hp ↦ ⟨(mem_primesLT.1 (mem_filter.1 hp).1).1,
      (sqrt_le_left (Nat.cast_nonneg p)).2 (mem_filter.1 hp).2⟩)
    have h := mul_le_mul_of_nonneg_left ht (hf y hy)
    convert h using 1
    ring
  nlinarith

end BretecheTenenbaumMean
