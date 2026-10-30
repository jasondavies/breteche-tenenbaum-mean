module

public import BretecheTenenbaumMean.RecursionPrimeAverage

@[expose] public section

/-! # The smoothed integral estimate for `V_q` -/

namespace BretecheTenenbaumMean

open Finset Real MeasureTheory

noncomputable def recursionIntegralKernel (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ) (y : ℝ) : ℝ :=
  logSmoothingWeight y * recursionAverage δ T θ q y

theorem recursionIntegralKernel_nonneg (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ)
    {y : ℝ} (hy : 1 ≤ y) : 0 ≤ recursionIntegralKernel δ T θ q y :=
  mul_nonneg (logSmoothingWeight_pos hy).le (recursionAverage_nonneg δ T θ q hy)

theorem intervalIntegrable_recursionAverage (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ)
    {X : ℝ} (hX : 1 ≤ X) : IntervalIntegrable (recursionAverage δ T θ q) volume 1 X := by
  unfold recursionAverage
  suffices h : IntervalIntegrable
      (∑ j ∈ Icc 1 (q / 2), fun y : ℝ ↦ (q.choose j : ℝ) *
        (1 / log (3 * y) + 2 ^ j / y ^ (1 / 4 : ℝ)) * momentProductSum δ T θ q j y) volume 1 X by
    convert h using 1
    ext y
    simp only [Finset.sum_apply]
  apply IntervalIntegrable.sum
  intro j _
  have hc : ContinuousOn (fun y : ℝ ↦ (q.choose j : ℝ) *
      (1 / log (3 * y) + 2 ^ j / y ^ (1 / 4 : ℝ))) (Set.uIcc 1 X) := by
    rw [Set.uIcc_of_le hX]
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    have hL : 0 < log (3 * y) := log_pos (by linarith [hy.1])
    have hr : 0 < y ^ (1 / 4 : ℝ) := rpow_pos_of_pos hy0 _
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  exact (intervalIntegrable_momentProductSum δ T θ q j 1 X).continuousOn_mul hc

theorem intervalIntegrable_recursionIntegralKernel (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ)
    {X : ℝ} (hX : 1 ≤ X) : IntervalIntegrable (recursionIntegralKernel δ T θ q) volume 1 X := by
  apply (intervalIntegrable_recursionAverage δ T θ q hX).continuousOn_mul
  rw [Set.uIcc_of_le hX]
  exact continuousOn_logSmoothingWeight le_rfl

/-- The smoothed `V_q` estimate in §2.3, with no conditional analytic input.
The exact fourth-root error remains in `recursionIntegralKernel`. -/
theorem recursionError_integral_bound : ∃ C > 0, ∀ δ T (θ : ℕ → ℝ) (q : ℕ),
    2 ≤ q → ∀ x : ℝ, 2 ≤ x →
    recursionError δ T θ q x ≤ 1 + C * ∫ y in 1..x ^ 2, recursionIntegralKernel δ T θ q y := by
  classical
  obtain ⟨C, hC, hband⟩ := recursionPrimeTerm_band_bound
  refine ⟨4 * C, by positivity, fun δ T θ q hq x hx ↦ ?_⟩
  let A := recursionPrimeTerm δ T θ q
  let F := fun y : ℝ ↦ ∑ p ∈ primesLT x, smoothedPrimeTerm A p y
  have hx2 : 1 ≤ x ^ 2 := by nlinarith
  have hF : ∀ y : ℝ, 1 ≤ y → F y ≤ C * recursionIntegralKernel δ T θ q y := by
    intro y hy
    let s := (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < y ∧ y ≤ (p : ℝ) ^ 2)
    have hs : ∀ p ∈ s, p.Prime ∧ sqrt y ≤ p ∧ (p : ℝ) < y := by
      intro p hp
      obtain ⟨hpx, hpy, hyp⟩ := mem_filter.1 hp
      exact ⟨(mem_primesLT.1 hpx).1,
        (sqrt_le_left (Nat.cast_nonneg p)).2 hyp, hpy⟩
    have he : F y = logSmoothingWeight y * ∑ p ∈ s, A p := by
      dsimp only [F, s, smoothedPrimeTerm]
      rw [sum_filter, mul_sum]
      apply sum_congr rfl
      intro p _
      simp only [Set.indicator_apply, Set.mem_Ioc]
      split_ifs <;> ring
    rw [he]
    have h := mul_le_mul_of_nonneg_left (hband δ T θ q hq y hy s hs)
      (logSmoothingWeight_pos hy).le
    convert h using 1
    dsimp only [recursionIntegralKernel]
    ring
  have hiF : IntervalIntegrable F volume 1 (x ^ 2) := by
    have h := IntervalIntegrable.sum (primesLT x) (a := 1) (b := x ^ 2) (fun p hp ↦
      (integrable_smoothedPrimeTerm A (mem_primesLT.1 hp).1).intervalIntegrable)
    convert h using 1
    ext y
    simp only [F, Finset.sum_apply]
  have hm := intervalIntegral.integral_mono_on hx2 hiF
    ((intervalIntegrable_recursionIntegralKernel δ T θ q hx2).const_mul C) (fun y hy ↦ hF y hy.1)
  rw [intervalIntegral.integral_const_mul] at hm
  have hsm := prime_sum_le_smoothed_integral hx A (fun p _ ↦ recursionPrimeTerm_nonneg δ T θ q p)
  rw [recursionError_eq_sum]
  change 1 + ∑ p ∈ primesLT x, A p ≤ _
  have h := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 4)
  linarith

end BretecheTenenbaumMean
