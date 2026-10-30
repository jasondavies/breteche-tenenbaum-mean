module

public import BretecheTenenbaumMean.PenaltyIntegral

@[expose] public section

/-! # Uniform Gaussian sums on the square-root grid -/

namespace BretecheTenenbaumMean

open Real Finset MeasureTheory

/-- One weighted grid value is bounded by the Gaussian mass on its adjacent
square-root interval. The Gaussian is widened by a factor two. -/
theorem gaussian_sqrt_grid_cell {γ r : ℝ} (hγ : 0 ≤ γ) (hr : 1 ≤ r) (m : ℝ) :
    exp (-γ * (sqrt r - m) ^ 2) / sqrt r ≤
      3 * exp γ * (∫ s in sqrt r..sqrt (r + 1), exp (-(γ / 2) * (s - m) ^ 2)) := by
  have hr0 : 0 ≤ r := by linarith
  have hα : 0 < sqrt r := sqrt_pos.2 (by linarith)
  have hα0 := hα.le
  have hβ0 := sqrt_nonneg (r + 1)
  have hαsq := sq_sqrt hr0
  have hβsq := sq_sqrt (show 0 ≤ r + 1 by linarith)
  have hab : sqrt r ≤ sqrt (r + 1) := sqrt_le_sqrt (by linarith)
  have hβ : sqrt (r + 1) ≤ 2 * sqrt r := (sqrt_le_left (by positivity)).2 (by nlinarith)
  have hwidth : 1 / sqrt r ≤ 3 * (sqrt (r + 1) - sqrt r) := by
    rw [div_le_iff₀ hα]
    have h := mul_le_mul_of_nonneg_left hβ (sub_nonneg.2 hab)
    nlinarith
  have hstep : sqrt (r + 1) ≤ sqrt r + 1 := (sqrt_le_left (by positivity)).2 (by nlinarith)
  have hp : ∀ s ∈ Set.Icc (sqrt r) (sqrt (r + 1)),
      exp (-γ * (sqrt r - m) ^ 2) ≤ exp γ * exp (-(γ / 2) * (s - m) ^ 2) := by
    intro s hs
    have hd0 : 0 ≤ s - sqrt r := by linarith [hs.1]
    have hd1 : s - sqrt r ≤ 1 := by linarith [hs.2]
    have hsq : (s - m) ^ 2 ≤ 2 * (sqrt r - m) ^ 2 + 2 := by
      nlinarith [sq_nonneg ((s - sqrt r) - (sqrt r - m)),
        mul_nonneg hd0 (sub_nonneg.2 hd1)]
    have h := mul_le_mul_of_nonneg_left hsq hγ
    rw [← exp_add]
    exact exp_le_exp.2 (by nlinarith)
  have hc : Continuous (fun s : ℝ ↦ exp γ * exp (-(γ / 2) * (s - m) ^ 2)) := by fun_prop
  have hm := intervalIntegral.integral_mono_on hab
    (f := fun _ ↦ exp (-γ * (sqrt r - m) ^ 2)) intervalIntegrable_const
    (hc.intervalIntegrable (μ := volume) _ _) hp
  simp only [intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_const_mul] at hm
  calc _ = exp (-γ * (sqrt r - m) ^ 2) * (1 / sqrt r) := by ring
    _ ≤ exp (-γ * (sqrt r - m) ^ 2) * (3 * (sqrt (r + 1) - sqrt r)) :=
      mul_le_mul_of_nonneg_left hwidth (exp_pos _).le
    _ = 3 * ((sqrt (r + 1) - sqrt r) * exp (-γ * (sqrt r - m) ^ 2)) := by ring
    _ ≤ 3 * (exp γ * (∫ s in sqrt r..sqrt (r + 1), exp (-(γ / 2) * (s - m) ^ 2))) :=
      mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = _ := by ring

/-- Every initial segment of the weighted Gaussian grid has bounded mass,
uniformly in the center. -/
theorem sum_range_gaussian_sqrt_grid_le {γ : ℝ} (hγ : 0 < γ) (m : ℝ) (N : ℕ) :
    (∑ j ∈ range N, exp (-γ * (sqrt (j + 1 : ℝ) - m) ^ 2) / sqrt (j + 1 : ℝ)) ≤
      3 * exp γ * sqrt (π / (γ / 2)) := by
  have hc : Continuous (fun s : ℝ ↦ exp (-(γ / 2) * (s - m) ^ 2)) := by fun_prop
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ ↦ sqrt (j + 1 : ℝ)) (n := N) (μ := volume)
    (fun _ _ ↦ hc.intervalIntegrable _ _)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, sqrt_one] at hs
  have hN : (1 : ℝ) ≤ sqrt (N + 1 : ℝ) := by
    have h := sqrt_le_sqrt (show (1 : ℝ) ≤ N + 1 by have := Nat.cast_nonneg (α := ℝ) N; linarith)
    simpa only [sqrt_one] using h
  calc _ ≤ ∑ j ∈ range N, 3 * exp γ *
      (∫ s in sqrt (j + 1 : ℝ)..sqrt ((j : ℝ) + 1 + 1), exp (-(γ / 2) * (s - m) ^ 2)) := by
        apply sum_le_sum
        intro j _
        exact gaussian_sqrt_grid_cell hγ.le (by have := Nat.cast_nonneg (α := ℝ) j; linarith) m
    _ = 3 * exp γ * (∫ s in (1 : ℝ)..sqrt (N + 1 : ℝ), exp (-(γ / 2) * (s - m) ^ 2)) := by
      rw [← mul_sum, hs]
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_translated_gaussian_le (by positivity) hN m) (by positivity)

/-- The same bound holds for arbitrary finite sets of grid points. -/
theorem sum_gaussian_sqrt_grid_le {γ : ℝ} (hγ : 0 < γ) (m : ℝ) (s : Finset ℕ) :
    (∑ j ∈ s, exp (-γ * (sqrt (j + 1 : ℝ) - m) ^ 2) / sqrt (j + 1 : ℝ)) ≤
      3 * exp γ * sqrt (π / (γ / 2)) := by
  classical
  have hsub : s ⊆ range (s.sup id + 1) := by
    intro j hj
    exact mem_range.2 (Nat.lt_succ_of_le (le_sup (f := id) hj))
  calc _ ≤ ∑ j ∈ range (s.sup id + 1),
      exp (-γ * (sqrt (j + 1 : ℝ) - m) ^ 2) / sqrt (j + 1 : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
    _ ≤ _ := sum_range_gaussian_sqrt_grid_le hγ m _

end BretecheTenenbaumMean
