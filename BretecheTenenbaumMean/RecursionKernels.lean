module

public import BretecheTenenbaumMean.IntegralRecursion
public import BretecheTenenbaumMean.RecursionErrorProducts
public import BretecheTenenbaumMean.LogPowerIntegral

@[expose] public section

/-! # Main and decaying parts of the moment recursion -/

namespace BretecheTenenbaumMean

open Finset Real MeasureTheory

noncomputable def recursionMainKernel (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ Icc 1 (q / 2), (q.choose j : ℝ) * momentProductSum δ T θ q j y /
    (y * log (3 * y) ^ 3)

noncomputable def recursionDecayKernel (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ Icc 1 (q / 2), (q.choose j : ℝ) * 2 ^ j * momentProductSum δ T θ q j y /
    (y * y ^ (1 / 4 : ℝ) * log (3 * y) ^ 2)

theorem recursionMainKernel_nonneg (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ)
    {y : ℝ} (hy : 1 ≤ y) : 0 ≤ recursionMainKernel δ T θ q y := by
  apply sum_nonneg
  intro j _
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (momentProductSum_nonneg ..))
    (mul_nonneg (by linarith) (pow_nonneg (log_nonneg (by linarith)) _))

theorem recursionDecayKernel_nonneg (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ)
    {y : ℝ} (hy : 1 ≤ y) : 0 ≤ recursionDecayKernel δ T θ q y := by
  apply sum_nonneg
  intro j _
  have hZ := momentProductSum_nonneg δ T θ q j y
  have hy0 : 0 < y := by linarith
  positivity

theorem intervalIntegrable_recursionMainKernel (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ)
    {X : ℝ} (hX : 1 ≤ X) : IntervalIntegrable (recursionMainKernel δ T θ q) volume 1 X := by
  have hi : ∀ j ∈ Icc 1 (q / 2), IntervalIntegrable
      (fun y : ℝ ↦ (q.choose j : ℝ) * momentProductSum δ T θ q j y / (y * log (3 * y) ^ 3)) volume 1 X := by
    intro j _
    have hc : ContinuousOn (fun y : ℝ ↦ (q.choose j : ℝ) / (y * log (3 * y) ^ 3)) (Set.uIcc 1 X) := by
      rw [Set.uIcc_of_le hX]
      intro y hy
      have hy0 : 0 < y := by linarith [hy.1]
      have hl : 0 < log (3 * y) := log_pos (by linarith [hy.1])
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := positivity)
    convert (intervalIntegrable_momentProductSum δ T θ q j 1 X).continuousOn_mul hc using 1
    ext y
    ring
  have h := IntervalIntegrable.sum (Icc 1 (q / 2)) hi
  convert h using 1
  ext y
  simp only [recursionMainKernel, Finset.sum_apply]

theorem intervalIntegrable_recursionDecayKernel (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ)
    {X : ℝ} (hX : 1 ≤ X) : IntervalIntegrable (recursionDecayKernel δ T θ q) volume 1 X := by
  have hi : ∀ j ∈ Icc 1 (q / 2), IntervalIntegrable
      (fun y : ℝ ↦ (q.choose j : ℝ) * 2 ^ j * momentProductSum δ T θ q j y /
        (y * y ^ (1 / 4 : ℝ) * log (3 * y) ^ 2)) volume 1 X := by
    intro j _
    have hc : ContinuousOn (fun y : ℝ ↦ (q.choose j : ℝ) * 2 ^ j /
        (y * y ^ (1 / 4 : ℝ) * log (3 * y) ^ 2)) (Set.uIcc 1 X) := by
      rw [Set.uIcc_of_le hX]
      intro y hy
      have hy0 : 0 < y := by linarith [hy.1]
      have hl : 0 < log (3 * y) := log_pos (by linarith [hy.1])
      have hr : 0 < y ^ (1 / 4 : ℝ) := rpow_pos_of_pos hy0 _
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := positivity)
    convert (intervalIntegrable_momentProductSum δ T θ q j 1 X).continuousOn_mul hc using 1
    ext y
    ring
  have h := IntervalIntegrable.sum (Icc 1 (q / 2)) hi
  convert h using 1
  ext y
  simp only [recursionDecayKernel, Finset.sum_apply]

theorem recursionIntegralKernel_split (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ)
    {y : ℝ} (hy : 1 ≤ y) :
    recursionIntegralKernel δ T θ q y / log (3 * y) =
      recursionMainKernel δ T θ q y + recursionDecayKernel δ T θ q y := by
  rw [recursionIntegralKernel_div_log δ T θ q hy]
  unfold recursionMainKernel recursionDecayKernel
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  have hy0 : 0 < y := by linarith
  have hl : 0 < log (3 * y) := log_pos (by linarith)
  have hr : 0 < y ^ (1 / 4 : ℝ) := rpow_pos_of_pos hy0 _
  generalize hL : log (3 * y) = L at hl ⊢
  field_simp

theorem sum_choose_two_pow_half_le (q : ℕ) :
    (∑ j ∈ Icc 1 (q / 2), (q.choose j : ℝ) * 2 ^ j) ≤ 3 ^ q := by
  calc
    _ ≤ ∑ j ∈ range (q + 1), (q.choose j : ℝ) * 2 ^ j := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact mem_range.2 (by have := (mem_Icc.1 hj).2; omega)
      · intro j _ _
        positivity
    _ = (2 + 1 : ℝ) ^ q := by
      rw [add_pow]
      apply sum_congr rfl
      intro j _
      simp only [one_pow, mul_one]
      ring
    _ = _ := by norm_num

/-- The pointwise fourth-root error after the elementary moment bound. -/
theorem recursionDecayKernel_bound : ∃ C > 0, ∀ δ T (θ : ℕ → ℝ) (q : ℕ),
    0 ≤ δ → 1 ≤ T → 2 ≤ q → ∀ y : ℝ, 1 ≤ y →
    recursionDecayKernel δ T θ q y ≤
      C * 3 ^ q * T ^ (q - 2) * (log (3 * y) ^ (q - 2) / (y * y ^ (1 / 4 : ℝ))) := by
  obtain ⟨C, hC, hZ⟩ := momentProductSum_trivial_bound
  refine ⟨C, hC, fun δ T θ q hδ hT hq y hy ↦ ?_⟩
  have hy0 : 0 < y := by linarith
  have hl : 0 < log (3 * y) := log_pos (by linarith)
  have hr : 0 < y ^ (1 / 4 : ℝ) := rpow_pos_of_pos hy0 _
  have hT0 : 0 ≤ T := by linarith
  let K := C * T ^ (q - 2) * (log (3 * y) ^ (q - 2) / (y * y ^ (1 / 4 : ℝ)))
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hpoint : ∀ j ∈ Icc 1 (q / 2),
      (q.choose j : ℝ) * 2 ^ j * momentProductSum δ T θ q j y /
        (y * y ^ (1 / 4 : ℝ) * log (3 * y) ^ 2) ≤ (q.choose j : ℝ) * 2 ^ j * K := by
    intro j hj
    obtain ⟨hj, hjq⟩ := mem_Icc.1 hj
    calc
      _ ≤ (q.choose j : ℝ) * 2 ^ j * (C * T ^ (q - 2) * log (3 * y) ^ q) /
          (y * y ^ (1 / 4 : ℝ) * log (3 * y) ^ 2) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hZ δ T θ q j hδ hT hj (by omega) y hy) (by positivity))
          (by positivity)
      _ = _ := by
        have hp : log (3 * y) ^ q = log (3 * y) ^ (q - 2) * log (3 * y) ^ 2 := by
          conv_lhs => rw [show q = (q - 2) + 2 by omega, pow_add]
        rw [hp]
        dsimp only [K]
        generalize hL : log (3 * y) = L at hl ⊢
        field_simp
  calc
    _ ≤ ∑ j ∈ Icc 1 (q / 2), (q.choose j : ℝ) * 2 ^ j * K := sum_le_sum hpoint
    _ = (∑ j ∈ Icc 1 (q / 2), (q.choose j : ℝ) * 2 ^ j) * K := (sum_mul ..).symm
    _ ≤ 3 ^ q * K := mul_le_mul_of_nonneg_right (sum_choose_two_pow_half_le q) hK
    _ = _ := by dsimp only [K]; ring

end BretecheTenenbaumMean
