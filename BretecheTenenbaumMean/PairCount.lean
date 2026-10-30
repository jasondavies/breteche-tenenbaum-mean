module

public import BretecheTenenbaumMean.TupleWindows
public import BretecheTenenbaumMean.SecondMoment

@[expose] public section

/-! # The close-divisor pair count `T(n,0)` -/

namespace BretecheTenenbaumMean

open Finset Real MeasureTheory

/-- The real-valued count of ordered divisor pairs at logarithmic distance at most one. -/
noncomputable def closeDivisorPairs (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, ∑ e ∈ n.divisors,
    if |log d - log e| ≤ 1 then (1 : ℝ) else 0

lemma wide_window_indicator_mul (a b w : ℝ) :
    (fun u ↦ (Set.Ico (a - w) a).indicator (fun _ : ℝ ↦ (1 : ℝ)) u *
      (Set.Ico (b - w) b).indicator (fun _ : ℝ ↦ (1 : ℝ)) u) =
      (Set.Ico (max (a - w) (b - w)) (min a b)).indicator (fun _ : ℝ ↦ (1 : ℝ)) := by
  funext u
  rw [← Set.inter_indicator_mul, Set.Ico_inter_Ico]
  simp

lemma integrable_wide_window_indicator_mul (a b w : ℝ) :
    Integrable (fun u ↦ (Set.Ico (a - w) a).indicator (fun _ : ℝ ↦ (1 : ℝ)) u *
      (Set.Ico (b - w) b).indicator (fun _ : ℝ ↦ (1 : ℝ)) u) := by
  rw [wide_window_indicator_mul]
  exact (integrableOn_const measure_Ico_lt_top.ne).integrable_indicator measurableSet_Ico

lemma integral_wide_window_indicator_mul (a b w : ℝ) :
    (∫ u, (Set.Ico (a - w) a).indicator (fun _ : ℝ ↦ (1 : ℝ)) u *
      (Set.Ico (b - w) b).indicator (fun _ : ℝ ↦ (1 : ℝ)) u) = max (w - |a - b|) 0 := by
  rw [wide_window_indicator_mul, integral_indicator_const (1 : ℝ) measurableSet_Ico]
  simp only [smul_eq_mul, mul_one, Real.volume_real_Ico]
  congr 1
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right (sub_le_sub_right h w), abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, max_eq_left (sub_le_sub_right h w), abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- Pair expansion for a window of arbitrary width. -/
theorem integral_wideDelta_sq_eq_sum (n : ℕ) (w : ℝ) :
    (∫ u, wideDelta n w u ^ 2) = ∑ d ∈ n.divisors, ∑ e ∈ n.divisors,
      max (w - |log d - log e|) 0 := by
  simp only [wideDelta, pow_two, sum_mul_sum]
  rw [integral_finsetSum _ (fun d _ ↦ integrable_finsetSum _
    (fun e _ ↦ integrable_wide_window_indicator_mul (log (d : ℕ)) (log (e : ℕ)) w))]
  apply sum_congr rfl
  intro d _
  rw [integral_finsetSum _ (fun e _ ↦ integrable_wide_window_indicator_mul (log (d : ℕ)) (log (e : ℕ)) w)]
  simp_rw [integral_wide_window_indicator_mul]

/-- The tent kernel is bounded by the indicator of pairs at distance at most one. -/
theorem moment_two_le_closeDivisorPairs (n : ℕ) : moment 2 n ≤ closeDivisorPairs n := by
  rw [moment_two_eq_sum, closeDivisorPairs]
  apply sum_le_sum
  intro d _
  apply sum_le_sum
  intro e _
  split_ifs with h
  · exact max_le (by linarith [abs_nonneg (log (d : ℝ) - log e)]) (by norm_num)
  · rw [max_eq_right (by linarith [lt_of_not_ge h])]

/-- Every close pair contributes at least one to the width-two overlap sum. -/
theorem closeDivisorPairs_le_four_moment_two (n : ℕ) : closeDivisorPairs n ≤ 4 * moment 2 n := by
  calc
    _ ≤ ∑ d ∈ n.divisors, ∑ e ∈ n.divisors, max (2 - |log d - log e|) 0 := by
      unfold closeDivisorPairs
      apply sum_le_sum
      intro d _
      apply sum_le_sum
      intro e _
      split_ifs with h
      · exact (by linarith : (1 : ℝ) ≤ 2 - |log d - log e|).trans (le_max_left _ _)
      · exact le_max_right _ _
    _ = ∫ u, wideDelta n 2 u ^ 2 := (integral_wideDelta_sq_eq_sum n 2).symm
    _ ≤ _ := by simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using integral_wideDelta_two_le n 2

/-- The two comparisons for `T(n,0)` stated in §2.1. -/
theorem closeDivisorPairs_bounds (n : ℕ) :
    moment 2 n ≤ closeDivisorPairs n ∧ closeDivisorPairs n ≤ 4 * moment 2 n :=
  ⟨moment_two_le_closeDivisorPairs n, closeDivisorPairs_le_four_moment_two n⟩

end BretecheTenenbaumMean
