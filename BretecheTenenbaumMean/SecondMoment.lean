module

public import BretecheTenenbaumMean.Moments

@[expose] public section

/-! # An exact real-space formula for the second moment -/

namespace BretecheTenenbaumMean

open Real MeasureTheory Set

/-- The indicator of the unit window ending at `a`, as a function of its position. -/
noncomputable def windowIndicator (a : ℝ) : ℝ → ℝ :=
  (Ico (a - 1) a).indicator (fun _ => 1)

theorem windowIndicator_mul (a b : ℝ) :
    (fun u => windowIndicator a u * windowIndicator b u) =
      (Ico (max (a - 1) (b - 1)) (min a b)).indicator (fun _ => 1) := by
  funext u
  rw [windowIndicator, windowIndicator, ← Set.inter_indicator_mul, Set.Ico_inter_Ico]
  simp

theorem integrable_windowIndicator_mul (a b : ℝ) :
    Integrable (fun u => windowIndicator a u * windowIndicator b u) := by
  rw [windowIndicator_mul]
  exact (integrableOn_const (measure_Ico_lt_top.ne)).integrable_indicator measurableSet_Ico

theorem integral_windowIndicator_mul (a b : ℝ) :
    (∫ u, windowIndicator a u * windowIndicator b u) = max (1 - |a - b|) 0 := by
  rw [windowIndicator_mul]
  rw [integral_indicator_const (1 : ℝ) measurableSet_Ico]
  simp only [smul_eq_mul, mul_one, Real.volume_real_Ico]
  congr 1
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right (sub_le_sub_right h 1), abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, max_eq_left (sub_le_sub_right h 1), abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- Each pair of divisors contributes the length of the overlap of two unit intervals. -/
theorem moment_two_eq_sum (n : ℕ) :
    moment 2 n = ∑ d ∈ n.divisors, ∑ e ∈ n.divisors,
      max (1 - |log d - log e|) 0 := by
  have h (u : ℝ) : delta n u ^ 2 = ∑ d ∈ n.divisors, ∑ e ∈ n.divisors,
      windowIndicator (log d) u * windowIndicator (log e) u := by
    rw [pow_two, delta_eq_sum_indicator]
    simp only [windowIndicator, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  simp_rw [moment, h]
  rw [integral_finsetSum _ (fun d _ => integrable_finsetSum _
    (fun e _ => integrable_windowIndicator_mul (log (d : ℕ)) (log (e : ℕ))))]
  apply Finset.sum_congr rfl
  intro d _
  rw [integral_finsetSum _ (fun e _ => integrable_windowIndicator_mul (log (d : ℕ)) (log (e : ℕ)))]
  simp_rw [integral_windowIndicator_mul]

/-- The diagonal pairs already contribute `τ(n)`. -/
theorem tau_le_moment_two (n : ℕ) : tau n ≤ moment 2 n := by
  rw [moment_two_eq_sum]
  calc
    tau n = ∑ d ∈ n.divisors, (1 : ℝ) := by simp [tau]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d hd
      calc
        (1 : ℝ) = max (1 - |log d - log d|) 0 := by simp
        _ ≤ ∑ e ∈ n.divisors, max (1 - |log d - log e|) 0 :=
          Finset.single_le_sum (fun (e : ℕ) _ => (le_max_right (1 - |log d - log e|) 0)) hd

end BretecheTenenbaumMean
