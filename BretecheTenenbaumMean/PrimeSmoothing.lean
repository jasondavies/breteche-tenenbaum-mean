module

public import BretecheTenenbaumMean.LogarithmicPenaltyIntegral
public import BretecheTenenbaumMean.SmoothSums

@[expose] public section

/-! # Smoothing a prime term over the interval `(p,p²]` -/

namespace BretecheTenenbaumMean

open Finset Real MeasureTheory

noncomputable def logSmoothingWeight (y : ℝ) : ℝ := 1 / (y * log (3 * y))

theorem logSmoothingWeight_pos {y : ℝ} (hy : 1 ≤ y) : 0 < logSmoothingWeight y := by
  unfold logSmoothingWeight
  have hL : 0 < log (3 * y) := log_pos (by linarith)
  positivity

theorem continuousOn_logSmoothingWeight {a b : ℝ} (ha : 1 ≤ a) :
    ContinuousOn logSmoothingWeight (Set.Icc a b) := by
  intro y hy
  have hy0 : 0 < y := by linarith [hy.1]
  have hL : 0 < log (3 * y) := log_pos (by linarith [hy.1])
  apply ContinuousAt.continuousWithinAt
  unfold logSmoothingWeight
  fun_prop (disch := positivity)

/-- The smoothing measure gives every prime interval a fixed positive mass. -/
theorem log_smoothing_integral_ge {p : ℝ} (hp : 2 ≤ p) :
    1 / 4 ≤ ∫ y in p..p ^ 2, logSmoothingWeight y := by
  have hp0 : 0 < p := by linarith
  have hpp : p ≤ p ^ 2 := by nlinarith
  have hlogp : 0 < log p := log_pos (by linarith)
  have hlog3 : 0 < log 3 := log_pos (by norm_num)
  have hcomp : log 3 ≤ 2 * log p := by
    have h := log_le_log (by norm_num : (0 : ℝ) < 3) (show 3 ≤ p ^ 2 by nlinarith)
    simpa only [log_pow, Nat.cast_ofNat] using h
  have hint : IntervalIntegrable logSmoothingWeight volume p (p ^ 2) := (continuousOn_logSmoothingWeight (by linarith : 1 ≤ p)).intervalIntegrable_of_Icc hpp
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y : ℝ ↦ log (log (3 * y)))
    (fun y hy ↦ hasDerivAt_loglog_three_mul (by
      rw [Set.uIcc_of_le hpp] at hy
      linarith [hy.1])) hint
  change 1 / 4 ≤ ∫ y in p..p ^ 2, 1 / (y * log (3 * y))
  rw [he, log_mul (by norm_num : (3 : ℝ) ≠ 0) (pow_ne_zero 2 hp0.ne'),
    log_mul (by norm_num : (3 : ℝ) ≠ 0) hp0.ne', log_pow]
  norm_num only [Nat.cast_ofNat]
  rw [← log_div (by positivity : log 3 + 2 * log p ≠ 0) (by positivity : log 3 + log p ≠ 0)]
  have hratio : (4 / 3 : ℝ) ≤ (log 3 + 2 * log p) / (log 3 + log p) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith
  have hfour : (1 / 4 : ℝ) ≤ log (4 / 3) := by
    have h := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    norm_num at h ⊢
    exact h
  exact hfour.trans (log_le_log (by norm_num) hratio)

/-- A prime contribution spread over its smoothing interval. -/
noncomputable def smoothedPrimeTerm (A : ℕ → ℝ) (p : ℕ) (y : ℝ) : ℝ :=
  (Set.Ioc (p : ℝ) ((p : ℝ) ^ 2)).indicator (fun y ↦ A p * logSmoothingWeight y) y

theorem integrable_smoothedPrimeTerm (A : ℕ → ℝ) {p : ℕ} (hp : p.Prime) :
    Integrable (smoothedPrimeTerm A p) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpp : (p : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
  apply IntegrableOn.integrable_indicator _ measurableSet_Ioc
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hpp).1
  exact ((continuousOn_logSmoothingWeight (by linarith : (1 : ℝ) ≤ p)).intervalIntegrable_of_Icc hpp).const_mul _

theorem integral_smoothedPrimeTerm {x : ℝ} (hx : 2 ≤ x) (A : ℕ → ℝ)
    {p : ℕ} (hp : p ∈ primesLT x) :
    (∫ y in 1..x ^ 2, smoothedPrimeTerm A p y) =
      A p * ∫ y in (p : ℝ)..(p : ℝ) ^ 2, logSmoothingWeight y := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesLT.1 hp).1.two_le
  have hpx := (mem_primesLT.1 hp).2
  have hpp : (p : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
  rw [intervalIntegral.integral_eq_integral_of_support_subset]
  · simp only [smoothedPrimeTerm]
    rw [integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le hpp, intervalIntegral.integral_const_mul]
  · intro y hy
    have hmem : y ∈ Set.Ioc (p : ℝ) ((p : ℝ) ^ 2) := by
      by_contra h
      exact hy (Set.indicator_of_notMem h _)
    exact ⟨by linarith [hmem.1], hmem.2.trans (by nlinarith)⟩

/-- A finite prime sum is bounded by four times its smoothed integral. -/
theorem prime_sum_le_smoothed_integral {x : ℝ} (hx : 2 ≤ x) (A : ℕ → ℝ)
    (hA : ∀ p ∈ primesLT x, 0 ≤ A p) :
    (∑ p ∈ primesLT x, A p) ≤
      4 * ∫ y in 1..x ^ 2, ∑ p ∈ primesLT x, smoothedPrimeTerm A p y := by
  rw [intervalIntegral.integral_finsetSum (fun p hp ↦
    (integrable_smoothedPrimeTerm A (mem_primesLT.1 hp).1).intervalIntegrable), mul_sum]
  apply sum_le_sum
  intro p hp
  rw [integral_smoothedPrimeTerm hx A hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesLT.1 hp).1.two_le
  have h := mul_le_mul_of_nonneg_left (log_smoothing_integral_ge hp2) (hA p hp)
  nlinarith

end BretecheTenenbaumMean
