module

public import BretecheTenenbaumMean.PrimeSmoothingTail
public import BretecheTenenbaumMean.WeightedSmoothedRecursion

@[expose] public section

/-! # The weighted integral recurrence -/

namespace BretecheTenenbaumMean.WeightedModel

open Finset Real MeasureTheory

theorem recursionIntegralKernel_div_log (w : MultiplicativeWeight) (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    recursionIntegralKernel w δ T θ q y / log (3 * y) =
      ∑ j ∈ Icc 1 (q / 2), (q.choose j : ℝ) *
        ((1 + 2 ^ j * log (3 * y) / y ^ (1 / 4 : ℝ)) * momentProductSum w δ T θ q j y /
          (y * log (3 * y) ^ 3)) := by
  unfold recursionIntegralKernel logSmoothingWeight recursionAverage
  rw [mul_sum, sum_div]
  apply sum_congr rfl
  intro j _
  have hy0 : 0 < y := by linarith
  have hl : 0 < log (3 * y) := log_pos (by linarith)
  have hr : 0 < y ^ (1 / 4 : ℝ) := rpow_pos_of_pos hy0 _
  generalize hL : log (3 * y) = L at hl ⊢
  field_simp


theorem truncatedMoment_integral_bound (w : MultiplicativeWeight) (hpw : PrimeEstimates w) : ∃ C > 0, ∀ δ T (θ : ℕ → ℝ) (q : ℕ),
    2 ≤ q → ∀ x : ℝ, 2 ≤ x →
    truncatedMoment w δ T θ q x ≤ C * (1 +
      ∫ y in 1..x ^ 2, recursionIntegralKernel w δ T θ q y / log (3 * y)) := by
  classical
  obtain ⟨A, hA, hrec⟩ := truncatedMoment_recursion_bound_unweighted w hpw
  obtain ⟨D, hD, herr⟩ := recursionError_integral_bound w hpw
  obtain ⟨B, hB, hint⟩ := prime_integral_tail_bound
  obtain ⟨E, hE, htail⟩ := PrimeSums.prime_inv_log_tail_bound
  let K : ℝ := (1 + E) / log 2
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨A * (K + D * B), by positivity, fun δ T θ q hq x hx ↦ ?_⟩
  let f := recursionIntegralKernel w δ T θ q
  let I : ℝ := ∫ y in 1..x ^ 2, f y / log (3 * y)
  let J : ℝ := (∫ y in 1..x ^ 2, f y) / log x +
    ∑ p ∈ primesLT x, (∫ y in 1..(p : ℝ) ^ 2, f y) / ((p : ℝ) * log p)
  have hx2 : 1 ≤ x ^ 2 := by nlinarith
  have hlx : 0 < log x := log_pos (by linarith)
  have hI : 0 ≤ I := intervalIntegral.integral_nonneg hx2 (fun y hy ↦
    div_nonneg (recursionIntegralKernel_nonneg w δ T θ q hy.1)
      (log_nonneg (by linarith [hy.1])))
  have hJ : J ≤ B * I := hint x hx f
    (intervalIntegrable_recursionIntegralKernel w δ T θ q hx2)
    (fun y hy ↦ recursionIntegralKernel_nonneg w δ T θ q hy.1)
  have hbase : 1 / log x + (∑ p ∈ primesLT x, 1 / ((p : ℝ) * log p)) ≤ K := by
    have hs := htail 2 le_rfl (primesLT x) (fun p hp ↦
      ⟨(mem_primesLT.1 hp).1, by exact_mod_cast (mem_primesLT.1 hp).1.two_le⟩)
    have hl := one_div_le_one_div_of_le hlog2 (log_le_log (by norm_num) hx)
    dsimp only [K]
    rw [add_div]
    linarith
  have hV : recursionError w δ T θ q x / log x +
      (∑ p ∈ primesLT x, recursionError w δ T θ q p / ((p : ℝ) * log p)) ≤ K + D * J := by
    calc
      _ ≤ (1 + D * ∫ y in 1..x ^ 2, f y) / log x +
          ∑ p ∈ primesLT x, (1 + D * ∫ y in 1..(p : ℝ) ^ 2, f y) / ((p : ℝ) * log p) := by
        apply add_le_add (div_le_div_of_nonneg_right (herr δ T θ q hq x hx) hlx.le)
        apply sum_le_sum
        intro p hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesLT.1 hp).1.two_le
        apply div_le_div_of_nonneg_right (herr δ T θ q hq p hp2)
        have hpl : 0 < log (p : ℝ) := log_pos (by linarith)
        positivity
      _ = (1 / log x + ∑ p ∈ primesLT x, 1 / ((p : ℝ) * log p)) + D * J := by
        dsimp only [J]
        simp only [add_div, mul_div_assoc, sum_add_distrib, ← mul_sum]
        ring
      _ ≤ K + D * J := add_le_add hbase le_rfl
  change _ ≤ A * (K + D * B) * (1 + I)
  calc
    _ ≤ A * (K + D * J) := (hrec δ T θ q x (by omega) hx).trans
      (mul_le_mul_of_nonneg_left hV hA.le)
    _ ≤ A * (K + D * (B * I)) := mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hJ hD.le)) hA.le
    _ ≤ _ := by
      have h : K + D * (B * I) ≤ (K + D * B) * (1 + I) := by
        nlinarith [mul_nonneg hK.le hI]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h hA.le


end BretecheTenenbaumMean.WeightedModel
