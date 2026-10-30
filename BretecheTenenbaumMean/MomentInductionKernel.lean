module

public import BretecheTenenbaumMean.InductionProducts
public import BretecheTenenbaumMean.RecursionKernels
public import BretecheTenenbaumMean.LogarithmicPenaltyIntegral

@[expose] public section

/-! # The integrated induction step for the main recursion kernel -/

namespace BretecheTenenbaumMean

open Finset Real MeasureTheory

/-- Pointwise induction, including the exceptional midpoint at order four. -/
theorem recursionMainKernel_induction_bound : ∃ C > 0,
    ∀ δ T (θ : ℕ → ℝ) (K : ℝ) (q : ℕ), 0 < T → 0 ≤ K →
    (∀ i, 0 ≤ θ i) → 4 ≤ q →
    (∀ k : ℕ, 3 ≤ k → k < q → ∀ x : ℝ, 2 ≤ x →
      truncatedMoment δ T θ k x ≤ K * θ k / (k : ℝ) ^ 2 / T) →
    ∀ y : ℝ, 1 ≤ y → recursionMainKernel δ T θ q y ≤
      C * K / (q : ℝ) ^ 2 * thresholdConvolution θ q *
        (exp (-penalty δ T y) / (y * log (3 * y))) := by
  obtain ⟨A, hA, hZ⟩ := momentProductSum_induction_bound
  refine ⟨3 * A, by positivity, fun δ T θ K q hT hK hθ hq hIH y hy ↦ ?_⟩
  have hy0 : 0 < y := by linarith
  have hL : 0 < log (3 * y) := log_pos (by linarith)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  let g := exp (-penalty δ T y) / (y * log (3 * y))
  have hg : 0 ≤ g := by dsimp only [g]; positivity
  have hconv := thresholdConvolution_nonneg hθ q
  have hp : ∀ j : ℕ, 1 ≤ j → j ≤ q / 2 → 3 ≤ q - j →
      (q.choose j : ℝ) * momentProductSum δ T θ q j y / (y * log (3 * y) ^ 3) ≤
      A * K / (q : ℝ) ^ 2 * ((q.choose j : ℝ) * θ j * θ (q - j)) * g := by
    intro j hj hjq hk
    have hb := hZ δ T θ K q j hT hK hθ hj hjq hk
      (hIH (q - j) hk (by omega)) y hy
    calc
      _ ≤ (q.choose j : ℝ) *
          (A * K * θ j * θ (q - j) / (q : ℝ) ^ 2 * log (3 * y) ^ 2 * exp (-penalty δ T y)) /
          (y * log (3 * y) ^ 3) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)) (by positivity)
      _ = _ := by
        dsimp only [g]
        generalize hlog : log (3 * y) = L at hL ⊢
        field_simp
  by_cases hq4 : q = 4
  · subst q
    have he : recursionMainKernel δ T θ 4 y =
        4 * momentProductSum δ T θ 4 1 y / (y * log (3 * y) ^ 3) +
        6 * momentProductSum δ T θ 4 2 y / (y * log (3 * y) ^ 3) := by
      unfold recursionMainKernel
      rw [show Icc 1 (4 / 2) = ({1, 2} : Finset ℕ) by decide]
      norm_num [Nat.choose]
    have hmid := momentProductSum_four_two_le δ T y θ
    have hZ0 := momentProductSum_nonneg δ T θ 4 1 y
    have hm : recursionMainKernel δ T θ 4 y ≤
        3 * (4 * momentProductSum δ T θ 4 1 y / (y * log (3 * y) ^ 3)) := by
      rw [he]
      have hd : 0 < y * log (3 * y) ^ 3 := by positivity
      have hh := div_le_div_of_nonneg_right hmid hd.le
      have hz := div_nonneg hZ0 hd.le
      simp only [mul_div_assoc]
      nlinarith
    have h1 := hp 1 (by norm_num) (by norm_num) (by norm_num)
    norm_num only [Nat.choose_one_right, Nat.cast_ofNat, Nat.reduceSub, Nat.reducePow] at h1
    have hc := thresholdConvolution_one_le hθ (q := 4) (by norm_num)
    norm_num only [Nat.cast_ofNat, Nat.reduceSub] at hc
    calc
      _ ≤ 3 * (4 * momentProductSum δ T θ 4 1 y / (y * log (3 * y) ^ 3)) := hm
      _ ≤ 3 * (A * K / 16 * (4 * θ 1 * θ 3) * g) := mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ ≤ 3 * (A * K / 16 * thresholdConvolution θ 4 * g) := by
        gcongr
      _ = _ := by norm_num; ring
  · have hq5 : 5 ≤ q := by omega
    have hs : recursionMainKernel δ T θ q y ≤
        A * K / (q : ℝ) ^ 2 * thresholdConvolution θ q * g := by
      calc
        _ ≤ ∑ j ∈ Icc 1 (q / 2), A * K / (q : ℝ) ^ 2 *
            ((q.choose j : ℝ) * θ j * θ (q - j)) * g := by
          apply sum_le_sum
          intro j hj
          obtain ⟨hj, hjq⟩ := mem_Icc.1 hj
          exact hp j hj hjq (by omega)
        _ = _ := by rw [← sum_mul, ← mul_sum]; rfl
    have hnonneg : 0 ≤ A * K / (q : ℝ) ^ 2 * thresholdConvolution θ q * g := by positivity
    calc
      _ ≤ A * K / (q : ℝ) ^ 2 * thresholdConvolution θ q * g := hs
      _ ≤ 3 * (A * K / (q : ℝ) ^ 2 * thresholdConvolution θ q * g) := by linarith
      _ = _ := by ring

/-- Integrating the induction step costs only `sqrt(log T)`. -/
theorem recursionMain_integral_induction_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ T (θ : ℕ → ℝ) (K : ℝ) (q : ℕ), 3 ≤ T → 0 ≤ K →
    (∀ i, 0 ≤ θ i) → 4 ≤ q →
    (∀ k : ℕ, 3 ≤ k → k < q → ∀ x : ℝ, 2 ≤ x →
      truncatedMoment δ T θ k x ≤ K * θ k / (k : ℝ) ^ 2 / T) →
    ∀ X : ℝ, 1 ≤ X →
    (∫ y in 1..X, recursionMainKernel δ T θ q y) ≤
      C * K * sqrt (log T) / (q : ℝ) ^ 2 * thresholdConvolution θ q := by
  obtain ⟨C, hC, hpoint⟩ := recursionMainKernel_induction_bound
  let D := 1 / δ + sqrt (π / δ)
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨C * D, mul_pos hC hD, fun T θ K q hT hK hθ hq hIH X hX ↦ ?_⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hconv := thresholdConvolution_nonneg hθ q
  have hc : ContinuousOn (fun y : ℝ ↦ exp (-penalty δ T y) / (y * log (3 * y)))
      (Set.uIcc 1 X) := by
    rw [Set.uIcc_of_le hX]
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    have hL : 0 < log (3 * y) := log_pos (by linarith [hy.1])
    apply ContinuousAt.continuousWithinAt
    unfold penalty
    fun_prop (disch := positivity)
  have hi := intervalIntegral.integral_mono_on hX
    (intervalIntegrable_recursionMainKernel δ T θ q hX)
    (hc.intervalIntegrable.const_mul (C * K / (q : ℝ) ^ 2 * thresholdConvolution θ q))
    (fun y hy ↦ hpoint δ T θ K q (by linarith) hK hθ hq hIH y hy.1)
  rw [intervalIntegral.integral_const_mul] at hi
  have hp := logarithmic_penalty_integral_bound hδ hT hX
  have hm := mul_le_mul_of_nonneg_left hp
    (by positivity : 0 ≤ C * K / (q : ℝ) ^ 2 * thresholdConvolution θ q)
  convert hi.trans hm using 1
  dsimp only [D]
  ring

end BretecheTenenbaumMean
