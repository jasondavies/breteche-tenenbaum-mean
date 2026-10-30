module

public import BretecheTenenbaumMean.WeightedPrimeRecursion
public import BretecheTenenbaumMean.WeightedSmoothSums
public import BretecheTenenbaumMean.RecursionPrimeAverage

@[expose] public section

/-! # Weighted prime averaging for the largest-prime error -/

namespace BretecheTenenbaumMean.WeightedModel

open Finset Real MeasureTheory

/-- The contribution of one largest prime to `V_q(x)-1`. -/
noncomputable def recursionPrimeTerm (w : MultiplicativeWeight) (δ T : ℝ) (θ : ℕ → ℝ) (q p : ℕ) : ℝ :=
  ∑ m ∈ smoothSupport p,
    w p * w m * (momentGoodSet δ T θ (q - 1)).indicator (fun m ↦ mixedRemainder q m p / tau m) m /
      ((m : ℝ) * p)

theorem recursionError_eq_sum (w : MultiplicativeWeight) (δ T x : ℝ) (θ : ℕ → ℝ) (q : ℕ) :
    recursionError w δ T θ q x = 1 + ∑ p ∈ primesLT x, recursionPrimeTerm w δ T θ q p := rfl

theorem recursionPrimeTerm_nonneg (w : MultiplicativeWeight) (δ T : ℝ) (θ : ℕ → ℝ) (q p : ℕ) :
    0 ≤ recursionPrimeTerm w δ T θ q p := by
  apply sum_nonneg
  intro m _
  apply div_nonneg _ (by positivity)
  exact mul_nonneg (mul_nonneg (w.nonneg p) (w.nonneg m))
    (Set.indicator_nonneg (fun n _ ↦ div_nonneg (mixedRemainder_nonneg _ _ _) (Nat.cast_nonneg _)) m)

/-- The pointwise majorant before multiplication by the smoothing measure. -/
noncomputable def recursionAverage (w : MultiplicativeWeight) (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ Icc 1 (q / 2), (q.choose j : ℝ) *
    (1 / log (3 * y) + 2 ^ j / y ^ (1 / 4 : ℝ)) * momentProductSum w δ T θ q j y

theorem recursionAverage_nonneg (w : MultiplicativeWeight) (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    0 ≤ recursionAverage w δ T θ q y := by
  have hL : 0 < log (3 * y) := log_pos (by linarith)
  apply sum_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity))
    (momentProductSum_nonneg w _ _ _ _ _ _)

/-- The prime-averaging estimate summed over the moment good set. The
constant is independent of all good-set, order and cutoff parameters. -/
theorem recursionPrimeTerm_band_bound (w : MultiplicativeWeight) (hpw : PrimeEstimates w) : ∃ C > 0, ∀ δ T (θ : ℕ → ℝ) (q : ℕ),
    2 ≤ q → ∀ y : ℝ, 1 ≤ y → ∀ s : Finset ℕ,
    (∀ p ∈ s, p.Prime ∧ sqrt y ≤ p ∧ (p : ℝ) < y) →
    (∑ p ∈ s, recursionPrimeTerm w δ T θ q p) ≤ C * recursionAverage w δ T θ q y := by
  classical
  obtain ⟨C, hC, hband⟩ := mixedMoment_prime_band_bound
  refine ⟨(hpw.primeBound + 1) * C, mul_pos (by linarith [hpw.primeBound_nonneg]) hC, fun δ T θ q hq y hy s hs ↦ ?_⟩
  let E := momentGoodSet δ T θ (q - 1)
  let g := fun m p : ℕ ↦ E.indicator (fun m ↦ mixedRemainder q m p / tau m) m / ((m : ℝ) * p)
  have hg : ∀ m p, 0 ≤ g m p := by
    intro m p
    apply div_nonneg _ (by positivity)
    exact Set.indicator_nonneg (fun n _ ↦ div_nonneg (mixedRemainder_nonneg _ _ _) (Nat.cast_nonneg _)) m
  have hpoint : ∀ m : ℕ, (∑ p ∈ s, g m p) ≤
      C * ∑ j ∈ Icc 1 (q / 2), (q.choose j : ℝ) *
        (1 / log (3 * y) + 2 ^ j / y ^ (1 / 4 : ℝ)) *
          E.indicator (fun m ↦ moment (q - j) m * moment j m / ((m : ℝ) * tau m)) m := by
    intro m
    by_cases hm : m ∈ E
    · simp only [g, Set.indicator_of_mem hm]
      calc
        _ = ∑ j ∈ Icc 1 (q / 2), (q.choose j : ℝ) *
            (∑ p ∈ s, mixedMoment j q m p / p) / ((m : ℝ) * tau m) := by
          simp only [mixedRemainder, sum_div, mul_sum]
          rw [sum_comm]
          apply sum_congr rfl
          intro j _
          apply sum_congr rfl
          intro p _
          ring
        _ ≤ ∑ j ∈ Icc 1 (q / 2), (q.choose j : ℝ) *
            (C * (1 / log (3 * y) + 2 ^ j / y ^ (1 / 4 : ℝ)) * moment j m * moment (q - j) m) /
              ((m : ℝ) * tau m) := by
          apply sum_le_sum
          intro j hj
          have hj1 := (mem_Icc.1 hj).1
          have hjq : j < q := by have := (mem_Icc.1 hj).2; omega
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hband m q j hj1 hjq y hy s
              (fun p hp ↦ ⟨(hs p hp).1, (hs p hp).2.1, (hs p hp).2.2.le⟩)) (Nat.cast_nonneg _))
            (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        _ = _ := by
          rw [mul_sum]
          apply sum_congr rfl
          intro j _
          ring
    · simp only [g, Set.indicator_of_notMem hm, zero_div, sum_const_zero, mul_zero, le_refl]
  have hwp : ∀ p ∈ s, w p ≤ hpw.primeBound + 1 :=
    fun p hp ↦ (hpw.prime_le p (hs p hp).1).trans (by linarith)
  have hwg : ∀ m p, 0 ≤ w m * g m p :=
    fun m p ↦ mul_nonneg (w.nonneg m) (hg m p)
  calc
    _ ≤ ∑ p ∈ s, (hpw.primeBound + 1) * ∑ m ∈ smoothSupport y, w m * g m p := by
      apply sum_le_sum
      intro p hp
      calc
        _ = w p * ∑ m ∈ smoothSupport p, w m * g m p := by
          rw [mul_sum]
          apply sum_congr rfl
          intro m _
          dsimp only [g, E]
          ring
        _ ≤ (hpw.primeBound + 1) * ∑ m ∈ smoothSupport p, w m * g m p :=
          mul_le_mul_of_nonneg_right (hwp p hp) (sum_nonneg (fun m _ ↦ hwg m p))
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (sum_le_sum_of_subset_of_nonneg (smoothSupport_mono (hs p hp).2.2.le)
            (fun m _ _ ↦ hwg m p)) (by linarith [hpw.primeBound_nonneg])
    _ = (hpw.primeBound + 1) * ∑ m ∈ smoothSupport y, w m * ∑ p ∈ s, g m p := by
      rw [← mul_sum, sum_comm]
      simp_rw [mul_sum]
    _ ≤ (hpw.primeBound + 1) * ∑ m ∈ smoothSupport y, w m * (C *
        ∑ j ∈ Icc 1 (q / 2), (q.choose j : ℝ) *
          (1 / log (3 * y) + 2 ^ j / y ^ (1 / 4 : ℝ)) *
          E.indicator (fun m ↦ moment (q - j) m * moment j m / ((m : ℝ) * tau m)) m) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith [hpw.primeBound_nonneg])
      exact sum_le_sum (fun m _ ↦ mul_le_mul_of_nonneg_left (hpoint m) (w.nonneg m))
    _ = ((hpw.primeBound + 1) * C) * recursionAverage w δ T θ q y := by
      unfold recursionAverage momentProductSum
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro m _
      dsimp only [E]
      ring


end BretecheTenenbaumMean.WeightedModel
