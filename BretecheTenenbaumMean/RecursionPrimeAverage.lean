module

public import BretecheTenenbaumMean.PrimeWindowAverage
public import BretecheTenenbaumMean.PrimeSmoothing

@[expose] public section

/-! # Prime averaging of the error in the largest-prime recursion -/

namespace BretecheTenenbaumMean

open Finset Real MeasureTheory

/-- The contribution of one largest prime to `V_q(x)-1`. -/
noncomputable def recursionPrimeTerm (δ T : ℝ) (θ : ℕ → ℝ) (q p : ℕ) : ℝ :=
  ∑ m ∈ smoothSupport p,
    (momentGoodSet δ T θ (q - 1)).indicator (fun m ↦ mixedRemainder q m p / tau m) m /
      ((m : ℝ) * p)

theorem recursionError_eq_sum (δ T x : ℝ) (θ : ℕ → ℝ) (q : ℕ) :
    recursionError δ T θ q x = 1 + ∑ p ∈ primesLT x, recursionPrimeTerm δ T θ q p := rfl

theorem mixedRemainder_nonneg (q n p : ℕ) : 0 ≤ mixedRemainder q n p :=
  sum_nonneg (fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (mixedMoment_nonneg _ _ _ _))

theorem recursionPrimeTerm_nonneg (δ T : ℝ) (θ : ℕ → ℝ) (q p : ℕ) :
    0 ≤ recursionPrimeTerm δ T θ q p := by
  apply sum_nonneg
  intro m _
  apply div_nonneg _ (by positivity)
  exact Set.indicator_nonneg (fun n _ ↦ div_nonneg (mixedRemainder_nonneg _ _ _) (Nat.cast_nonneg _)) m

/-- The pointwise majorant before multiplication by the smoothing measure. -/
noncomputable def recursionAverage (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ Icc 1 (q / 2), (q.choose j : ℝ) *
    (1 / log (3 * y) + 2 ^ j / y ^ (1 / 4 : ℝ)) * momentProductSum δ T θ q j y

theorem recursionAverage_nonneg (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    0 ≤ recursionAverage δ T θ q y := by
  have hL : 0 < log (3 * y) := log_pos (by linarith)
  apply sum_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity))
    (momentProductSum_nonneg _ _ _ _ _ _)

/-- The prime-averaging estimate summed over the moment good set. The
constant is independent of all good-set, order and cutoff parameters. -/
theorem recursionPrimeTerm_band_bound : ∃ C > 0, ∀ δ T (θ : ℕ → ℝ) (q : ℕ),
    2 ≤ q → ∀ y : ℝ, 1 ≤ y → ∀ s : Finset ℕ,
    (∀ p ∈ s, p.Prime ∧ sqrt y ≤ p ∧ (p : ℝ) < y) →
    (∑ p ∈ s, recursionPrimeTerm δ T θ q p) ≤ C * recursionAverage δ T θ q y := by
  classical
  obtain ⟨C, hC, hband⟩ := mixedMoment_prime_band_bound
  refine ⟨C, hC, fun δ T θ q hq y hy s hs ↦ ?_⟩
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
  calc
    _ ≤ ∑ p ∈ s, ∑ m ∈ smoothSupport y, g m p := by
      apply sum_le_sum
      intro p hp
      exact sum_le_sum_of_subset_of_nonneg (smoothSupport_mono (hs p hp).2.2.le) (fun m _ _ ↦ hg m p)
    _ = ∑ m ∈ smoothSupport y, ∑ p ∈ s, g m p := sum_comm
    _ ≤ ∑ m ∈ smoothSupport y, C * ∑ j ∈ Icc 1 (q / 2), (q.choose j : ℝ) *
        (1 / log (3 * y) + 2 ^ j / y ^ (1 / 4 : ℝ)) *
          E.indicator (fun m ↦ moment (q - j) m * moment j m / ((m : ℝ) * tau m)) m :=
      sum_le_sum (fun m _ ↦ hpoint m)
    _ = C * recursionAverage δ T θ q y := by
      rw [← mul_sum, sum_comm]
      unfold recursionAverage momentProductSum
      congr 1
      apply sum_congr rfl
      intro j _
      rw [mul_sum]

end BretecheTenenbaumMean
