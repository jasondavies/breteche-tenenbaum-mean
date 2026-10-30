module

public import BretecheTenenbaumMean.FiniteTailExpectation
public import BretecheTenenbaumMean.WeightedEventBounds

@[expose] public section

/-! # Finite tail sums in the weighted probability model -/

namespace BretecheTenenbaumMean.WeightedModel

open Finset Real

theorem expectation_const (w : MultiplicativeWeight) (x c : ℝ) : expectation w x (fun _ ↦ c) = c := by
  have h := expectation_const_mul w x c (fun _ ↦ 1)
  simpa only [mul_one, expectation_one w] using h


theorem expectation_finset_sum (w : MultiplicativeWeight) (x : ℝ) (s : Finset ℕ) (f : ℕ → ℕ → ℝ) :
    expectation w x (fun n ↦ ∑ j ∈ s, f j n) = ∑ j ∈ s, expectation w x (f j) := by
  unfold expectation
  rw [← sum_div]
  congr 1
  simp_rw [mul_sum, sum_div]
  exact sum_comm


theorem expectation_div_const (w : MultiplicativeWeight) (x c : ℝ) (f : ℕ → ℝ) :
    expectation w x (fun n ↦ f n / c) = expectation w x f / c := by
  simpa only [div_eq_mul_inv, mul_comm] using expectation_const_mul w x c⁻¹ f


theorem expectation_le_finite_tails (w : MultiplicativeWeight) (x : ℝ) (f : ℕ → ℝ) (hf : ∀ n ∈ smoothSupport x, 0 ≤ f n)
    (R : ℕ → ℝ) (N : ℕ) (hR : ∀ j, 0 ≤ R j) (hRN : 0 < R N) :
    expectation w x f ≤ R 0 + (∑ j ∈ range N, R (j + 1) * probability w x {n | R j < f n}) +
      expectation w x (fun n ↦ f n ^ 2) / R N := by
  classical
  have h := expectation_mono w x (f := f)
    (g := fun n ↦ R 0 +
      (∑ j ∈ range N, R (j + 1) * ({m | R j < f m}).indicator (fun _ ↦ (1 : ℝ)) n) + f n ^ 2 / R N)
    (fun n hn ↦ by simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using
      le_finite_tail_majorant (hf n hn) R N hR hRN)
  rw [expectation_add w, expectation_add w, expectation_const w, expectation_finset_sum w, expectation_div_const w] at h
  simp_rw [expectation_const_mul w] at h
  exact h


end BretecheTenenbaumMean.WeightedModel
