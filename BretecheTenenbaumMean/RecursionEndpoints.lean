module

public import BretecheTenenbaumMean.SmoothSums
public import BretecheTenenbaumMean.RangeCheck

@[expose] public section

/-! # Endpoint bounds for the moment induction -/

namespace BretecheTenenbaumMean

open Finset Real

theorem primesLT_eq_empty_of_le_two {x : ℝ} (hx : x ≤ 2) : primesLT x = ∅ := by
  apply eq_empty_iff_forall_notMem.2
  intro p hp
  obtain ⟨hp, hpx⟩ := mem_primesLT.1 hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  linarith

theorem expectation_of_le_two {x : ℝ} (hx : x ≤ 2) (f : ℕ → ℝ) : expectation x f = f 1 := by
  simp [expectation, smoothSupport, primeProduct, normalizer, primesLT_eq_empty_of_le_two hx]

theorem truncatedMoment_eq_two_of_le (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ)
    {x : ℝ} (hx : x ≤ 2) : truncatedMoment δ T θ q x = truncatedMoment δ T θ q 2 := by
  unfold truncatedMoment
  rw [expectation_of_le_two hx, expectation_two]

theorem normalizer_log_three_bound : ∃ C > 0, ∀ y : ℝ, 1 ≤ y →
    normalizer y ≤ C * log (3 * y) := by
  obtain ⟨_, C, _, hC, hnormal⟩ := PrimeSums.normalizer_bounds
  refine ⟨C, hC, fun y hy ↦ ?_⟩
  have hm : normalizer y ≤ normalizer (3 * y) := by
    rw [← sum_reciprocal_smoothSupport, ← sum_reciprocal_smoothSupport]
    exact sum_smoothSupport_mono (fun n ↦ by positivity) (by linarith)
  exact hm.trans (hnormal (3 * y) (by linarith)).2

/-- The product estimate (2.17) on the entire smoothing interval. -/
theorem momentProductSum_bound_one : ∃ C > 0, ∀ δ T y (θ : ℕ → ℝ) (q j : ℕ),
    0 ≤ T → 1 ≤ y → 1 ≤ j → j ≤ q - 1 → 0 ≤ θ j →
    momentProductSum δ T θ q j y ≤ C * θ j * T * log (3 * y) ^ 2 *
      truncatedMoment δ T θ (q - j) y * exp (-penalty δ T y) := by
  obtain ⟨C, hC, hnormal⟩ := normalizer_log_three_bound
  refine ⟨C, hC, fun δ T y θ q j hT hy hj hjq hθ ↦ ?_⟩
  have hl : 0 ≤ log (3 * y) := log_nonneg (by linarith)
  have hS : 0 ≤ truncatedMoment δ T θ (q - j) y := by
    apply expectation_nonneg
    intro m _
    exact Set.indicator_nonneg (fun n _ ↦ div_nonneg (moment_nonneg _ _) (Nat.cast_nonneg _)) m
  calc
    _ ≤ θ j * (T * log (3 * y) * exp (-penalty δ T y)) *
        normalizer y * truncatedMoment δ T θ (q - j) y := momentProductSum_le δ hT hy θ hj hjq hθ
    _ ≤ θ j * (T * log (3 * y) * exp (-penalty δ T y)) *
        (C * log (3 * y)) * truncatedMoment δ T θ (q - j) y :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hnormal y hy) (by positivity)) hS
    _ = _ := by ring

end BretecheTenenbaumMean
