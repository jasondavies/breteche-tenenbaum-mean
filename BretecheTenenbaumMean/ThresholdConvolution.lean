module

public import BretecheTenenbaumMean.Targets

@[expose] public section

/-! # The threshold convolution in the moment induction -/

namespace BretecheTenenbaumMean

open Finset

noncomputable def thresholdConvolution (θ : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 (q / 2), (q.choose j : ℝ) * θ j * θ (q - j)

theorem thresholdConvolution_nonneg {θ : ℕ → ℝ} (hθ : ∀ j, 0 ≤ θ j) (q : ℕ) :
    0 ≤ thresholdConvolution θ q :=
  sum_nonneg (fun j _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hθ j)) (hθ _))

theorem thresholdConvolution_one_le {θ : ℕ → ℝ} (hθ : ∀ j, 0 ≤ θ j)
    {q : ℕ} (hq : 2 ≤ q) : (q : ℝ) * θ 1 * θ (q - 1) ≤ thresholdConvolution θ q := by
  have h := single_le_sum (s := Icc 1 (q / 2))
    (f := fun j ↦ (q.choose j : ℝ) * θ j * θ (q - j))
    (fun j _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hθ j)) (hθ _))
    (show 1 ∈ Icc 1 (q / 2) by simp only [mem_Icc]; omega)
  simpa only [Nat.choose_one_right, thresholdConvolution] using h

/-- The geometric error in (2.16) is controlled by the first convolution term. -/
theorem threshold_geometric_error_le {θ : ℕ → ℝ} (hθ : ∀ j, 0 ≤ θ j)
    (hθ1 : 1 ≤ θ 1) {q : ℕ} (hq : 3 ≤ q) :
    θ (q - 1) / 2 ^ q ≤ thresholdConvolution θ q / (q : ℝ) ^ 2 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqpow : (q : ℝ) ≤ 2 ^ q := by exact_mod_cast (Nat.lt_two_pow_self (n := q)).le
  have hfirst : (q : ℝ) * θ (q - 1) ≤ thresholdConvolution θ q := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hθ1 hq0.le) (hθ (q - 1))
    simpa only [mul_one] using h.trans (thresholdConvolution_one_le hθ (by omega))
  calc
    _ ≤ θ (q - 1) / q := div_le_div_of_nonneg_left (hθ _) hq0 hqpow
    _ ≤ _ := by
      apply (div_le_div_iff₀ hq0 (sq_pos_of_pos hq0)).2
      have h := mul_le_mul_of_nonneg_left hfirst hq0.le
      nlinarith

end BretecheTenenbaumMean
