module

public import BretecheTenenbaumMean.ThresholdConvolution
public import Mathlib.NumberTheory.ZetaValues

@[expose] public section

/-! # The inverse-square sum controlling the threshold convolution -/

namespace BretecheTenenbaumMean

open Finset Real

theorem sum_inv_sq_le_pi_sq_div_six (s : Finset ℕ) :
    (∑ j ∈ s, 1 / (j : ℝ) ^ 2) ≤ π ^ 2 / 6 :=
  sum_le_hasSum s (fun j _ ↦ by positivity) hasSum_zeta_two

theorem half_inverse_square_convolution_bound {q : ℕ} (hq : 2 ≤ q) :
    (∑ j ∈ Icc 1 (q / 2), 1 / ((j : ℝ) ^ 2 * ((q - j : ℕ) : ℝ) ^ 2)) ≤
      (2 * π ^ 2 / 3) / (q : ℝ) ^ 2 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  calc
    _ ≤ ∑ j ∈ Icc 1 (q / 2), (4 / (q : ℝ) ^ 2) * (1 / (j : ℝ) ^ 2) := by
      apply sum_le_sum
      intro j hj
      obtain ⟨hj, hjq⟩ := mem_Icc.1 hj
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
      have hk0 : (0 : ℝ) < (q - j : ℕ) := by exact_mod_cast (show 0 < q - j by omega)
      have hqk : (q : ℝ) ≤ 2 * (q - j : ℕ) := by exact_mod_cast (show q ≤ 2 * (q - j) by omega)
      have hdiv : 1 / ((q - j : ℕ) : ℝ) ^ 2 ≤ 4 / (q : ℝ) ^ 2 := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hk0) (sq_pos_of_pos hq0)).2
        nlinarith
      have h := mul_le_mul_of_nonneg_right hdiv (by positivity : 0 ≤ 1 / (j : ℝ) ^ 2)
      convert h using 1; ring
    _ = (4 / (q : ℝ) ^ 2) * ∑ j ∈ Icc 1 (q / 2), 1 / (j : ℝ) ^ 2 := (mul_sum ..).symm
    _ ≤ (4 / (q : ℝ) ^ 2) * (π ^ 2 / 6) :=
      mul_le_mul_of_nonneg_left (sum_inv_sq_le_pi_sq_div_six _) (by positivity)
    _ = _ := by ring

end BretecheTenenbaumMean
