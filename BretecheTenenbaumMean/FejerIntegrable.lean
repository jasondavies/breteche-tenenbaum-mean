module

public import BretecheTenenbaumMean.FejerKernel

@[expose] public section

/-! # Integrability of the global frequency kernel -/

namespace BretecheTenenbaumMean

open Real MeasureTheory

/-- The removable singularity in the Fejér kernel agrees with the continuous
sinc convention. -/
theorem fejerKernel_eq_sinc (t : ℝ) : fejerKernel t = sinc (t / 2) ^ 2 / 2 := by
  by_cases ht : t = 0
  · subst t
    norm_num [fejerKernel]
  have ht2 : t / 2 ≠ 0 := by exact div_ne_zero ht (by norm_num)
  rw [fejerKernel, ite_eq_right ht, sinc_of_ne_zero ht2]
  have hc := cos_two_mul (t / 2)
  have hs := cos_sq_add_sin_sq (t / 2)
  have he : 2 * (t / 2) = t := by ring
  rw [he] at hc
  field_simp
  nlinarith

@[fun_prop] theorem continuous_fejerKernel : Continuous fejerKernel := by
  have he : fejerKernel = fun t ↦ sinc (t / 2) ^ 2 / 2 := funext fejerKernel_eq_sinc
  rw [he]
  exact ((continuous_sinc.comp (continuous_id.div_const 2)).pow 2).div_const 2

theorem fejerKernel_le_half (t : ℝ) : fejerKernel t ≤ 1 / 2 := by
  rw [fejerKernel_eq_sinc]
  have h := (sq_le_sq₀ (abs_nonneg (sinc (t / 2))) (by norm_num : (0 : ℝ) ≤ 1)).2
    (abs_sinc_le_one (t / 2))
  rw [sq_abs] at h
  linarith

/-- An integrable majorant valid across the removable singularity. -/
theorem fejerKernel_le_integrable (t : ℝ) : fejerKernel t ≤ 4 * (1 + t ^ 2)⁻¹ := by
  have hd : 0 < 1 + t ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hd]
  by_cases ht : t ^ 2 ≤ 1
  · have h := mul_le_mul_of_nonneg_right (fejerKernel_le_half t) hd.le
    nlinarith
  · have ht0 : t ≠ 0 := by intro he; subst t; norm_num at ht
    have hk : fejerKernel t * t ^ 2 ≤ 2 := by
      rw [fejerKernel, ite_eq_right ht0, div_mul_cancel₀ _ (pow_ne_zero _ ht0)]
      linarith [neg_one_le_cos t]
    nlinarith [fejerKernel_le_half t]

theorem integrable_fejerKernel : Integrable fejerKernel := by
  apply (integrable_inv_one_add_sq.const_mul 4).mono' continuous_fejerKernel.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg t)]
    exact fejerKernel_le_integrable t)

theorem integrable_fejerKernel_cos (a : ℝ) :
    Integrable (fun t ↦ fejerKernel t * cos (t * a)) := by
  apply integrable_fejerKernel.mono'
    (by fun_prop : Continuous (fun t ↦ fejerKernel t * cos (t * a))).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t ↦ by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (fejerKernel_nonneg t)]
    exact mul_le_of_le_one_right (fejerKernel_nonneg t) (abs_cos_le_one _))

end BretecheTenenbaumMean
