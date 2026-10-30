module

public import BretecheTenenbaumMean.TriangleTransform

@[expose] public section

/-! # Global cosine transform of the Fejér kernel -/

namespace BretecheTenenbaumMean

open Real MeasureTheory FourierTransform

/-- Fourier inversion for the triangle, before changing frequency variables. -/
theorem integral_scaled_fejer_cos (a : ℝ) :
    (∫ ξ : ℝ, 2 * fejerKernel (2 * π * ξ) * cos (2 * π * ξ * a)) = triangleKernel a := by
  let f : ℝ → ℂ := fun u ↦ (triangleKernel u : ℂ)
  have hf : Integrable f := integrable_triangleKernel.ofReal
  have hb : Integrable (fun ξ : ℝ ↦ 2 * fejerKernel (2 * π * ξ)) :=
    (integrable_fejerKernel.comp_mul_left' (show 2 * π ≠ 0 by positivity)).const_mul 2
  have hft : Integrable (𝓕 f) := by
    have he : 𝓕 f = fun ξ : ℝ ↦ ((2 * fejerKernel (2 * π * ξ) : ℝ) : ℂ) :=
      funext fourier_triangleKernel
    rw [he]
    exact hb.ofReal
  have hinv := hf.fourierInv_fourier_eq hft
    (show ContinuousAt f a by dsimp [f]; fun_prop)
  rw [Real.fourierInv_eq'] at hinv
  simp only [f, fourier_triangleKernel, smul_eq_mul, real_inner_comm] at hinv
  have hI : Integrable (fun ξ : ℝ ↦
      Complex.exp (((2 * π * ξ * a : ℝ) : ℂ) * Complex.I) *
        ((2 * fejerKernel (2 * π * ξ) : ℝ) : ℂ)) := by
    apply hb.mono' (by fun_prop)
    exact Filter.Eventually.of_forall (fun ξ ↦ by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) (fejerKernel_nonneg _))])
  have heq : (∫ ξ : ℝ,
      Complex.exp (((2 * π * ξ * a : ℝ) : ℂ) * Complex.I) *
        ((2 * fejerKernel (2 * π * ξ) : ℝ) : ℂ)) = (triangleKernel a : ℂ) := by
    convert hinv using 1
    congr 1
    funext ξ
    congr 2
    simp
    ring
  have hre := (Complex.reCLM.integral_comp_comm hI).trans (congrArg Complex.re heq)
  convert hre using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ξ ↦ by
    simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.exp_ofReal_mul_I_re]
    ring)

/-- The global angular-frequency cosine transform, with its exact factor `π`. -/
theorem integral_fejer_cos (a : ℝ) :
    (∫ θ : ℝ, fejerKernel θ * cos (θ * a)) = π * triangleKernel a := by
  have h := integral_scaled_fejer_cos a
  have he : (fun ξ : ℝ ↦ 2 * fejerKernel (2 * π * ξ) * cos (2 * π * ξ * a)) =
      fun ξ ↦ 2 * (fejerKernel (2 * π * ξ) * cos ((2 * π * ξ) * a)) := by
    funext ξ
    ring
  rw [he, integral_const_mul,
    Measure.integral_comp_mul_left (fun θ : ℝ ↦ fejerKernel θ * cos (θ * a)) (2 * π)] at h
  simp only [smul_eq_mul, abs_of_pos (inv_pos.2 (show 0 < 2 * π by positivity))] at h
  have hπ := pi_pos
  field_simp at h
  nlinarith

/-- The sinc-squared kernel in (2.6), including its removable singularity. -/
theorem integral_sinc_sq_cos (a : ℝ) :
    (∫ θ : ℝ, sinc (θ / 2) ^ 2 * cos (θ * a)) = 2 * π * triangleKernel a := by
  have he : (fun θ : ℝ ↦ sinc (θ / 2) ^ 2 * cos (θ * a)) =
      fun θ ↦ 2 * (fejerKernel θ * cos (θ * a)) := by
    funext θ
    rw [fejerKernel_eq_sinc]
    ring
  rw [he, integral_const_mul, integral_fejer_cos]
  ring

end BretecheTenenbaumMean
