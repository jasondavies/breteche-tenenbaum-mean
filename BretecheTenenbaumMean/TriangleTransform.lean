module

public import BretecheTenenbaumMean.FejerIntegrable
public import Mathlib.Analysis.Fourier.Inversion

@[expose] public section

/-! # Fourier transform of the triangular overlap kernel -/

namespace BretecheTenenbaumMean

open Real MeasureTheory Set FourierTransform

noncomputable def triangleKernel (u : ℝ) : ℝ := max (1 - |u|) 0

@[fun_prop] theorem continuous_triangleKernel : Continuous triangleKernel := by
  unfold triangleKernel
  fun_prop

theorem triangleKernel_eq_zero {u : ℝ} (hu : 1 ≤ |u|) : triangleKernel u = 0 := by
  exact max_eq_right (by linarith)

theorem triangleKernel_on_unit {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    triangleKernel u = 1 - u := by
  rw [triangleKernel, abs_of_nonneg hu.1, max_eq_left (by linarith [hu.2])]

@[simp] theorem triangleKernel_neg (u : ℝ) : triangleKernel (-u) = triangleKernel u := by
  simp only [triangleKernel, abs_neg]

theorem triangleKernel_compactSupport : HasCompactSupport triangleKernel := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1))
  intro u hu
  by_contra hn
  have hzero : triangleKernel u = 0 := by
    apply triangleKernel_eq_zero
    have h := not_and_or.mp hn
    rcases h with h | h
    · have := neg_le_abs u
      linarith
    · have := le_abs_self u
      linarith
  exact hu hzero

theorem integrable_triangleKernel : Integrable triangleKernel :=
  continuous_triangleKernel.integrable_of_hasCompactSupport triangleKernel_compactSupport

/-- Splitting the compact support at zero expresses the transform by its
even part. This formula retains the endpoints explicitly. -/
theorem integral_triangle_mul (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ u, (triangleKernel u : ℂ) * f u) =
      ∫ u in (0 : ℝ)..1, ((1 - u : ℝ) : ℂ) * (f u + f (-u)) := by
  let F : ℝ → ℂ := fun u ↦ (triangleKernel u : ℂ) * f u
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hs : ∀ u, u ∉ Ioc (-1 : ℝ) 1 → F u = 0 := by
    intro u hu
    have habs : 1 ≤ |u| := by
      rcases not_and_or.mp hu with h | h
      · have := neg_le_abs u
        linarith
      · have := le_abs_self u
        linarith
    simp [F, triangleKernel_eq_zero habs]
  have hright : (∫ u in (0 : ℝ)..1, F u) =
      ∫ u in (0 : ℝ)..1, ((1 - u : ℝ) : ℂ) * f u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    simp only [F, triangleKernel_on_unit hu]
  have hleft : (∫ u in (-1 : ℝ)..0, F u) =
      ∫ u in (0 : ℝ)..1, ((1 - u : ℝ) : ℂ) * f (-u) := by
    have he := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) F
    simp only [neg_zero] at he
    rw [← he]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    simp only [F, triangleKernel_neg, triangleKernel_on_unit hu]
  calc
    _ = ∫ u in Ioc (-1 : ℝ) 1, F u := (setIntegral_eq_integral_of_forall_compl_eq_zero hs).symm
    _ = ∫ u in (-1 : ℝ)..1, F u := (intervalIntegral.integral_of_le (by norm_num)).symm
    _ = (∫ u in (-1 : ℝ)..0, F u) + ∫ u in (0 : ℝ)..1, F u :=
      (intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable _ _)
        (hF.intervalIntegrable _ _)).symm
    _ = _ := by
      have h1 := (show Continuous (fun u : ℝ ↦ ((1 - u : ℝ) : ℂ) * f (-u)) by fun_prop).intervalIntegrable (μ := volume) 0 1
      have h2 := (show Continuous (fun u : ℝ ↦ ((1 - u : ℝ) : ℂ) * f u) by fun_prop).intervalIntegrable (μ := volume) 0 1
      rw [hleft, hright, ← intervalIntegral.integral_add h1 h2]
      apply intervalIntegral.integral_congr
      intro u _
      ring

/-- The imaginary parts cancel between opposite frequencies. -/
theorem cexp_add_opposite (a : ℝ) :
    Complex.exp ((a : ℂ) * Complex.I) + Complex.exp (((-a : ℝ) : ℂ) * Complex.I) =
      ((2 * cos a : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im, cos_neg, sin_neg] <;> ring

/-- The angular-frequency transform of the triangular overlap function. -/
theorem integral_triangle_exp (t : ℝ) :
    (∫ u, (triangleKernel u : ℂ) * Complex.exp (((u * t : ℝ) : ℂ) * Complex.I)) =
      ((2 * fejerKernel t : ℝ) : ℂ) := by
  rw [integral_triangle_mul _ (by fun_prop)]
  have he : (fun u : ℝ ↦ ((1 - u : ℝ) : ℂ) *
      (Complex.exp (((u * t : ℝ) : ℂ) * Complex.I) +
       Complex.exp (((-u * t : ℝ) : ℂ) * Complex.I))) =
      fun u ↦ ((2 * ((1 - u) * cos (u * t)) : ℝ) : ℂ) := by
    funext u
    rw [neg_mul, cexp_add_opposite]
    push_cast
    ring
  rw [he, intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul, integral_triangular_cos]

/-- Mathlib uses the `2π` Fourier normalization. -/
theorem fourier_triangleKernel (ξ : ℝ) :
    𝓕 (fun u : ℝ ↦ (triangleKernel u : ℂ)) ξ =
      ((2 * fejerKernel (2 * π * ξ) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he : (fun u : ℝ ↦ Complex.exp (((-2 * π * u * ξ : ℝ) : ℂ) * Complex.I) •
      (triangleKernel u : ℂ)) =
      fun u ↦ (triangleKernel u : ℂ) * Complex.exp (((u * (-(2 * π * ξ)) : ℝ) : ℂ) * Complex.I) := by
    funext u
    rw [smul_eq_mul, mul_comm]
    congr 2
    push_cast
    ring
  rw [he, integral_triangle_exp]
  congr 2
  simp [fejerKernel, cos_neg]

end BretecheTenenbaumMean
