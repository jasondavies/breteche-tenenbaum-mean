module

public import BretecheTenenbaumMean.DedekindZetaBounds
public import BretecheTenenbaumMean.DedekindEulerLog

@[expose] public section

/-! # Uniform smoothed reciprocal-prime-ideal sums -/

namespace BretecheTenenbaumMean

open Complex NumberField
open scoped NumberField

/-- Replacing the Euclidean distance to the pole by the sum of its real and
imaginary distances costs at most `log 2`. -/
theorem log_norm_sub_one_comparison {s : ℂ} (hs : 1 < s.re) :
    |Real.log (s.re - 1 + |s.im|) - Real.log ‖s - 1‖| ≤ Real.log 2 := by
  have hs0 : s - 1 ≠ 0 := sub_ne_zero.mpr (fun h ↦ by simp [h] at hs)
  have hn : 0 < ‖s - 1‖ := norm_pos_iff.2 hs0
  have hr : 0 < s.re - 1 := sub_pos.2 hs
  have hdist : 0 < s.re - 1 + |s.im| := by positivity
  have hl : ‖s - 1‖ ≤ s.re - 1 + |s.im| := by
    simpa only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      sub_zero, abs_of_pos hr] using Complex.norm_le_abs_re_add_abs_im (s - 1)
  have hupper : s.re - 1 + |s.im| ≤ 2 * ‖s - 1‖ := by
    have h1 := Complex.re_le_norm (s - 1)
    have h2 := Complex.abs_im_le_norm (s - 1)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h1 h2
    linarith
  have hlogl := Real.log_le_log hn hl
  have hlogu := Real.log_le_log hdist hupper
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn.ne'] at hlogu
  rw [abs_of_nonneg (by linarith : 0 ≤ Real.log (s.re - 1 + |s.im|) - Real.log ‖s - 1‖)]
  linarith

/-- The reciprocal-prime-ideal Dirichlet sum has the logarithmic pole model,
uniformly up to the boundary line and on each fixed bounded height range. -/
theorem primeIdealDirichletSum_log_bound (K : Type*) [Field K] [NumberField K]
    {R : ℝ} (hR : 0 ≤ R) : ∃ B ≥ (0 : ℝ), ∀ s : ℂ,
      1 < s.re → s.re ≤ 2 → |s.im| ≤ R →
      |(∑' P, primeIdealDirichletTerm K s P).re + Real.log (s.re - 1 + |s.im|)| ≤ B := by
  obtain ⟨B, hB, hzeta⟩ := dedekindZeta_log_norm_bound K hR
  let E := ∑' P : IsDedekindDomain.HeightOneSpectrum (𝓞 K), (Ideal.absNorm P.asIdeal : ℝ)⁻¹ ^ 2
  have hE : 0 ≤ E := tsum_nonneg (fun P ↦ sq_nonneg _)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨B + E + Real.log 2, by positivity, fun s hs hs2 him ↦ ?_⟩
  have h1 := hzeta s hs hs2 him
  have h2 := dedekindZeta_log_norm_sub_prime_sum_le K hs
  have h3 := log_norm_sub_one_comparison hs
  let L := Real.log ‖dedekindZeta K s‖
  let P := (∑' P, primeIdealDirichletTerm K s P).re
  let d := Real.log ‖s - 1‖
  let a := Real.log (s.re - 1 + |s.im|)
  have he : P + a = (L + d) - (L - P) + (a - d) := by ring
  change |P + a| ≤ _
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add h1 h2)) h3)

/-- The exact logarithmic profile at the smoothing scale `1/log x`.
This is still an ideal-prime sum; the polynomial root-count correspondence
and removal of the smoothing are separate arithmetic steps. -/
theorem smoothed_primeIdeal_sum_log_ratio (K : Type*) [Field K] [NumberField K] :
    ∃ B ≥ (0 : ℝ), ∀ x θ : ℝ, Real.exp 1 ≤ x → |θ| ≤ 2 →
      |(∑' P, primeIdealDirichletTerm K ((1 + (Real.log x)⁻¹ : ℝ) + θ * I) P).re -
        Real.log (Real.log x / (1 + |θ| * Real.log x))| ≤ B := by
  obtain ⟨B, hB, hbound⟩ := primeIdealDirichletSum_log_bound K (R := 2) (by norm_num)
  refine ⟨B, hB, fun x θ hx hθ ↦ ?_⟩
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hl : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hl0 : 0 < Real.log x := by linarith
  have hinv : 0 < (Real.log x)⁻¹ := inv_pos.2 hl0
  have hinv1 : (Real.log x)⁻¹ ≤ 1 := (inv_le_one₀ hl0).2 hl
  let s : ℂ := (1 + (Real.log x)⁻¹ : ℝ) + θ * I
  have hre : s.re = 1 + (Real.log x)⁻¹ := by simp [s]
  have him : s.im = θ := by simp [s]
  have h := hbound s (by rw [hre]; linarith) (by rw [hre]; linarith) (by rwa [him])
  have he : Real.log (s.re - 1 + |s.im|) =
      -Real.log (Real.log x / (1 + |θ| * Real.log x)) := by
    rw [hre, him]
    have heq : 1 + (Real.log x)⁻¹ - 1 + |θ| =
        (Real.log x / (1 + |θ| * Real.log x))⁻¹ := by
      field_simp
      ring
    rw [heq, Real.log_inv]
  rw [he] at h
  simpa only [sub_eq_add_neg] using h

end BretecheTenenbaumMean
