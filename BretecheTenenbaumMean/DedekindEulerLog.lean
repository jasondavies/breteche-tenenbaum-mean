module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial
public import Mathlib.NumberTheory.EulerProduct.ExpLog

@[expose] public section

/-! # The first-prime term of the Dedekind Euler logarithm

Taking the real part of the exponential Euler-product identity avoids any
choice of logarithm branch for the zeta function itself. The omitted higher
prime powers have a uniformly summable reciprocal-square majorant.
-/

namespace BretecheTenenbaumMean

open Complex NumberField TauCeti IsDedekindDomain
open scoped NumberField

noncomputable def primeIdealDirichletTerm (K : Type*) [Field K] [NumberField K]
    (s : ℂ) (P : HeightOneSpectrum (𝓞 K)) : ℂ :=
  1 / (Ideal.absNorm P.asIdeal : ℂ) ^ s

theorem summable_primeIdealDirichletTerm (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) : Summable (primeIdealDirichletTerm K s) := by
  have hi : Summable (idealTerm K (1 : MultiplicativeIdealWeight K).toIdealArithmeticFunction s) := by
    rw [MultiplicativeIdealWeight.toIdealArithmeticFunction_one]
    exact summable_idealTerm_one_iff.mpr hs
  refine ((1 : MultiplicativeIdealWeight K).summable_div_of_summable_idealTerm hi).congr ?_
  intro P
  rw [MultiplicativeIdealWeight.one_apply, ite_eq_right P.ne_bot]
  rfl

theorem primeIdealDirichletTerm_norm_le (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 ≤ s.re) (P : HeightOneSpectrum (𝓞 K)) :
    ‖primeIdealDirichletTerm K s P‖ ≤ (Ideal.absNorm P.asIdeal : ℝ)⁻¹ := by
  have hp := NumberField.HeightOneSpectrum.one_lt_absNorm P
  have hp0 : 0 < (Ideal.absNorm P.asIdeal : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hp)
  rw [primeIdealDirichletTerm, norm_div, norm_one,
    Complex.norm_natCast_cpow_of_pos (by omega)]
  rw [inv_eq_one_div]
  apply one_div_le_one_div_of_le hp0
  simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.le) hs

theorem summable_primeIdeal_reciprocal_sq (K : Type*) [Field K] [NumberField K] :
    Summable (fun P : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm P.asIdeal : ℝ)⁻¹ ^ 2) := by
  have h := (summable_primeIdealDirichletTerm K (s := 2) (by norm_num)).norm
  refine h.congr ?_
  intro P
  simp [primeIdealDirichletTerm, norm_pow, inv_pow]

/-- The local logarithm differs from its linear term by a reciprocal square. -/
theorem primeIdeal_log_error_le (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 ≤ s.re) (P : HeightOneSpectrum (𝓞 K)) :
    ‖-Complex.log (1 - primeIdealDirichletTerm K s P) - primeIdealDirichletTerm K s P‖ ≤
      (Ideal.absNorm P.asIdeal : ℝ)⁻¹ ^ 2 := by
  let z := primeIdealDirichletTerm K s P
  have hz := primeIdealDirichletTerm_norm_le K hs P
  have hp2 : (2 : ℝ) ≤ Ideal.absNorm P.asIdeal := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm P)
  have hhalf : ‖z‖ ≤ 1 / 2 := hz.trans (by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hp2)
  have hpos : 0 < 1 - ‖z‖ := by linarith
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 2)]
    norm_num
    linarith
  have h := Complex.norm_log_one_add_sub_self_le (z := -z) (by rw [norm_neg]; linarith)
  have he : -Complex.log (1 - z) - z = -(Complex.log (1 + -z) - -z) := by
    rw [sub_eq_add_neg (1 : ℂ) z]
    ring
  change ‖-Complex.log (1 - z) - z‖ ≤ _
  rw [he, norm_neg]
  simp only [norm_neg] at h
  calc
    _ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := h
    _ ≤ ‖z‖ ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hinv (sq_nonneg ‖z‖)]
    _ ≤ _ := pow_le_pow_left₀ (norm_nonneg _) hz 2

/-- The exact real part of the logarithmic Euler product. -/
theorem dedekindZeta_log_norm_eq_prime_logs (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    Real.log ‖dedekindZeta K s‖ =
      (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - primeIdealDirichletTerm K s P)).re := by
  have hi : Summable (idealTerm K (1 : MultiplicativeIdealWeight K).toIdealArithmeticFunction s) := by
    rw [MultiplicativeIdealWeight.toIdealArithmeticFunction_one]
    exact summable_idealTerm_one_iff.mpr hs
  have h := (1 : MultiplicativeIdealWeight K).exp_tsum_neg_log_one_sub_eq_LSeries hi
  have hf (P : HeightOneSpectrum (𝓞 K)) :
      (1 : MultiplicativeIdealWeight K) P.asIdeal / (Ideal.absNorm P.asIdeal : ℂ) ^ s =
        primeIdealDirichletTerm K s P := by
    rw [MultiplicativeIdealWeight.one_apply, ite_eq_right P.ne_bot]
    rfl
  simp_rw [hf] at h
  rw [MultiplicativeIdealWeight.toIdealArithmeticFunction_one,
    ← dedekindZeta_eq_LSeries_normCoeff_one K s] at h
  have hn := congrArg (fun z : ℂ ↦ Real.log ‖z‖) h
  rw [Complex.norm_exp, Real.log_exp] at hn
  exact hn.symm

/-- The higher prime powers contribute a constant independent of `s` on
`Re s>1`. The constant is the convergent prime-ideal reciprocal-square sum. -/
theorem dedekindZeta_log_norm_sub_prime_sum_le (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    |Real.log ‖dedekindZeta K s‖ - (∑' P, primeIdealDirichletTerm K s P).re| ≤
      ∑' P : HeightOneSpectrum (𝓞 K), (Ideal.absNorm P.asIdeal : ℝ)⁻¹ ^ 2 := by
  have hz := summable_primeIdealDirichletTerm K hs
  have hlog : Summable (fun P ↦ -Complex.log (1 - primeIdealDirichletTerm K s P)) :=
    (Summable.clog_one_sub hz).neg
  have hd := hlog.sub hz
  rw [dedekindZeta_log_norm_eq_prime_logs K hs, ← Complex.sub_re, ← hlog.tsum_sub hz]
  refine (Complex.abs_re_le_norm _).trans ?_
  exact (norm_tsum_le_tsum_norm hd.norm).trans
    (hd.norm.tsum_le_tsum (primeIdeal_log_error_le K hs.le) (summable_primeIdeal_reciprocal_sq K))

end BretecheTenenbaumMean
