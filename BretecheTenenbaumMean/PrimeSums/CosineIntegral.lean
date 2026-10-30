module

public import BretecheTenenbaumMean.PrimeSums.Cosine
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-! # Uniform estimates for the cosine integral in the prime-sum formula -/

open Real MeasureTheory intervalIntegral

namespace BretecheTenenbaumMean.PrimeSums

theorem intervalIntegrable_cos_div (ψ : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t ↦ cos (ψ * t) / t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div (by fun_prop) continuousOn_id
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  change t ≠ 0
  linarith [ht.1]

/-- On the low-frequency range, replacing the cosine by one costs at most one. -/
theorem cosineIntegral_low {ψ a b : ℝ} (hψ : 0 ≤ ψ) (ha : 0 < a)
    (hab : a ≤ b) (hb : ψ * b ≤ 1) :
    |(∫ t in a..b, cos (ψ * t) / t) - (log b - log a)| ≤ 1 := by
  have hb0 : 0 < b := ha.trans_le hab
  have hi : IntervalIntegrable (fun t : ℝ ↦ t⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ continuousOn_id
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    change t ≠ 0
    linarith [ht.1]
  have he : (∫ t in a..b, t⁻¹) = log b - log a := by
    rw [integral_inv_of_pos ha hb0, log_div hb0.ne' ha.ne']
  rw [← he, ← integral_sub (intervalIntegrable_cos_div ψ ha hab) hi, ← norm_eq_abs]
  have h := norm_integral_le_of_norm_le_const (a := a) (b := b)
    (f := fun t ↦ cos (ψ * t) / t - t⁻¹) (C := ψ) (by
      intro t ht
      rw [Set.uIoc_of_le hab] at ht
      have ht0 : 0 < t := ha.trans ht.1
      rw [norm_eq_abs, show cos (ψ * t) / t - t⁻¹ = (cos (ψ * t) - 1) / t by ring,
        abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
      have hc := abs_cos_sub_cos_le (ψ * t) 0
      simpa only [cos_zero, sub_zero, abs_of_nonneg (mul_nonneg hψ ht0.le)] using hc)
  refine h.trans ?_
  rw [abs_of_nonneg (sub_nonneg.2 hab)]
  nlinarith [mul_nonneg hψ ha.le]

/-- Integration by parts controls the oscillatory tail, uniformly in the endpoints. -/
theorem cosineIntegral_tail {ψ a b : ℝ} (hψ : 0 < ψ) (ha : 0 < a) (hab : a ≤ b) :
    |∫ t in a..b, cos (ψ * t) / t| ≤ 3 / (ψ * a) := by
  have hb : 0 < b := ha.trans_le hab
  have ht : ∀ t ∈ Set.uIcc a b, 0 < t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact ha.trans_le ht.1
  have hcont : ContinuousOn (fun t : ℝ ↦ 1 / (ψ * t ^ 2)) (Set.uIcc a b) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht'
    exact mul_ne_zero hψ.ne' (pow_ne_zero _ (ht t ht').ne')
  have hsin : IntervalIntegrable (fun t ↦ sin (ψ * t) / (ψ * t ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht'
    exact mul_ne_zero hψ.ne' (pow_ne_zero _ (ht t ht').ne')
  have hder : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t ↦ sin (ψ * t) / (ψ * t))
        (cos (ψ * t) / t - sin (ψ * t) / (ψ * t ^ 2)) t := by
    intro t ht'
    have h := (((hasDerivAt_id t).const_mul ψ).sin).div
      ((hasDerivAt_id t).const_mul ψ) (mul_ne_zero hψ.ne' (ht t ht').ne')
    convert h using 1
    · ext z
      rfl
    · dsimp only [id_eq]
      field_simp
  have hftc := integral_eq_sub_of_hasDerivAt hder
    ((intervalIntegrable_cos_div ψ ha hab).sub hsin)
  rw [integral_sub (intervalIntegrable_cos_div ψ ha hab) hsin] at hftc
  have hanti : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t ↦ -(ψ * t)⁻¹) (1 / (ψ * t ^ 2)) t := by
    intro t ht'
    have h := (((hasDerivAt_id t).const_mul ψ).inv
      (mul_ne_zero hψ.ne' (ht t ht').ne')).neg
    convert h using 1
    · ext z
      rfl
    · dsimp only [id_eq]
      field_simp
  have hint : |∫ t in a..b, sin (ψ * t) / (ψ * t ^ 2)| ≤ 1 / (ψ * a) := by
    rw [← norm_eq_abs]
    refine (norm_integral_le_of_norm_le hab (ae_of_all _ fun t ht' ↦ ?_)
      hcont.intervalIntegrable).trans ?_
    · have ht0 : 0 < t := ha.trans ht'.1
      rw [norm_eq_abs, abs_div, abs_of_pos (mul_pos hψ (sq_pos_of_pos ht0))]
      exact div_le_div_of_nonneg_right (abs_sin_le_one _) (by positivity)
    · rw [integral_eq_sub_of_hasDerivAt hanti hcont.intervalIntegrable]
      have : 0 ≤ (ψ * b)⁻¹ := by positivity
      simp only [one_div]
      linarith
  have hbd : ∀ t, a ≤ t → |sin (ψ * t) / (ψ * t)| ≤ 1 / (ψ * a) := by
    intro t hat
    have ht0 := ha.trans_le hat
    rw [abs_div, abs_of_pos (mul_pos hψ ht0)]
    calc |sin (ψ * t)| / (ψ * t) ≤ 1 / (ψ * t) :=
          div_le_div_of_nonneg_right (abs_sin_le_one _) (by positivity)
      _ ≤ 1 / (ψ * a) := by gcongr
  have h1 := hbd a le_rfl
  have h2 := hbd b hab
  have he : (∫ t in a..b, cos (ψ * t) / t) =
      sin (ψ * b) / (ψ * b) - sin (ψ * a) / (ψ * a) +
        (∫ t in a..b, sin (ψ * t) / (ψ * t ^ 2)) := by linarith
  rw [he]
  calc _ ≤ |sin (ψ * b) / (ψ * b)| + |sin (ψ * a) / (ψ * a)| +
        |∫ t in a..b, sin (ψ * t) / (ψ * t ^ 2)| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ 1 / (ψ * a) + 1 / (ψ * a) + 1 / (ψ * a) := add_le_add (add_le_add h2 h1) hint
    _ = 3 / (ψ * a) := by ring

/-- A uniform logarithmic approximation, with the transition at `ψ * b = 1`
handled explicitly and the frequency-zero endpoint included. -/
theorem cosineIntegral_log_ratio {ψ a b : ℝ} (hψ : 0 ≤ ψ) (hψ1 : ψ ≤ 1)
    (ha : 0 < a) (ha1 : a ≤ 1) (hab : a ≤ b) :
    |(∫ t in a..b, cos (ψ * t) / t) - log (b / (1 + ψ * b))| ≤ 5 + |log a| := by
  have hb : 0 < b := ha.trans_le hab
  have hp : 0 < 1 + ψ * b := by positivity
  have hla := le_abs_self (log a)
  have hla' := neg_abs_le (log a)
  by_cases hlow : ψ * b ≤ 1
  · have h := abs_le.1 (cosineIntegral_low hψ ha hab hlow)
    have hlog0 : 0 ≤ log (1 + ψ * b) := log_nonneg (by nlinarith)
    have hlog1 : log (1 + ψ * b) ≤ 1 := by
      have := log_le_sub_one_of_pos hp
      linarith
    rw [log_div hb.ne' hp.ne', abs_le]
    constructor <;> linarith
  · have hhigh : 1 < ψ * b := lt_of_not_ge hlow
    have hψ0 : 0 < ψ := by nlinarith
    let c := ψ⁻¹
    have hc : 0 < c := inv_pos.2 hψ0
    have hc1 : 1 ≤ c := by
      dsimp only [c]
      exact (one_le_inv₀ hψ0).2 hψ1
    have hac : a ≤ c := ha1.trans hc1
    have hcb : c ≤ b := by
      dsimp only [c]
      rw [inv_le_iff_one_le_mul₀' hψ0]
      nlinarith
    have hec : ψ * c = 1 := mul_inv_cancel₀ hψ0.ne'
    have hleft := abs_le.1 (cosineIntegral_low hψ ha hac hec.le)
    have hright := cosineIntegral_tail hψ0 hc hcb
    rw [hec] at hright
    norm_num only [div_one] at hright
    have hright' := abs_le.1 hright
    let r := b / (1 + ψ * b)
    have hr : 0 < r := div_pos hb hp
    have hrc : r ≤ c := by
      dsimp only [r]
      rw [div_le_iff₀ hp]
      nlinarith [hec]
    have hcr : c / 2 ≤ r := by
      dsimp only [r]
      rw [le_div_iff₀ hp]
      have : 1 ≤ ψ * b := hhigh.le
      have hcb' : c ≤ b := hcb
      nlinarith [hec]
    have hloghi : log r ≤ log c := log_le_log hr hrc
    have hloglo : log c - 1 ≤ log r := by
      have h := log_le_log (show 0 < c / 2 by positivity) hcr
      rw [log_div hc.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h
      have := log_two_lt_d9
      linarith
    rw [← integral_add_adjacent_intervals (intervalIntegrable_cos_div ψ ha hac)
      (intervalIntegrable_cos_div ψ hc hcb), abs_le]
    change -(5 + |log a|) ≤ _ - log r ∧ _ - log r ≤ 5 + |log a|
    constructor <;> linarith

/-- Logarithmic substitution for the cosine weight, with no regularity assumption
at zero needed because the integration interval lies above one. -/
theorem integral_cosineWeight_eq {x : ℝ} (hx : 2 ≤ x) (ψ : ℝ) :
    (∫ t in 2..x, cosineWeight ψ t) = ∫ u in log 2..log x, cos (ψ * u) / u := by
  have hpos : ∀ t ∈ Set.uIcc 2 x, 0 < t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    linarith [ht.1]
  have hlog : ContinuousOn log (Set.uIcc 2 x) :=
    continuousOn_log.mono (fun t ht ↦ by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact (hpos t ht).ne')
  have hsub := integral_comp_mul_deriv_of_deriv_nonneg
    (f := log) (f' := fun t ↦ t⁻¹) (g := fun u ↦ cos (ψ * u) / u) hlog
    (fun t ht ↦ hasDerivAt_log (hpos t (Set.Ioo_subset_Icc_self ht)).ne')
    (fun t ht ↦ inv_nonneg.2 (hpos t (Set.Ioo_subset_Icc_self ht)).le)
  convert hsub using 1
  congr 1
  ext t
  dsimp only [cosineWeight, Function.comp_apply]
  ring

/-- The continuous counterpart of (2.12), uniformly including `ψ = 0`. -/
theorem integral_cosineWeight_log_ratio {x ψ : ℝ} (hx : 2 ≤ x)
    (hψ : 0 ≤ ψ) (hψ1 : ψ ≤ 1) :
    |(∫ t in 2..x, cosineWeight ψ t) - log (log x / (1 + ψ * log x))| ≤
      5 + |log (log 2)| := by
  rw [integral_cosineWeight_eq hx]
  exact cosineIntegral_log_ratio hψ hψ1 (log_pos one_lt_two)
    (by have := log_two_lt_d9; linarith) (log_le_log (by norm_num) hx)

/-- Formula (2.12): the cosine prime sum is its logarithmic main term plus
an absolute, uniform error for `x ≥ 2` and `0 ≤ ψ ≤ 1`. -/
theorem cosinePrimeSum_log_ratio : ∃ K ≥ 0, ∀ x ψ,
    2 ≤ x → 0 ≤ ψ → ψ ≤ 1 →
    |cosinePrimeSum x ψ - log (log x / (1 + ψ * log x))| ≤ K := by
  obtain ⟨K, hK0, hK⟩ := cosinePrimeSum_integral_error
  refine ⟨K + (5 + |log (log 2)|), by positivity, fun x ψ hx hψ hψ1 ↦ ?_⟩
  calc |cosinePrimeSum x ψ - log (log x / (1 + ψ * log x))|
      ≤ |cosinePrimeSum x ψ - (∫ t in 2..x, cosineWeight ψ t)| +
        |(∫ t in 2..x, cosineWeight ψ t) - log (log x / (1 + ψ * log x))| :=
          abs_sub_le _ _ _
    _ ≤ K + (5 + |log (log 2)|) := add_le_add
        (hK x ψ hx (by rw [abs_of_nonneg hψ]; linarith))
        (integral_cosineWeight_log_ratio hx hψ hψ1)

end BretecheTenenbaumMean.PrimeSums
