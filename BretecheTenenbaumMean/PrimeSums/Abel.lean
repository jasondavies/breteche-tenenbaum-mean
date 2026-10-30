module

public import BretecheTenenbaumMean.PrimeSums.Mertens

@[expose] public section

/-! # Weighted partial summation against the prime number theorem -/

open Real Finset MeasureTheory intervalIntegral
open scoped Chebyshev

namespace BretecheTenenbaumMean.PrimeSums

/-- The error in replacing a prime sum weighted by `f(p) log p` by `∫ f`.
The identity retains the exact endpoint convention `(x,y]`. -/
theorem weighted_sum_sub_integral {f f' : ℝ → ℝ} {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y)
    (hf : ∀ t ∈ Set.Icc x y, HasDerivAt f (f' t) t)
    (hf' : ContinuousOn f' (Set.Icc x y)) :
    (∑ k ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, f k * logPrime k) - (∫ t in x..y, f t) =
      f y * (θ y - y) - f x * (θ x - x) - ∫ t in x..y, f' t * (θ t - t) := by
  have hi : IntegrableOn (deriv f) (Set.Icc x y) :=
    hf'.integrableOn_Icc.congr_fun (fun t ht ↦ (hf t ht).deriv.symm) measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul logPrime hx hxy
    (fun t ht ↦ (hf t ht).differentiableAt) hi
  simp only [sum_logPrime_eq_theta] at habel
  rw [setIntegral_congr_fun measurableSet_Ioc
    (g := fun t ↦ f' t * θ t)
    (fun t ht ↦ by rw [(hf t (Set.Ioc_subset_Icc_self ht)).deriv]),
    ← intervalIntegral.integral_of_le hxy] at habel
  have hfc : ContinuousOn f (Set.uIcc x y) := by
    rw [Set.uIcc_of_le hxy]
    exact fun t ht ↦ (hf t ht).continuousAt.continuousWithinAt
  have hfc' : ContinuousOn f' (Set.uIcc x y) := by rwa [Set.uIcc_of_le hxy]
  have hi1 : IntervalIntegrable (fun t ↦ f' t * θ t) volume x y :=
    Chebyshev.theta_mono.intervalIntegrable.continuousOn_mul hfc'
  have hi2 : IntervalIntegrable (fun t ↦ f' t * t) volume x y :=
    (continuousOn_id.mono (Set.subset_univ _)).intervalIntegrable.continuousOn_mul hfc'
  have hftc : (∫ t in x..y, f' t * t) + (∫ t in x..y, f t) = f y * y - f x * x := by
    rw [← integral_add hi2 hfc.intervalIntegrable]
    apply integral_eq_sub_of_hasDerivAt _ (hi2.add hfc.intervalIntegrable)
    intro t ht
    have h := (hf t (by rwa [Set.uIcc_of_le hxy] at ht)).mul (hasDerivAt_id t)
    convert h using 1
    · ext z
      rfl
    · simp only [id_eq, mul_one]
  have hsplit : (∫ t in x..y, f' t * (θ t - t)) =
      (∫ t in x..y, f' t * θ t) - ∫ t in x..y, f' t * t := by
    simp_rw [mul_sub]
    exact integral_sub hi1 hi2
  rw [hsplit]
  linear_combination habel - hftc

/-- A uniform PNT error for a family of smooth weights. The constant is independent
of the endpoints, the weight, and the derivative-bound parameter `A`. -/
theorem weighted_prime_error_bound : ∃ K ≥ 0, ∀ {x y A : ℝ} {f f' : ℝ → ℝ},
    2 ≤ x → x ≤ y → 0 ≤ A →
    (∀ t ∈ Set.Icc x y, HasDerivAt f (f' t) t) →
    ContinuousOn f' (Set.Icc x y) →
    (∀ t ∈ Set.Icc x y, |f t| ≤ (t * log t)⁻¹) →
    (∀ t ∈ Set.Icc x y, |f' t| ≤ A * ((log t + 1) / (t * log t) ^ 2)) →
    |(∑ k ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, f k * logPrime k) - (∫ t in x..y, f t)| ≤
      K * (1 + A) * pntE x := by
  obtain ⟨C, hC0, hC⟩ := theta_asymp
  have hκ := pntκ_pos
  refine ⟨4 * C + 12 * C / pntκ, by positivity, ?_⟩
  intro x y A f f' hx hxy hA hf hf' hw hd
  rw [weighted_sum_sub_integral (by linarith) hxy hf hf']
  have hbd : ∀ t ∈ Set.Icc x y, |f t * (θ t - t)| ≤ 2 * C * pntE x := by
    intro t ht
    have ht2 : 2 ≤ t := hx.trans ht.1
    have ht0 : 0 < t := by linarith
    have hL := half_le_log ht2
    have hE := pntE_pos t
    calc |f t * (θ t - t)| = |f t| * |θ t - t| := abs_mul _ _
      _ ≤ (t * log t)⁻¹ * (C * t * pntE t) :=
        mul_le_mul (hw t ht) (hC t ht2) (abs_nonneg _) (by positivity)
      _ = C * pntE t / log t := by field_simp
      _ ≤ 2 * C * pntE t := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith [mul_nonneg hC0 hE.le]
      _ ≤ 2 * C * pntE x := by gcongr; exact pntE_le_pntE (by linarith) ht.1
  have hderivE : ∀ t ∈ Set.uIcc x y,
      HasDerivAt pntE (pntE t * (-pntκ * (t⁻¹ / (2 * √(log t))))) t := fun t ht ↦
    hasDerivAt_pntE (by rw [Set.uIcc_of_le hxy] at ht; linarith [ht.1])
  have hcontE := continuousOn_deriv_pntE (y := y) (show 1 < x by linarith)
  rw [← Set.uIcc_of_le hxy] at hcontE
  have hintE := hcontE.intervalIntegrable (μ := volume)
  have hftc : (∫ t in x..y,
      A * (-(12 * C / pntκ) * (pntE t * (-pntκ * (t⁻¹ / (2 * √(log t))))))) =
        A * (12 * C / pntκ) * (pntE x - pntE y) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_eq_sub_of_hasDerivAt hderivE hintE]
    ring
  have hint : |∫ t in x..y, f' t * (θ t - t)| ≤ A * (12 * C / pntκ) * pntE x := by
    rw [← norm_eq_abs]
    refine (norm_integral_le_of_norm_le hxy (ae_of_all _ fun t ht ↦ ?_)
      ((hintE.const_mul (-(12 * C / pntκ))).const_mul A)).trans ?_
    · have ht' : t ∈ Set.Icc x y := Set.Ioc_subset_Icc_self ht
      have ht2 := hx.trans ht'.1
      have hq : 0 ≤ (log t + 1) / (t * log t) ^ 2 := by
        have := half_le_log ht2
        positivity
      rw [norm_eq_abs, abs_mul]
      calc |f' t| * |θ t - t|
          ≤ (A * ((log t + 1) / (t * log t) ^ 2)) * |θ t - t| :=
            mul_le_mul_of_nonneg_right (hd t ht') (abs_nonneg _)
        _ = A * |(log t + 1) / (t * log t) ^ 2 * (θ t - t)| := by
            rw [abs_mul, abs_of_nonneg hq]; ring
        _ ≤ A * (-(12 * C / pntκ) * (pntE t * (-pntκ * (t⁻¹ / (2 * √(log t)))))) :=
            mul_le_mul_of_nonneg_left (abs_integrand_le hC0 ht2 (hC t ht2)) hA
    · rw [hftc]
      have : 0 ≤ A * (12 * C / pntκ) * pntE y :=
        mul_nonneg (by positivity) (pntE_nonneg y)
      nlinarith
  have hb1 := hbd x ⟨le_rfl, hxy⟩
  have hb2 := hbd y ⟨hxy, le_rfl⟩
  calc |f y * (θ y - y) - f x * (θ x - x) - ∫ t in x..y, f' t * (θ t - t)|
      ≤ |f y * (θ y - y)| + |f x * (θ x - x)| + |∫ t in x..y, f' t * (θ t - t)| :=
        (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ (4 * C + A * (12 * C / pntκ)) * pntE x := by linarith
    _ ≤ (4 * C + 12 * C / pntκ) * (1 + A) * pntE x := by
        have := pntE_pos x
        have : 0 ≤ A * (4 * C) + 12 * C / pntκ := by positivity
        nlinarith

end BretecheTenenbaumMean.PrimeSums
