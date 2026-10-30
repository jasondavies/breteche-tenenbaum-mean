module

public import BretecheTenenbaumMean.WindowBounds
public import BretecheTenenbaumMean.MomentRecurrence
public import BretecheTenenbaumMean.GoodSets
public import BretecheTenenbaumMean.PrimeLayers
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-! # The support-length lower bound for the normalized second moment -/

namespace BretecheTenenbaumMean

open Real MeasureTheory Set

/-- Cauchy–Schwarz on the support of the divisor-window function. -/
theorem tau_sq_le_moment_two_mul_log (n : ℕ) :
    tau n ^ 2 ≤ moment 2 n * (log n + 1) := by
  let g : ℝ → ℝ := (Ico (-1) (log n)).indicator (fun _ ↦ 1)
  have hlog : 0 ≤ log (n : ℝ) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · exact log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn)
  have hg : Integrable g :=
    (integrableOn_const (measure_Ico_lt_top.ne)).integrable_indicator measurableSet_Ico
  have hg2 : (fun u ↦ g u ^ 2) = g := by
    funext u
    by_cases hu : u ∈ Ico (-1) (log (n : ℝ)) <;> simp [g, hu]
  have hgnonneg : ∀ u, 0 ≤ g u := fun u ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) u
  have hprod : (fun u ↦ delta n u * g u) = delta n := by
    funext u
    by_cases hu : u ∈ Ico (-1) (log (n : ℝ))
    · simp [g, hu]
    · simp [g, hu, delta_eq_zero_outside n hu]
  have hgi : (∫ u, g u) = log n + 1 := by
    dsimp only [g]
    rw [integral_indicator_const _ measurableSet_Ico]
    simp only [Real.volume_real_Ico, smul_eq_mul, mul_one, sub_neg_eq_add]
    rw [max_eq_left (by linarith)]
  have hf := (memLp_two_iff_integrable_sq (measurable_delta n).aestronglyMeasurable).2
    (integrable_delta_pow n 2 (by omega))
  have hgm := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 (by rwa [hg2])
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 by constructor <;> norm_num)
    (Filter.Eventually.of_forall (delta_nonneg n)) (Filter.Eventually.of_forall hgnonneg)
    (by simpa using hf) (by simpa using hgm)
  simp only [rpow_two] at h
  rw [hprod, integral_delta, hg2, hgi] at h
  change tau n ≤ (moment 2 n) ^ (1 / 2 : ℝ) * (log n + 1) ^ (1 / 2 : ℝ) at h
  rw [← sqrt_eq_rpow, ← sqrt_eq_rpow] at h
  have hh := mul_self_le_mul_self (show 0 ≤ tau n from Nat.cast_nonneg _) h
  simpa only [← pow_two, mul_pow, sq_sqrt (moment_nonneg 2 n),
    sq_sqrt (show 0 ≤ log (n : ℝ) + 1 by linarith)] using hh

/-- A size bound on an integer gives a lower bound for its normalized second
moment in terms of its divisor count. -/
theorem normalized_second_moment_ge_tau {n : ℕ} (hn : n ≠ 0)
    {L : ℝ} (hL : 0 < L) (hsize : log n + 1 ≤ L) :
    tau n / L ≤ moment 2 n / tau n := by
  apply (div_le_div_iff₀ hL (tau_pos hn)).2
  have h := tau_sq_le_moment_two_mul_log n
  have hm := mul_le_mul_of_nonneg_left hsize (moment_nonneg 2 n)
  nlinarith

/-- At a locally controlled cutoff, a large divisor count forces a large
normalized second moment of every squarefree multiple. -/
theorem normalized_second_moment_ge_smallPrime {n : ℕ} (hn : Squarefree n)
    {y K : ℝ} (hy : 2 ≤ y) (hK : 1 ≤ K)
    (hsize : (smallPrimePart n y : ℝ) ≤ y ^ K) :
    tau (smallPrimePart n y) / (K * log y + 1) ≤ moment 2 n / tau n := by
  have hy0 : 0 < y := by linarith
  have hly : 0 < log y := log_pos (by linarith)
  have hsmall : 0 < (smallPrimePart n y : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (smallPrimePart_ne_zero n y)
  have hl : log (smallPrimePart n y : ℝ) ≤ K * log y := by
    have h := log_le_log hsmall hsize
    rwa [log_rpow hy0] at h
  have hlocal := normalized_second_moment_ge_tau (smallPrimePart_ne_zero n y)
    (show 0 < K * log y + 1 by positivity) (by nlinarith)
  exact hlocal.trans (normalized_moment_le_of_dvd hn (smallPrimePart_dvd n y) (by norm_num))

/-- At a dyadic cutoff, a count of `h+t` primes gives a lower threshold
independent of the scale index `h`. -/
theorem normalized_second_moment_dyadic_layer {n : ℕ} (hn : Squarefree n)
    (h t : ℕ) {K : ℝ} (hK : 1 ≤ K)
    (hcount : (smallPrimePart n (exp ((2 : ℝ) ^ h))).primeFactors.card = h + t)
    (hsize : (smallPrimePart n (exp ((2 : ℝ) ^ h)) : ℝ) ≤
      (exp ((2 : ℝ) ^ h)) ^ K) :
    (2 : ℝ) ^ t / (K + 1) ≤ moment 2 n / tau n := by
  have hh : (1 : ℝ) ≤ 2 ^ h := one_le_pow₀ (by norm_num)
  have hy : 2 ≤ exp ((2 : ℝ) ^ h) := exp_one_gt_two.le.trans (exp_le_exp.2 hh)
  have he := normalized_second_moment_ge_smallPrime hn hy hK hsize
  rw [tau_squarefree (hn.squarefree_of_dvd (smallPrimePart_dvd _ _)), hcount,
    log_exp, pow_add] at he
  have hd : 0 < K * (2 : ℝ) ^ h + 1 := by positivity
  calc
    _ = ((2 : ℝ) ^ h * 2 ^ t) / ((K + 1) * 2 ^ h) := by field_simp
    _ ≤ ((2 : ℝ) ^ h * 2 ^ t) / (K * 2 ^ h + 1) :=
      div_le_div_of_nonneg_left (by positivity) hd (by nlinarith)
    _ ≤ _ := he

end BretecheTenenbaumMean
