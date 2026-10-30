module

public import BretecheTenenbaumMean.PrimeLayerCentral
public import BretecheTenenbaumMean.GridThreshold

@[expose] public section

/-! # Uniform marginal probabilities on the scale window used in §3 -/

namespace BretecheTenenbaumMean

open Real

theorem criticalSlope_ge_one : 1 ≤ criticalSlope := by
  have hp := criticalSlope_pos
  have hl : log (2 : ℝ) < 1 := by linarith [log_two_lt_d9]
  nlinarith [criticalSlope_log_identity, mul_lt_mul_of_pos_left hl hp]

/-- Every scale in the window has the required size, count range, and
quadratic distance from the tilted mean. -/
theorem central_dyadic_window_bounds {h t : ℕ} (ht : (1 : ℝ) ≤ t)
    (hlo : criticalSlope * t ≤ h) (hhi : (h : ℝ) ≤ criticalSlope * t + sqrt t) :
    (t : ℝ) / 2 ≤ (h : ℝ) * log 2 ∧
    (h : ℝ) * log 2 ≤ 4 * t ∧
    (h + t : ℕ) ≤ 4 * ((h : ℝ) * log 2) ∧
    ((h + t : ℕ) - 2 * ((h : ℝ) * log 2)) ^ 2 ≤ 2 * ((h : ℝ) * log 2) := by
  have ht0 : 0 ≤ (t : ℝ) := Nat.cast_nonneg _
  have hh0 : 0 ≤ (h : ℝ) := Nat.cast_nonneg _
  have hγ := criticalSlope_pos
  have hγ1 := criticalSlope_ge_one
  have hγ3 := criticalSlope_le_three
  have hlhalf : (1 / 2 : ℝ) < log 2 := by linarith [log_two_gt_d9]
  have hlone : log (2 : ℝ) < 1 := by linarith [log_two_lt_d9]
  have hroot : sqrt (t : ℝ) ≤ t := by
    have := sq_sqrt ht0
    nlinarith [sqrt_nonneg (t : ℝ)]
  have hth : (t : ℝ) ≤ h := by nlinarith [mul_le_mul_of_nonneg_right hγ1 ht0]
  have hhhi : (h : ℝ) ≤ 4 * t := by
    have := mul_le_mul_of_nonneg_right hγ3 ht0
    linarith
  have hLlo : (t : ℝ) / 2 ≤ (h : ℝ) * log 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hlhalf.le hh0]
  have hLhi : (h : ℝ) * log 2 ≤ 4 * t := by
    nlinarith [mul_le_mul_of_nonneg_left hlone.le hh0]
  refine ⟨hLlo, hLhi, ?_, ?_⟩
  · push_cast
    nlinarith [mul_le_mul_of_nonneg_left hlhalf.le hh0]
  · let d := (h : ℝ) + t - 2 * ((h : ℝ) * log 2)
    have hid : criticalSlope * d = criticalSlope * t - h := by
      have he := congrArg (fun z : ℝ ↦ (h : ℝ) * z) criticalSlope_log_identity
      dsimp only [d]
      nlinarith
    have hd0 : d ≤ 0 := by nlinarith [hlo]
    have hdlo : -sqrt (t : ℝ) ≤ d := by
      have he := mul_le_mul_of_nonpos_right hγ1 hd0
      rw [hid] at he
      linarith
    have hsq : d ^ 2 ≤ (t : ℝ) := by
      have he := mul_nonneg (show 0 ≤ d + sqrt (t : ℝ) by linarith)
        (show 0 ≤ sqrt (t : ℝ) - d by linarith [sqrt_nonneg (t : ℝ)])
      nlinarith [sq_sqrt ht0]
    push_cast
    change d ^ 2 ≤ _
    linarith

/-- Each marginal in the chosen scale window has mass bounded below by
an absolute multiple of `2^(-t)/sqrt t`. -/
theorem central_dyadic_marginal_lower : ∃ c > 0, ∃ T₀ ≥ (1 : ℝ),
    ∀ h t : ℕ, T₀ ≤ t → criticalSlope * t ≤ h →
      (h : ℝ) ≤ criticalSlope * t + sqrt t →
      c / ((2 : ℝ) ^ t * sqrt t) ≤
        probability (exp ((2 : ℝ) ^ h)) {n | n.primeFactors.card = h + t} := by
  obtain ⟨c, hc, C, hC, L₀, hL₀, hprob⟩ := probability_prime_layer_central
    (show (0 : ℝ) ≤ 2 by norm_num)
  refine ⟨c / sqrt 8, by positivity, max 1 (2 * L₀), le_max_left _ _,
    fun h t ht hlo hhi ↦ ?_⟩
  have ht1 : (1 : ℝ) ≤ t := (le_max_left _ _).trans ht
  have htL : 2 * L₀ ≤ (t : ℝ) := (le_max_right _ _).trans ht
  have hb := central_dyadic_window_bounds ht1 hlo hhi
  have hy : 2 ≤ exp ((2 : ℝ) ^ h) := exp_one_gt_two.le.trans
    (exp_le_exp.2 (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
  have hp := (hprob (exp ((2 : ℝ) ^ h)) hy
    (by simp only [log_exp, log_pow]; linarith [hb.1]) (h + t)
    (by simpa only [log_exp, log_pow] using hb.2.2.2)).1
  simp only [log_exp, log_pow, Nat.cast_add] at hp
  have hexp : exp ((h : ℝ) * log 2 - ((h : ℝ) + t) * log 2) = 1 / (2 : ℝ) ^ t := by
    rw [show (h : ℝ) * log 2 - ((h : ℝ) + t) * log 2 = -((t : ℝ) * log 2) by ring,
      exp_neg, exp_nat_mul, exp_log (by norm_num : (0 : ℝ) < 2), one_div]
  rw [hexp] at hp
  have hs : 0 < sqrt (2 * ((h : ℝ) * log 2)) := sqrt_pos.2 (by linarith [hb.1])
  have hroot : sqrt (2 * ((h : ℝ) * log 2)) ≤ sqrt 8 * sqrt (t : ℝ) := by
    rw [← sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
    exact sqrt_le_sqrt (by linarith [hb.2.1])
  calc
    _ = (c / (2 : ℝ) ^ t) / (sqrt 8 * sqrt (t : ℝ)) := by ring
    _ ≤ (c / (2 : ℝ) ^ t) / sqrt (2 * ((h : ℝ) * log 2)) :=
      div_le_div_of_nonneg_left (by positivity) hs hroot
    _ = c * ((1 / (2 : ℝ) ^ t) / sqrt (2 * ((h : ℝ) * log 2))) := by ring
    _ ≤ _ := hp

end BretecheTenenbaumMean
