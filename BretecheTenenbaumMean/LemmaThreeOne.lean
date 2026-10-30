module

public import BretecheTenenbaumMean.PrimeLayerAsymptotic
public import BretecheTenenbaumMean.Targets

@[expose] public section

/-! # Lemma 3.1: uniform fixed-prime-count probabilities -/

namespace BretecheTenenbaumMean

open Real

/-- Estimate (3.1), with all constants and the lower cutoff chosen before the
varying parameters `x,h,k`. -/
theorem lemmaThreeOne : LemmaThreeOne := by
  intro ε hε _
  have hA : 0 < 1 / ε ^ 2 := by positivity
  obtain ⟨c, hc, C, hC, L₀, hL₀, hprob⟩ := probability_prime_layer_bounds hA
  let R := (L₀ + 1) / ε
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨c, hc, C, hC, max 3 (exp (exp R)), le_max_left _ _, fun x hx h k hh _ _ hk ↦ ?_⟩
  have hx3 : 3 ≤ x := (le_max_left _ _).trans hx
  have hxe : exp (exp R) ≤ x := (le_max_right _ _).trans hx
  have hlx : 0 < log x := log_pos (by linarith)
  have hll : R ≤ log (log x) := by
    have hl : exp R ≤ log x := by
      have h := log_le_log (exp_pos (exp R)) hxe
      simpa only [log_exp] using h
    have h := log_le_log (exp_pos R) hl
    simpa only [log_exp] using h
  have hcut : L₀ ≤ ε * log (log x) := by
    have h := mul_le_mul_of_nonneg_left hll hε.le
    have he : ε * R = L₀ + 1 := by dsimp [R]; field_simp
    rw [he] at h
    linarith
  have hscale : ε * log (log x) ≤ (h : ℝ) * log 2 := by
    have hlog := log_le_log (rpow_pos_of_pos hlx ε) hh
    rw [log_rpow hlx, log_pow] at hlog
    exact hlog
  have hy : 2 ≤ exp ((2 : ℝ) ^ h) := by
    exact exp_one_gt_two.le.trans (exp_le_exp.2 (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
  have hk' : (k : ℝ) ≤ (1 / ε ^ 2) * ((h : ℝ) * log 2) := by
    rw [one_div, inv_mul_eq_div]
    apply (le_div_iff₀ (sq_pos_of_pos hε)).2
    have h := (le_div_iff₀ hε).1 hk
    have hmul := mul_le_mul_of_nonneg_right h hε.le
    nlinarith
  have hbound := hprob (exp ((2 : ℝ) ^ h)) hy
    (by simpa only [log_exp, log_pow] using hcut.trans hscale) k
    (by simpa only [log_exp, log_pow] using hk')
  simpa only [log_exp, log_pow] using hbound

end BretecheTenenbaumMean
