module

public import BretecheTenenbaumMean.PrimeLayerCentral
public import BretecheTenenbaumMean.GridThreshold

@[expose] public section

/-! # The central-window consequence (3.2) -/

namespace BretecheTenenbaumMean

open Real

/-- The second assertion of Lemma 3.1, with an integer prime count and a real
 offset, so no integer rounding is implicit. -/
theorem lemmaThreeOneCentral : LemmaThreeOneCentral := by
  intro ε hε hεhi
  obtain ⟨c, hc, C, hC, L₀, hL₀, hprob⟩ := probability_prime_layer_central
    (show 0 ≤ 1 / ε by positivity)
  let R := (L₀ + 1) / ε
  have hR : 0 < R := by dsimp [R]; positivity
  have hs2 : 0 < sqrt (2 : ℝ) := by positivity
  have hsε : 0 < sqrt (2 * ε) := by positivity
  refine ⟨c / sqrt 2, by positivity, C / sqrt (2 * ε), by positivity,
    max 3 (exp (exp R)), le_max_left _ _, fun x hx h k hh hhhi hcenter ↦ ?_⟩
  let X := log (log x)
  let L := (h : ℝ) * log 2
  have hx3 : 3 ≤ x := (le_max_left _ _).trans hx
  have hxe : exp (exp R) ≤ x := (le_max_right _ _).trans hx
  have hlx : 0 < log x := log_pos (by linarith)
  have hRX : R ≤ X := by
    have hl : exp R ≤ log x := by
      have he := log_le_log (exp_pos (exp R)) hxe
      simpa only [log_exp] using he
    have he := log_le_log (exp_pos R) hl
    simpa only [log_exp] using he
  have hX : 0 < X := hR.trans_le hRX
  have hcut : L₀ ≤ ε * X := by
    have he := mul_le_mul_of_nonneg_left hRX hε.le
    have hid : ε * R = L₀ + 1 := by dsimp [R]; field_simp
    rw [hid] at he
    linarith
  have hlo : ε * X ≤ L := by
    have he := log_le_log (rpow_pos_of_pos hlx ε) hh
    simpa only [log_rpow hlx, log_pow] using he
  have hhi : L ≤ X := by
    have he := log_le_log (by positivity : 0 < (2 : ℝ) ^ h) hhhi
    rw [log_pow, log_rpow hlx] at he
    change L ≤ (1 - ε) * X at he
    nlinarith
  have hL : 0 < L := (mul_pos hε hX).trans_le hlo
  have hid : (h : ℝ) / criticalSlope = 2 * L - h := by
    apply (div_eq_iff criticalSlope_pos.ne').2
    have he := congrArg (fun z : ℝ ↦ (h : ℝ) * z) criticalSlope_log_identity
    dsimp only [L]
    nlinarith
  have hgap : ((k : ℝ) - 2 * L) ^ 2 ≤ (1 / ε) * L := by
    rw [hid, show (k : ℝ) - h - (2 * L - h) = k - 2 * L by ring] at hcenter
    have he := (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).2 hcenter
    rw [sq_abs, sq_sqrt hX.le] at he
    have hXL : X ≤ (1 / ε) * L := by
      rw [one_div, inv_mul_eq_div]
      exact (le_div_iff₀ hε).2 (by linarith)
    exact he.trans hXL
  have hy : 2 ≤ exp ((2 : ℝ) ^ h) :=
    exp_one_gt_two.le.trans (exp_le_exp.2 (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
  have hp := hprob (exp ((2 : ℝ) ^ h)) hy
    (by simpa only [log_exp, log_pow] using hcut.trans hlo) k
    (by simpa only [log_exp, log_pow] using hgap)
  simp only [log_exp, log_pow] at hp
  change c * (exp (L - k * log 2) / sqrt (2 * L)) ≤ _ ∧
    _ ≤ C * (exp (L - k * log 2) / sqrt (2 * L)) at hp
  have hexp : exp (L - k * log 2) = 1 / (2 : ℝ) ^ ((k : ℝ) - h) := by
    rw [rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), one_div, ← exp_neg]
    congr 1
    dsimp only [L]
    ring
  rw [hexp] at hp
  have hsX : 0 < sqrt X := sqrt_pos.2 hX
  have hsL : 0 < sqrt (2 * L) := by positivity
  have hrootlo : sqrt (2 * ε) * sqrt X ≤ sqrt (2 * L) := by
    rw [← sqrt_mul (by positivity)]
    apply sqrt_le_sqrt
    linarith
  have hroothi : sqrt (2 * L) ≤ sqrt 2 * sqrt X := by
    rw [← sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact sqrt_le_sqrt (by linarith)
  have hd : 0 < (2 : ℝ) ^ ((k : ℝ) - h) := rpow_pos_of_pos (by norm_num) _
  constructor
  · calc
      _ = (c * (1 / (2 : ℝ) ^ ((k : ℝ) - h))) / (sqrt 2 * sqrt X) := by ring
      _ ≤ (c * (1 / (2 : ℝ) ^ ((k : ℝ) - h))) / sqrt (2 * L) :=
        div_le_div_of_nonneg_left (by positivity) hsL hroothi
      _ = c * ((1 / (2 : ℝ) ^ ((k : ℝ) - h)) / sqrt (2 * L)) := by ring
      _ ≤ _ := hp.1
  · calc
      _ ≤ C * ((1 / (2 : ℝ) ^ ((k : ℝ) - h)) / sqrt (2 * L)) := hp.2
      _ = (C * (1 / (2 : ℝ) ^ ((k : ℝ) - h))) / sqrt (2 * L) := by ring
      _ ≤ (C * (1 / (2 : ℝ) ^ ((k : ℝ) - h))) / (sqrt (2 * ε) * sqrt X) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hsε hsX) hrootlo
      _ = _ := by ring

end BretecheTenenbaumMean
