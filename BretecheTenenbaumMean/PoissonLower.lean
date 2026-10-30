module

public import BretecheTenenbaumMean.PoissonBound

@[expose] public section

/-! # Lower bounds for Poisson coefficients near their mean -/

namespace BretecheTenenbaumMean

open Real

/-- The monotonicity half of Stirling's formula gives an upper factorial bound. -/
theorem factorial_le_stirling_upper {r : ℕ} (hr : r ≠ 0) :
    (r.factorial : ℝ) ≤ Stirling.stirlingSeq 1 *
      (sqrt (2 * r) * ((r : ℝ) / exp 1) ^ r) := by
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hr
  have h : Stirling.stirlingSeq r ≤ Stirling.stirlingSeq 1 := by
    simpa only [Function.comp_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hr)] using
      Stirling.stirlingSeq'_antitone (show 0 ≤ r - 1 by omega)
  rw [Stirling.stirlingSeq, div_le_iff₀ (by positivity)] at h
  exact h

/-- An explicit lower point-mass bound with a quadratic penalty away from the mean. -/
theorem factorial_term_lower {u : ℝ} (hu : 0 < u) {r : ℕ} (hr : r ≠ 0) :
    exp (u - ((r : ℝ) - u) ^ 2 / u) /
        (Stirling.stirlingSeq 1 * sqrt (2 * r)) ≤ u ^ r / (r.factorial : ℝ) := by
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hr
  have hf : 0 < (r.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos r
  have hseq : 0 < Stirling.stirlingSeq 1 := Stirling.stirlingSeq'_pos 0
  have hs : 0 < sqrt (2 * r) := sqrt_pos.2 (by positivity)
  have hp : 0 < ((r : ℝ) / exp 1) ^ r := by positivity
  have hlog := log_le_sub_one_of_pos (div_pos hr0 hu)
  have hmul := mul_le_mul_of_nonneg_left hlog hr0.le
  have he : u - ((r : ℝ) - u) ^ 2 / u ≤
      (r : ℝ) * log (u / r) + r := by
    rw [log_div hu.ne' hr0.ne']
    rw [log_div hr0.ne' hu.ne'] at hmul
    have halg : u - ((r : ℝ) - u) ^ 2 / u =
        (r : ℝ) - r * ((r : ℝ) / u - 1) := by field_simp; ring
    rw [halg]
    linarith
  have hpow : exp (u - ((r : ℝ) - u) ^ 2 / u) *
      ((r : ℝ) / exp 1) ^ r ≤ u ^ r := by
    calc
      _ ≤ exp ((r : ℝ) * log (u / r) + r) * ((r : ℝ) / exp 1) ^ r :=
        mul_le_mul_of_nonneg_right (exp_le_exp.2 he) hp.le
      _ = u ^ r := by
        rw [exp_add, exp_nat_mul, exp_log (div_pos hu hr0),
          show exp (r : ℝ) = (exp 1) ^ r by
            simpa only [mul_one] using exp_nat_mul (1 : ℝ) r,
          ← mul_pow, ← mul_pow]
        congr 1
        field_simp
  rw [div_le_div_iff₀ (mul_pos hseq hs) hf]
  calc
    _ ≤ exp (u - ((r : ℝ) - u) ^ 2 / u) *
        (Stirling.stirlingSeq 1 * (sqrt (2 * r) * ((r : ℝ) / exp 1) ^ r)) :=
      mul_le_mul_of_nonneg_left (factorial_le_stirling_upper hr) (exp_pos _).le
    _ = (exp (u - ((r : ℝ) - u) ^ 2 / u) * ((r : ℝ) / exp 1) ^ r) *
        (Stirling.stirlingSeq 1 * sqrt (2 * r)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow (mul_pos hseq hs).le

/-- Two-sided Poisson bounds in a window whose squared radius is proportional
 to its mean. The constants are explicit and independent of `u,r`. -/
theorem factorial_term_central {u B : ℝ} (hu : 0 < u) {r : ℕ}
    (hr : r ≠ 0) (hrhi : (r : ℝ) ≤ 2 * u)
    (hgap : ((r : ℝ) - u) ^ 2 ≤ B * u) :
    (1 / (2 * Stirling.stirlingSeq 1 * exp B)) * (exp u / sqrt u) ≤
        u ^ r / (r.factorial : ℝ) ∧
      u ^ r / (r.factorial : ℝ) ≤ 8 * (exp u / sqrt u) := by
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hr
  have hseq : 0 < Stirling.stirlingSeq 1 := Stirling.stirlingSeq'_pos 0
  have hs : 0 < sqrt u := sqrt_pos.2 hu
  have hsr : 0 < sqrt (2 * r) := sqrt_pos.2 (by positivity)
  have hroot : sqrt (2 * r) ≤ 2 * sqrt u := by
    have h1 := sq_sqrt (show 0 ≤ 2 * (r : ℝ) by positivity)
    have h2 := sq_sqrt hu.le
    nlinarith [sqrt_nonneg (2 * r)]
  constructor
  · calc
      _ = exp (u - B) / (Stirling.stirlingSeq 1 * (2 * sqrt u)) := by
        rw [exp_sub]
        ring
      _ ≤ exp (u - ((r : ℝ) - u) ^ 2 / u) /
          (Stirling.stirlingSeq 1 * sqrt (2 * r)) := by
        apply div_le_div₀ (exp_pos _).le
        · apply exp_le_exp.2
          have := (div_le_iff₀ hu).2 hgap
          linarith
        · positivity
        · exact mul_le_mul_of_nonneg_left hroot hseq.le
      _ ≤ _ := factorial_term_lower hu hr
  · calc
      _ ≤ 8 * exp u / sqrt (1 + u) := factorial_term_uniform hu.le r
      _ ≤ 8 * exp u / sqrt u := by gcongr; linarith
      _ = _ := by ring

end BretecheTenenbaumMean
