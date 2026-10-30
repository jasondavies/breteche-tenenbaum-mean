module

public import BretecheTenenbaumMean.InverseSquareConvolution
public import BretecheTenenbaumMean.ThirdMomentBase
public import BretecheTenenbaumMean.RecursionEndpoints
public import BretecheTenenbaumMean.ThresholdRecursion

@[expose] public section

/-! # The explicit admissible threshold sequence in §2.4 -/

namespace BretecheTenenbaumMean

open Finset Real

noncomputable def thresholdScale (C₀ T : ℝ) : ℝ := (2 * π ^ 2 * C₀ / 3) * T * sqrt (log T)

noncomputable def explicitThreshold (C₀ T : ℝ) (q : ℕ) : ℝ :=
  if q = 0 then 1 else (q.factorial : ℝ) / (q : ℝ) ^ 2 * thresholdScale C₀ T ^ (q - 1)

theorem thresholdScale_pos {C₀ T : ℝ} (hC : 0 < C₀) (hT : 1 < T) : 0 < thresholdScale C₀ T := by
  have ht : 0 < T := by linarith
  have hl := log_pos hT
  unfold thresholdScale
  positivity

@[simp] theorem explicitThreshold_zero (C₀ T : ℝ) : explicitThreshold C₀ T 0 = 1 := by
  simp [explicitThreshold]

@[simp] theorem explicitThreshold_one (C₀ T : ℝ) : explicitThreshold C₀ T 1 = 1 := by
  norm_num [explicitThreshold]

theorem explicitThreshold_of_pos (C₀ T : ℝ) {q : ℕ} (hq : 1 ≤ q) :
    explicitThreshold C₀ T q = (q.factorial : ℝ) / (q : ℝ) ^ 2 * thresholdScale C₀ T ^ (q - 1) := by
  rw [explicitThreshold, ite_eq_right (by omega)]

theorem explicitThreshold_pos {C₀ T : ℝ} (hC : 0 < C₀) (hT : 1 < T) (q : ℕ) :
    0 < explicitThreshold C₀ T q := by
  by_cases hq : q = 0
  · simp [hq]
  · rw [explicitThreshold_of_pos C₀ T (by omega)]
    have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
    have hf : 0 < (q.factorial : ℝ) := by exact_mod_cast q.factorial_pos
    have hs := thresholdScale_pos hC hT
    positivity

/-- Exact cancellation of the factorials in a convolution summand. -/
theorem explicitThreshold_convolution_term (C₀ T : ℝ) {q j : ℕ}
    (hj : 1 ≤ j) (hjq : j < q) :
    (q.choose j : ℝ) * explicitThreshold C₀ T j * explicitThreshold C₀ T (q - j) =
      (q.factorial : ℝ) * thresholdScale C₀ T ^ (q - 2) /
        ((j : ℝ) ^ 2 * ((q - j : ℕ) : ℝ) ^ 2) := by
  rw [explicitThreshold_of_pos C₀ T hj, explicitThreshold_of_pos C₀ T (by omega)]
  have hfac : (q.choose j : ℝ) * (j.factorial : ℝ) * ((q - j).factorial : ℝ) = q.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjq.le
  calc
    _ = ((q.choose j : ℝ) * (j.factorial : ℝ) * ((q - j).factorial : ℝ)) *
        (thresholdScale C₀ T ^ (j - 1) * thresholdScale C₀ T ^ (q - j - 1)) /
        ((j : ℝ) ^ 2 * ((q - j : ℕ) : ℝ) ^ 2) := by ring
    _ = _ := by rw [hfac, ← pow_add, show j - 1 + (q - j - 1) = q - 2 by omega]

/-- The convolution condition, with the paper's exact constant `2π²/3`. -/
theorem explicitThreshold_convolution_le {C₀ T : ℝ} (hC : 0 < C₀) (hT : 1 < T)
    {q : ℕ} (hq : 3 ≤ q) :
    thresholdConvolution (explicitThreshold C₀ T) q ≤
      explicitThreshold C₀ T q / (C₀ * T * sqrt (log T)) := by
  have hs := thresholdScale_pos hC hT
  have ht : 0 < T := by linarith
  have hl := log_pos hT
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have he : thresholdConvolution (explicitThreshold C₀ T) q =
      (q.factorial : ℝ) * thresholdScale C₀ T ^ (q - 2) *
        ∑ j ∈ Icc 1 (q / 2), 1 / ((j : ℝ) ^ 2 * ((q - j : ℕ) : ℝ) ^ 2) := by
    unfold thresholdConvolution
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    obtain ⟨hj, hjq⟩ := mem_Icc.1 hj
    rw [explicitThreshold_convolution_term C₀ T hj (by omega)]
    ring
  rw [he]
  calc
    _ ≤ (q.factorial : ℝ) * thresholdScale C₀ T ^ (q - 2) * ((2 * π ^ 2 / 3) / (q : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (half_inverse_square_convolution_bound (by omega)) (by positivity)
    _ = _ := by
      rw [explicitThreshold_of_pos C₀ T (by omega)]
      have hp : thresholdScale C₀ T ^ (q - 1) =
          thresholdScale C₀ T ^ (q - 2) * thresholdScale C₀ T := by
        rw [← pow_succ, show q - 2 + 1 = q - 1 by omega]
      rw [hp]
      unfold thresholdScale
      field_simp

/-- The packaged scale agrees with the displayed sequence in the paper. -/
theorem explicitThreshold_eq_paper {C₀ T : ℝ} (hT : 1 ≤ T) {q : ℕ} (hq : 1 ≤ q) :
    explicitThreshold C₀ T q = (q.factorial : ℝ) / (q : ℝ) ^ 2 *
      (2 * π ^ 2 * C₀ / 3) ^ (q - 1) * T ^ (q - 1) *
        log T ^ (((q - 1 : ℕ) : ℝ) / 2) := by
  rw [explicitThreshold_of_pos C₀ T hq]
  have hs : sqrt (log T) ^ (q - 1) = log T ^ (((q - 1 : ℕ) : ℝ) / 2) := by
    rw [sqrt_eq_rpow, ← rpow_mul_natCast (log_nonneg hT)]
    congr 1
    ring
  unfold thresholdScale
  rw [mul_pow, mul_pow, hs]
  ring

theorem thresholdScale_lower {C₀ T : ℝ} (hC : 0 < C₀) (hT : 1 < T) :
    4 * C₀ * T * sqrt (log T) ≤ thresholdScale C₀ T := by
  have ht : 0 < T := by linarith
  have hπ : (4 : ℝ) ≤ 2 * π ^ 2 / 3 := by nlinarith [pi_gt_three]
  have h := mul_le_mul_of_nonneg_right hπ
    (by positivity : 0 ≤ C₀ * T * sqrt (log T))
  unfold thresholdScale
  nlinarith

theorem nat_sq_le_four_pow_sub_one {q : ℕ} (hq : 1 ≤ q) :
    (q : ℝ) ^ 2 ≤ 4 ^ (q - 1) := by
  have aux : ∀ n : ℕ, n + 1 ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih => rw [pow_succ]; nlinarith
  have h : (q : ℝ) ≤ (2 : ℝ) ^ (q - 1) := by
    have hh := aux (q - 1)
    rw [Nat.sub_add_cancel hq] at hh
    exact_mod_cast hh
  have hsq := mul_self_le_mul_self (Nat.cast_nonneg (α := ℝ) q) h
  have he : (4 : ℝ) ^ (q - 1) = (2 ^ (q - 1)) * 2 ^ (q - 1) := by
    rw [← mul_pow]
    norm_num
  rw [he]
  simpa only [pow_two] using hsq

/-- The factorial growth condition holds at every positive order. -/
theorem explicitThreshold_factorial_lower {C₀ T : ℝ} (hC : 0 < C₀) (hT : 3 ≤ T)
    {q : ℕ} (hq : 1 ≤ q) :
    (q.factorial : ℝ) * (C₀ * T) ^ (q - 1) ≤ explicitThreshold C₀ T q := by
  have ht : 0 < T := by linarith
  have hl : 1 ≤ log T := (show (1 : ℝ) ≤ log 3 by linarith [log_three_gt_d9]).trans
    (log_le_log (by norm_num) hT)
  have hs : 1 ≤ sqrt (log T) := by simpa only [sqrt_one] using sqrt_le_sqrt hl
  have hscale : 4 * C₀ * T ≤ thresholdScale C₀ T := by
    have h := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 4 * C₀ * T)
    have hh : 4 * C₀ * T ≤ 4 * C₀ * T * sqrt (log T) := by simpa only [mul_one] using h
    exact hh.trans (thresholdScale_lower hC (by linarith))
  have hpow : (q : ℝ) ^ 2 * (C₀ * T) ^ (q - 1) ≤ thresholdScale C₀ T ^ (q - 1) := by
    calc
      _ ≤ 4 ^ (q - 1) * (C₀ * T) ^ (q - 1) :=
        mul_le_mul_of_nonneg_right (nat_sq_le_four_pow_sub_one hq) (by positivity)
      _ = (4 * C₀ * T) ^ (q - 1) := by rw [← mul_pow]; congr 1; ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hscale _
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hh := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (α := ℝ) q.factorial)
  rw [explicitThreshold_of_pos C₀ T hq]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hq0)).2
  nlinarith

/-- Every assumption of Proposition 2.2 is met by the sequence in §2.4. -/
theorem explicitThreshold_admissible {C₀ T : ℝ} (hC : 1 ≤ C₀) (hT : 3 ≤ T) :
    AdmissibleThresholds C₀ T (explicitThreshold C₀ T) := by
  have hC0 : 0 < C₀ := by linarith
  have ht : 0 < T := by linarith
  have ht1 : 1 < T := by linarith
  have hlog := log_pos ht1
  refine ⟨explicitThreshold_pos hC0 ht1, by simp, ?_, ?_,
    (fun j hj ↦ explicitThreshold_factorial_lower hC0 hT (by omega)),
    (fun q hq ↦ explicitThreshold_convolution_le hC0 ht1 hq)⟩
  · have h := explicitThreshold_factorial_lower hC0 hT (q := 2) (by norm_num)
    norm_num only [Nat.factorial, Nat.reduceMul, Nat.cast_ofNat, Nat.reduceSub, pow_one] at h
    nlinarith
  · have hs := thresholdScale_lower hC0 ht1
    have hs0 : 0 ≤ 4 * C₀ * T * sqrt (log T) := by positivity
    have hsq := mul_self_le_mul_self hs0 hs
    have he : (4 * C₀ * T * sqrt (log T)) ^ 2 = 16 * C₀ ^ 2 * T ^ 2 * log T := by
      rw [mul_pow, mul_pow, mul_pow, sq_sqrt hlog.le]
      norm_num
    rw [← pow_two, ← pow_two, he] at hsq
    rw [explicitThreshold_of_pos C₀ T (q := 3) (by norm_num)]
    norm_num only [Nat.factorial, Nat.reduceMul, Nat.cast_ofNat, Nat.reduceSub, Nat.reducePow]
    have hnonneg : 0 ≤ C₀ ^ 2 * T ^ 2 * log T := by positivity
    nlinarith

/-- The scale dominates `T`, which absorbs the divisor-count envelope. -/
theorem thresholdScale_ge_T {C₀ T : ℝ} (hC : 1 ≤ C₀) (hT : 3 ≤ T) : T ≤ thresholdScale C₀ T := by
  have ht : 0 < T := by linarith
  have hc : 0 < C₀ := by linarith
  have hl : 1 ≤ log T := (show (1 : ℝ) ≤ log 3 by linarith [log_three_gt_d9]).trans
    (log_le_log (by norm_num) hT)
  have hs : 1 ≤ sqrt (log T) := by simpa only [sqrt_one] using sqrt_le_sqrt hl
  have hscale := thresholdScale_lower hc (by linarith : 1 < T)
  have h1 := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 4 * C₀ * T)
  have h2 := mul_le_mul_of_nonneg_right hC ht.le
  nlinarith

/-- The crude factorial bound needed to recover the divisor maximum. -/
theorem explicitThreshold_upper {C₀ T : ℝ} (hC : 0 < C₀) (hT : 1 < T)
    {q : ℕ} (hq : 1 ≤ q) :
    explicitThreshold C₀ T q ≤ (q : ℝ) ^ q * thresholdScale C₀ T ^ (q - 1) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hs := thresholdScale_pos hC hT
  have hf : (q.factorial : ℝ) ≤ (q : ℝ) ^ q := by exact_mod_cast Nat.factorial_le_pow q
  rw [explicitThreshold_of_pos C₀ T hq]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact (div_le_self (Nat.cast_nonneg _) (one_le_pow₀ hq1)).trans hf

end BretecheTenenbaumMean
