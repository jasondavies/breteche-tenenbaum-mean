module

public import BretecheTenenbaumMean.DyadicGoodSets
public import BretecheTenenbaumMean.Penalty

@[expose] public section

/-! # A logarithmic grid for the good-set exceptional event -/

namespace BretecheTenenbaumMean

open Real Finset

/-- The logarithm of the exact good-set envelope in variables `t=log T`,
`u=log log(3y)`. -/
noncomputable def barrierProfile (δ t u : ℝ) : ℝ :=
  t + u - δ * min (t + u) ((u - criticalSlope * t) ^ 2 / t)

/-- The clipped penalty cannot decrease faster than a fixed linear rate. -/
theorem clipped_penalty_lower_increment {t u v : ℝ} (ht : 0 < t) (hu : 0 ≤ u) (huv : u ≤ v) :
    min (t + u) ((u - criticalSlope * t) ^ 2 / t) - 6 * (v - u) ≤
      min (t + v) ((v - criticalSlope * t) ^ 2 / t) := by
  have hb := criticalSlope_le_three
  have hv : 0 ≤ v := hu.trans huv
  have hquad : (u - criticalSlope * t) ^ 2 / t - 6 * (v - u) ≤
      (v - criticalSlope * t) ^ 2 / t := by
    rw [sub_le_iff_le_add, div_le_iff₀ ht]
    have he : ((v - criticalSlope * t) ^ 2 / t + 6 * (v - u)) * t =
        (v - criticalSlope * t) ^ 2 + 6 * (v - u) * t := by field_simp
    rw [he]
    nlinarith [mul_nonneg (sub_nonneg.2 huv) (add_nonneg hu hv),
      mul_nonneg (sub_nonneg.2 huv) (mul_nonneg (sub_nonneg.2 hb) ht.le)]
  apply le_min
  · have h := min_le_left (t + u) ((u - criticalSlope * t) ^ 2 / t)
    linarith
  · exact (sub_le_sub_right (min_le_right (t + u) ((u - criticalSlope * t) ^ 2 / t)) _).trans hquad

/-- Uniform upper growth of the logarithmic barrier. -/
theorem barrierProfile_increment_le {δ t u v : ℝ} (hδ : 0 ≤ δ) (ht : 0 < t)
    (hu : 0 ≤ u) (huv : u ≤ v) :
    barrierProfile δ t v - barrierProfile δ t u ≤ (1 + 6 * δ) * (v - u) := by
  have h := mul_le_mul_of_nonneg_left (clipped_penalty_lower_increment ht hu huv) hδ
  unfold barrierProfile
  nlinarith

theorem barrierProfile_near_le {δ t u v : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : 0 < t) (hu : 0 ≤ u) (huv : u ≤ v) (hvu : v ≤ u + 1) :
    barrierProfile δ t v ≤ barrierProfile δ t u + 7 := by
  have h := barrierProfile_increment_le hδ ht hu huv
  have hmul := mul_le_mul (show 1 + 6 * δ ≤ 7 by linarith)
    (show v - u ≤ 1 by linarith) (sub_nonneg.2 huv) (by norm_num : (0 : ℝ) ≤ 7)
  linarith

/-- The barrier profile represents the original envelope exactly. -/
theorem goodEnvelope_eq_exp_profile {δ T y : ℝ} (hT : 0 < T) (hy : 1 ≤ y) :
    goodEnvelope δ T y = exp (barrierProfile δ (log T) (log (log (3 * y)))) := by
  have hL : 0 < log (3 * y) := log_pos (by linarith)
  unfold goodEnvelope barrierProfile penalty
  rw [log_mul hT.ne' hL.ne', exp_sub, exp_add, exp_log hT, exp_log hL, exp_neg]
  ring

noncomputable def goodSetGrid (j : ℕ) : ℝ := exp (exp (j : ℝ)) / 3

theorem goodSetGrid_ge_one {j : ℕ} (hj : 1 ≤ j) : 1 ≤ goodSetGrid j := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h1 := add_one_le_exp (j : ℝ)
  have h2 := add_one_le_exp (exp (j : ℝ))
  unfold goodSetGrid
  linarith

/-- Exact logarithmic coordinates of the grid points. -/
theorem loglog_goodSetGrid (j : ℕ) : log (log (3 * goodSetGrid j)) = j := by
  unfold goodSetGrid
  rw [show 3 * (exp (exp (j : ℝ)) / 3) = exp (exp (j : ℝ)) by ring, log_exp, log_exp]

/-- Moving a cutoff upward can only increase its small-prime divisor count. -/
theorem tau_smallPrimePart_mono (n : ℕ) {y z : ℝ} (hyz : y ≤ z) :
    tau (smallPrimePart n y) ≤ tau (smallPrimePart n z) := by
  apply tau_le_of_dvd (smallPrimePart_ne_zero n z)
  unfold smallPrimePart
  apply prod_dvd_prod_of_subset _ _
  intro p hp
  exact mem_filter.2 ⟨(mem_filter.1 hp).1, (mem_filter.1 hp).2.trans_le hyz⟩

/-- Round the logarithmic coordinate upward; this costs at most `exp 7` in
the exact envelope and preserves the direction of the cutoff. -/
theorem exists_goodSetGrid_above {δ T y : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hT : 1 < T) (hy : 1 ≤ y) : ∃ j : ℕ, 1 ≤ j ∧ y ≤ goodSetGrid j ∧
      goodEnvelope δ T (goodSetGrid j) ≤ exp 7 * goodEnvelope δ T y := by
  let u := log (log (3 * y))
  have h3 : 1 < log 3 := by linarith [log_three_gt_d9]
  have hL : 1 < log (3 * y) := h3.trans_le (log_le_log (by norm_num) (by linarith))
  have hu : 0 < u := log_pos hL
  let j := ⌈u⌉₊
  have hj : 1 ≤ j := Nat.one_le_ceil_iff.2 hu
  have huj : u ≤ (j : ℝ) := Nat.le_ceil u
  have hju : (j : ℝ) ≤ u + 1 := (Nat.ceil_lt_add_one hu.le).le
  refine ⟨j, hj, ?_, ?_⟩
  · have h := exp_le_exp.2 (exp_le_exp.2 huj)
    dsimp only [u] at h
    rw [exp_log (by linarith : 0 < log (3 * y)), exp_log (by linarith : 0 < 3 * y)] at h
    unfold goodSetGrid
    linarith
  · rw [goodEnvelope_eq_exp_profile (by linarith) (goodSetGrid_ge_one hj), loglog_goodSetGrid,
      goodEnvelope_eq_exp_profile (by linarith) hy, ← exp_add]
    apply exp_le_exp.2
    have h := barrierProfile_near_le hδ hδ1 (log_pos hT) hu.le huj hju
    dsimp only [u] at h
    linarith

/-- Every failure of the continuum of good-set constraints is detected at an
integer grid point. This includes witnesses larger than the ambient cutoff. -/
theorem goodSet_failure_grid {δ T : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hT : 1 < T)
    {n : ℕ} (hn : Squarefree n) (hbad : n ∉ goodSet δ T) :
    ∃ j : ℕ, 1 ≤ j ∧ exp (-7) * goodEnvelope δ T (goodSetGrid j) <
      tau (smallPrimePart n (goodSetGrid j)) := by
  have hnot : ¬ ∀ y : ℝ, 1 ≤ y → tau (smallPrimePart n y) ≤ goodEnvelope δ T y :=
    fun h ↦ hbad ⟨hn, h⟩
  obtain ⟨y, hy⟩ := not_forall.1 hnot
  have hy' := not_imp.1 hy
  obtain ⟨j, hj, hyj, hB⟩ := exists_goodSetGrid_above hδ hδ1 hT hy'.1
  refine ⟨j, hj, ?_⟩
  have hb : exp (-7) * goodEnvelope δ T (goodSetGrid j) ≤ goodEnvelope δ T y := by
    have h := mul_le_mul_of_nonneg_left hB (exp_pos (-7)).le
    calc _ ≤ exp (-7) * (exp 7 * goodEnvelope δ T y) := h
      _ = _ := by rw [← mul_assoc, ← exp_add]; norm_num
  exact (hb.trans_lt (lt_of_not_ge hy'.2)).trans_le (tau_smallPrimePart_mono n hyj)

end BretecheTenenbaumMean
