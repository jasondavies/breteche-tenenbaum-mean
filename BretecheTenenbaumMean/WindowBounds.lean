module

public import BretecheTenenbaumMean.Moments

@[expose] public section

/-! # Recovering the maximum from moments and the pigeonhole bound -/

namespace BretecheTenenbaumMean

open Real MeasureTheory Set

/-- Two adjacent windows cover any unit window whose left endpoint lies between theirs. -/
theorem divisorWindow_le_adjacent (n : ℕ) {u v : ℝ} (huv : u ≤ v) (hvu : v ≤ u + 1) :
    divisorWindow n u ≤ divisorWindow n v + divisorWindow n (v - 1) := by
  classical
  unfold divisorWindow
  apply le_trans (Finset.card_le_card (t :=
    (n.divisors.filter fun d : ℕ => v < log d ∧ log d ≤ v + 1) ∪
      (n.divisors.filter fun d : ℕ => v - 1 < log d ∧ log d ≤ v - 1 + 1)) ?_)
    (Finset.card_union_le _ _)
  intro d hd
  obtain ⟨hd, h₁, h₂⟩ := Finset.mem_filter.mp hd
  apply Finset.mem_union.mpr
  rcases lt_or_ge v (log d) with h | h
  · exact Or.inl (Finset.mem_filter.mpr ⟨hd, h, by linarith⟩)
  · exact Or.inr (Finset.mem_filter.mpr ⟨hd, by constructor <;> linarith⟩)

theorem delta_le_adjacent (n : ℕ) {u v : ℝ} (huv : u ≤ v) (hvu : v ≤ u + 1) :
    delta n u ≤ delta n v + delta n (v - 1) := by
  unfold delta
  exact_mod_cast divisorWindow_le_adjacent n huv hvu

theorem delta_pow_le_moment (n q : ℕ) (hq : 1 ≤ q) (u : ℝ) :
    delta n u ^ q ≤ 2 ^ q * moment q n := by
  have hi := integrable_delta_pow n q hq
  have hs : Integrable (fun v => delta n (v - 1) ^ q) := hi.comp_sub_right 1
  have hb := (hi.add hs).const_mul ((2 : ℝ) ^ (q - 1))
  calc
    delta n u ^ q = ∫ v in Icc u (u + 1), delta n u ^ q := by
      simp [Real.volume_real_Icc]
    _ ≤ ∫ v in Icc u (u + 1), 2 ^ (q - 1) * (delta n v ^ q + delta n (v - 1) ^ q) := by
      apply setIntegral_mono_on (integrableOn_const (measure_Icc_lt_top.ne))
        hb.integrableOn measurableSet_Icc
      intro v hv
      exact (pow_le_pow_left₀ (delta_nonneg n u) (delta_le_adjacent n hv.1 hv.2) q).trans
        (add_pow_le (delta_nonneg n v) (delta_nonneg n (v - 1)) q)
    _ ≤ ∫ v, 2 ^ (q - 1) * (delta n v ^ q + delta n (v - 1) ^ q) := by
      apply setIntegral_le_integral hb
      exact Filter.Eventually.of_forall fun v => mul_nonneg (by positivity)
        (add_nonneg (pow_nonneg (delta_nonneg n v) _) (pow_nonneg (delta_nonneg n _) _))
    _ = 2 ^ q * moment q n := by
      rw [integral_const_mul, integral_add hi hs,
        integral_sub_right_eq_self (fun v => delta n v ^ q) 1]
      change 2 ^ (q - 1) * (moment q n + moment q n) = 2 ^ q * moment q n
      have hpow : (2 : ℝ) ^ q = 2 ^ (q - 1) * 2 := by
        conv_lhs => rw [← Nat.sub_add_cancel hq]
        exact pow_succ _ _
      rw [hpow]
      ring

/-- The moment-to-maximum estimate used in §2.4, without taking roots. -/
theorem max_pow_le_moment (n q : ℕ) (hq : 1 ≤ q) :
    (hooleyDelta n : ℝ) ^ q ≤ 2 ^ q * moment q n := by
  obtain ⟨u, hu⟩ := hooleyDelta_attained n
  simpa only [delta, hu] using delta_pow_le_moment n q hq u

theorem delta_eq_zero_outside (n : ℕ) {u : ℝ} (hu : u ∉ Ico (-1) (log n)) :
    delta n u = 0 := by
  classical
  suffices h : (n.divisors.filter fun d : ℕ => u < log d ∧ log d ≤ u + 1) = ∅ by
    simp [delta, divisorWindow, h]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  obtain ⟨hd, hdu, hud⟩ := Finset.mem_filter.mp hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have hdn : (d : ℝ) ≤ n := by
    exact_mod_cast Nat.divisor_le hd
  exact hu ⟨by linarith [Real.log_nonneg hd1], hdu.trans_le (Real.log_le_log hdpos hdn)⟩

/-- An explicit form of the pigeonhole bound used in §4. -/
theorem tau_le_max_mul_log (n : ℕ) :
    tau n ≤ (hooleyDelta n : ℝ) * (log n + 1) := by
  have hi : Integrable ((Ico (-1) (log n)).indicator (fun _ : ℝ => (hooleyDelta n : ℝ))) :=
    (integrableOn_const (measure_Ico_lt_top.ne)).integrable_indicator measurableSet_Ico
  have hlog : 0 ≤ log n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  calc
    tau n = ∫ u, delta n u := (integral_delta n).symm
    _ ≤ ∫ u, (Ico (-1) (log n)).indicator (fun _ : ℝ => (hooleyDelta n : ℝ)) u := by
      apply integral_mono (integrable_delta n) hi
      intro u
      by_cases hu : u ∈ Ico (-1) (log n)
      · rw [Set.indicator_of_mem hu]
        exact delta_le_max n u
      · rw [Set.indicator_of_notMem hu, delta_eq_zero_outside n hu]
    _ = (hooleyDelta n : ℝ) * (log n + 1) := by
      rw [integral_indicator_const _ measurableSet_Ico]
      simp only [Real.volume_real_Ico, sub_neg_eq_add, smul_eq_mul]
      rw [max_eq_left (by linarith : 0 ≤ log n + 1), mul_comm]

end BretecheTenenbaumMean
