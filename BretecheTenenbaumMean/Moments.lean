module

public import BretecheTenenbaumMean.Delta

@[expose] public section

/-! # The moments of the divisor-window function

The integral is with respect to Lebesgue measure on the whole real line.
In particular, integrability is proved before using integral identities.
-/

namespace BretecheTenenbaumMean

open Finset Real MeasureTheory Set

theorem delta_nonneg (n : ℕ) (u : ℝ) : 0 ≤ delta n u := Nat.cast_nonneg _

theorem delta_le_tau (n : ℕ) (u : ℝ) : delta n u ≤ tau n := by
  unfold delta tau
  exact_mod_cast (show divisorWindow n u ≤ n.divisors.card from divisorWindow_le_card n u)

theorem delta_le_max (n : ℕ) (u : ℝ) : delta n u ≤ (hooleyDelta n : ℝ) := by
  unfold delta
  exact_mod_cast divisorWindow_le_delta n u

theorem delta_eq_sum_indicator (n : ℕ) (u : ℝ) :
    delta n u = ∑ d ∈ n.divisors,
      (Ico (log d - 1) (log d)).indicator (fun _ : ℝ => (1 : ℝ)) u := by
  classical
  rw [delta, divisorWindow_eq_sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro d _
  have h : (u < log d ∧ log d ≤ u + 1) ↔ u ∈ Ico (log d - 1) (log d) := by
    simp only [Set.mem_Ico]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, h, indicator_apply]

theorem integrable_divisor_indicator (d : ℕ) :
    Integrable ((Ico (log d - 1) (log d)).indicator (fun _ : ℝ => (1 : ℝ))) := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Ico
  exact integrableOn_const (measure_Ico_lt_top.ne)

theorem integrable_delta (n : ℕ) : Integrable (delta n) := by
  simp_rw [show delta n = (fun u => ∑ d ∈ n.divisors,
      (Ico (log d - 1) (log d)).indicator (fun _ : ℝ => (1 : ℝ)) u) from
    funext (delta_eq_sum_indicator n)]
  exact integrable_finsetSum _ (fun d _ => integrable_divisor_indicator d)

theorem measurable_delta (n : ℕ) : Measurable (delta n) := by
  have h := funext (delta_eq_sum_indicator n)
  rw [h]
  exact Finset.measurable_sum _ (fun d _ => measurable_const.indicator measurableSet_Ico)

theorem integrable_delta_pow (n q : ℕ) (hq : 1 ≤ q) :
    Integrable (fun u => delta n u ^ q) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  apply ((integrable_delta n).const_mul (tau n ^ k)).mono'
    ((measurable_delta n).pow_const _).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro u
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (delta_nonneg n u) _), pow_succ]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (delta_nonneg n u)
    (delta_le_tau n u) _) (delta_nonneg n u)

theorem integral_delta (n : ℕ) : ∫ u, delta n u = tau n := by
  simp_rw [delta_eq_sum_indicator]
  rw [integral_finsetSum _ (fun d _ => integrable_divisor_indicator d)]
  simp [measurableSet_Ico, Real.volume_real_Ico, tau]

@[simp] theorem moment_one (n : ℕ) : moment 1 n = tau n := by
  simpa [moment] using integral_delta n

theorem moment_nonneg (q n : ℕ) : 0 ≤ moment q n :=
  integral_nonneg fun u => pow_nonneg (delta_nonneg n u) q

/-- The elementary bound in the footnote to §2.3. -/
theorem moment_le_max_mul_tau (n q : ℕ) (hq : 1 ≤ q) :
    moment q n ≤ (hooleyDelta n : ℝ) ^ (q - 1) * tau n := by
  rw [← integral_delta, ← integral_const_mul]
  apply integral_mono (integrable_delta_pow n q hq) ((integrable_delta n).const_mul _)
  intro u
  change delta n u ^ q ≤ _
  rw [← Nat.sub_add_cancel hq, pow_succ]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (delta_nonneg n u) (delta_le_max n u) _) (delta_nonneg n u)

theorem moment_le_tau_pow (n q : ℕ) (hq : 1 ≤ q) : moment q n ≤ tau n ^ q := by
  calc
    moment q n ≤ (hooleyDelta n : ℝ) ^ (q - 1) * tau n := moment_le_max_mul_tau n q hq
    _ ≤ tau n ^ (q - 1) * tau n := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      unfold tau
      exact_mod_cast hooleyDelta_le_card n
    _ = tau n ^ q := by rw [← pow_succ, Nat.sub_add_cancel hq]

/-- Splitting a window when a new prime is adjoined, preceding (1.4). -/
theorem delta_mul_prime {n p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) (u : ℝ) :
    delta (n * p) u = delta n u + delta n (u - log p) := by
  have hcop : p.Coprime n := hp.coprime_iff_not_dvd.mpr hpn
  have h := divisorWindow_mul hcop u
  rw [hp.divisors] at h
  simpa [delta, mul_comm n p, Finset.sum_insert, hp.ne_one.symm] using congrArg (Nat.cast : ℕ → ℝ) h

/-- The lower half of the moment recurrence (1.4). -/
theorem two_mul_moment_le {n p q : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) (hq : 1 ≤ q) :
    2 * moment q n ≤ moment q (n * p) := by
  have hi := integrable_delta_pow n q hq
  have hs : Integrable (fun u => delta n (u - log p) ^ q) := hi.comp_sub_right (log p)
  calc
    2 * moment q n = (∫ u, delta n u ^ q) + ∫ u, delta n (u - log p) ^ q := by
      rw [integral_sub_right_eq_self (fun u => delta n u ^ q) (log p)]; simp [moment, two_mul]
    _ = ∫ u, delta n u ^ q + delta n (u - log p) ^ q := (integral_add hi hs).symm
    _ ≤ moment q (n * p) := by
      apply integral_mono (hi.add hs) (integrable_delta_pow _ _ hq)
      intro u
      change delta n u ^ q + delta n (u - log p) ^ q ≤ delta (n * p) u ^ q
      rw [delta_mul_prime hp hpn]
      exact pow_add_pow_le (delta_nonneg n u) (delta_nonneg n _) (by omega)

end BretecheTenenbaumMean
