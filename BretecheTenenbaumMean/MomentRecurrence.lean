module

public import BretecheTenenbaumMean.Moments

@[expose] public section

/-! # Mixed moments and adjoining a prime

This module gives the full binomial expansion underlying (1.4)--(1.5).
-/

namespace BretecheTenenbaumMean

open Real MeasureTheory Finset

/-- The mixed moment `N_{j,q}(n,p)` in (1.5). -/
noncomputable def mixedMoment (j q n p : ℕ) : ℝ :=
  ∫ u : ℝ, delta n u ^ j * delta n (u - log p) ^ (q - j)

theorem integrable_mixedMoment (j q n p : ℕ) (hq : 1 ≤ q) :
    Integrable (fun u => delta n u ^ j * delta n (u - log p) ^ (q - j)) := by
  by_cases hj : j = 0
  · simp only [hj, pow_zero, Nat.sub_zero, one_mul]
    exact (integrable_delta_pow n q hq).comp_sub_right _
  · apply (integrable_delta_pow n j (by omega)).mul_bdd
      (((measurable_delta n).comp (measurable_id.sub_const _)).pow_const _).aestronglyMeasurable
      (c := tau n ^ (q - j))
    apply Filter.Eventually.of_forall
    intro u
    change ‖delta n (u - log p) ^ (q - j)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (delta_nonneg n _) _)]
    exact pow_le_pow_left₀ (delta_nonneg n _) (delta_le_tau n _) _

theorem mixedMoment_nonneg (j q n p : ℕ) : 0 ≤ mixedMoment j q n p :=
  integral_nonneg fun _ => mul_nonneg (pow_nonneg (delta_nonneg _ _) _)
    (pow_nonneg (delta_nonneg _ _) _)

@[simp] theorem mixedMoment_zero (q n p : ℕ) : mixedMoment 0 q n p = moment q n := by
  simp only [mixedMoment, pow_zero, Nat.sub_zero, one_mul]
  exact integral_sub_right_eq_self (fun u => delta n u ^ q) (log p)

@[simp] theorem mixedMoment_self (q n p : ℕ) : mixedMoment q q n p = moment q n := by
  simp [mixedMoment, moment]

/-- The exact expansion, retaining both ends and all mixed terms. -/
theorem moment_mul_prime {n p q : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) (hq : 1 ≤ q) :
    moment q (n * p) = ∑ j ∈ range (q + 1),
      (q.choose j : ℝ) * mixedMoment j q n p := by
  simp only [moment, delta_mul_prime hp hpn, add_pow]
  rw [integral_finsetSum _ (fun j _ => (integrable_mixedMoment j q n p hq).mul_const _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_mul_const]
  exact mul_comm _ _

theorem tau_mul_prime {n p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) :
    tau (n * p) = 2 * tau n := by
  have hc := (hp.coprime_iff_not_dvd.mpr hpn).symm.card_divisors_mul
  simp only [tau, hc, Nat.cast_mul, hp.divisors]
  simp [hp.ne_one.symm, mul_comm]

theorem tau_pos {n : ℕ} (hn : n ≠ 0) : 0 < tau n := by
  unfold tau
  exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩

/-- A normalized moment increases when a prime not already dividing `n` is added. -/
theorem normalized_moment_le_mul_prime {n p q : ℕ} (hn : n ≠ 0)
    (hp : p.Prime) (hpn : ¬ p ∣ n) (hq : 1 ≤ q) :
    moment q n / tau n ≤ moment q (n * p) / tau (n * p) := by
  rw [tau_mul_prime hp hpn]
  apply (div_le_div_iff₀ (tau_pos hn) (mul_pos (by norm_num) (tau_pos hn))).mpr
  nlinarith [two_mul_moment_le hp hpn hq, tau_pos hn]

theorem normalized_moment_le_mul (n k q : ℕ) (hsq : Squarefree (n * k)) (hq : 1 ≤ q) :
    moment q n / tau n ≤ moment q (n * k) / tau (n * k) := by
  induction k using induction_on_primes with
  | zero => simp at hsq
  | one => simp
  | prime_mul p k hp ih =>
    have hsq' : Squarefree ((n * k) * p) := by simpa [mul_assoc, mul_comm, mul_left_comm] using hsq
    have hnk : Squarefree (n * k) := hsq'.squarefree_of_dvd (dvd_mul_right _ _)
    have hpn : ¬ p ∣ n * k := hp.coprime_iff_not_dvd.mp
      (Nat.coprime_of_squarefree_mul hsq').symm
    have hstep := normalized_moment_le_mul_prime hnk.ne_zero hp hpn hq
    exact (ih hnk).trans (by simpa [mul_assoc, mul_comm, mul_left_comm] using hstep)

/-- On squarefree integers, normalized moments are increasing under divisibility. -/
theorem normalized_moment_le_of_dvd {d n q : ℕ} (hn : Squarefree n)
    (hd : d ∣ n) (hq : 1 ≤ q) : moment q d / tau d ≤ moment q n / tau n := by
  obtain ⟨k, rfl⟩ := hd
  exact normalized_moment_le_mul d k q hn hq

end BretecheTenenbaumMean
