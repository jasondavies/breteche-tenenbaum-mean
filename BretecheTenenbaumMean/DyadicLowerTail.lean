module

public import BretecheTenenbaumMean.LowerTailReduction
public import BretecheTenenbaumMean.ScaleWindowCount

@[expose] public section

/-! # The lower moment tail at dyadic thresholds -/

namespace BretecheTenenbaumMean

open Finset Real

/-- The central window has enough separated scales to supply a dyadic lower
tail. The ambient cutoff `exp(2^(4t))` is explicit. -/
theorem dyadic_second_moment_lower_tail : ∃ c > 0, ∃ K ≥ (1 : ℝ), ∃ t₀ : ℕ,
    ∀ t : ℕ, t₀ ≤ t → ∀ x : ℝ, exp ((2 : ℝ) ^ (4 * t)) ≤ x →
      c / (2 : ℝ) ^ t ≤ probability x {n | (2 : ℝ) ^ t / (K + 1) ≤ moment 2 n / tau n} := by
  obtain ⟨m, hm, K, hK, L₀, hL₀, hreduce⟩ := lower_tail_dyadic_reduction
  obtain ⟨c, hc, T₀, hT₀, hmarg⟩ := central_dyadic_marginal_lower
  obtain ⟨t₀, ht₀⟩ := exists_nat_gt (max 1 (max T₀ (max (2 * L₀) (4 * (m : ℝ) ^ 2))))
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  refine ⟨c / (8 * m), by positivity, K, hK, t₀, fun t ht x hx ↦ ?_⟩
  have hbase : max 1 (max T₀ (max (2 * L₀) (4 * (m : ℝ) ^ 2))) ≤ (t : ℝ) :=
    ht₀.le.trans (by exact_mod_cast ht)
  have ht1 : (1 : ℝ) ≤ t := (le_max_left _ _).trans hbase
  have htT : T₀ ≤ (t : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hbase)
  have htL : 2 * L₀ ≤ (t : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hbase))
  have htm : 4 * (m : ℝ) ^ 2 ≤ t :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hbase))
  let s := scaleWindow m t
  have hwindow : ∀ i ∈ s, criticalSlope * t ≤ (m * i : ℕ) ∧
      (m * i : ℕ) ≤ criticalSlope * t + sqrt t := fun i hi ↦ scaleWindow_bounds hm hi
  have hbounds : ∀ i ∈ s,
      (t : ℝ) / 2 ≤ (m * i : ℕ) * log 2 ∧
      (m * i : ℕ) * log 2 ≤ 4 * t ∧
      (m * i + t : ℕ) ≤ 4 * ((m * i : ℕ) * log 2) ∧
      ((m * i + t : ℕ) - 2 * ((m * i : ℕ) * log 2)) ^ 2 ≤ 2 * ((m * i : ℕ) * log 2) :=
    fun i hi ↦ central_dyadic_window_bounds ht1 (hwindow i hi).1 (hwindow i hi).2
  have hcut : ∀ i ∈ s, exp ((2 : ℝ) ^ (m * i)) ≤ x := by
    intro i hi
    have hroot : sqrt (t : ℝ) ≤ t := by
      nlinarith [sq_sqrt (show (0 : ℝ) ≤ t by positivity), sqrt_nonneg (t : ℝ)]
    have hγ := mul_le_mul_of_nonneg_right criticalSlope_le_three (Nat.cast_nonneg (α := ℝ) t)
    have hidxR : ((m * i : ℕ) : ℝ) ≤ (4 : ℝ) * t := by
      push_cast
      have he := (hwindow i hi).2
      push_cast at he
      linarith
    have hidx : m * i ≤ 4 * t := by exact_mod_cast hidxR
    exact (exp_le_exp.2 (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hidx)).trans hx
  have htail := hreduce x s t hcut (fun i hi ↦ by linarith [(hbounds i hi).1])
    (fun i hi ↦ (hbounds i hi).2.2.1)
  have hsqrt : 0 < sqrt (t : ℝ) := sqrt_pos.2 (by linarith)
  have hcard : sqrt (t : ℝ) / (2 * m) ≤ (s.card : ℝ) := scaleWindow_card_lower hm htm
  calc
    _ = (1 / 4 : ℝ) * ((sqrt (t : ℝ) / (2 * m)) *
        (c / ((2 : ℝ) ^ t * sqrt t))) := by field_simp; ring
    _ ≤ (1 / 4 : ℝ) * ((s.card : ℝ) * (c / ((2 : ℝ) ^ t * sqrt t))) := by
      gcongr
    _ = (1 / 4 : ℝ) * ∑ i ∈ s, (c / ((2 : ℝ) ^ t * sqrt t)) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ (1 / 4 : ℝ) * ∑ i ∈ s, probability (exp ((2 : ℝ) ^ (m * i)))
        {n | n.primeFactors.card = m * i + t} := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact sum_le_sum (fun i hi ↦ hmarg (m * i) t htT (hwindow i hi).1 (hwindow i hi).2)
    _ ≤ _ := htail

end BretecheTenenbaumMean
