module

public import BretecheTenenbaumMean.WeightedMangoldtSquare
public import BretecheTenenbaumMean.DeltaLogAverage
public import BretecheTenenbaumMean.GoodSets

@[expose] public section

/-! # Removing logarithmic averaging from the squared Delta function -/

namespace BretecheTenenbaumMean

open Finset Real
open scoped ArithmeticFunction

noncomputable def deltaSquaredArithmetic : ArithmeticFunction ℝ :=
  ⟨fun n ↦ (hooleyDelta n : ℝ) ^ 2, by simp⟩

@[simp] lemma deltaSquaredArithmetic_apply (n : ℕ) : deltaSquaredArithmetic n = (hooleyDelta n : ℝ) ^ 2 := rfl

/-- Divisor decomposition and the identity `log = 1 * Λ` control the logarithmic weight. -/
lemma delta_sq_mul_log_le_convolution (n : ℕ) :
    (hooleyDelta n : ℝ) ^ 2 * log n ≤ (deltaSquaredArithmetic * divisorSquareMangoldt) n := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal' (fun a b ↦ deltaSquaredArithmetic a * divisorSquareMangoldt b),
    ← ArithmeticFunction.vonMangoldt_sum, mul_sum]
  apply sum_le_sum
  intro d hd
  have hdvd := Nat.dvd_of_mem_divisors hd
  have h := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (hooleyDelta (d * (n / d))))
    (hooleyDelta_mul_le_tau d (n / d)) 2
  rw [Nat.mul_div_cancel' hdvd, mul_pow] at h
  simpa only [divisorSquareMangoldt_apply, deltaSquaredArithmetic_apply, mul_assoc, mul_left_comm, mul_comm]
    using mul_le_mul_of_nonneg_right h (ArithmeticFunction.vonMangoldt_nonneg (n := d))

/-- Chebyshev's bound gives a harmonic majorant for the logarithmically weighted sum. -/
theorem delta_sq_log_sum_le_harmonic : ∃ C > 0, ∀ N : ℕ,
    (∑ n ∈ Ioc 0 N, (hooleyDelta n : ℝ) ^ 2 * log n) ≤
      C * N * ∑ n ∈ Ioc 0 N, (hooleyDelta n : ℝ) ^ 2 / n := by
  obtain ⟨C, hC, hbound⟩ := sum_divisorSquareMangoldt_le
  refine ⟨C, hC, fun N ↦ ?_⟩
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, (deltaSquaredArithmetic * divisorSquareMangoldt) n :=
      sum_le_sum (fun n _ ↦ delta_sq_mul_log_le_convolution n)
    _ = ∑ n ∈ Ioc 0 N, (hooleyDelta n : ℝ) ^ 2 *
        ∑ m ∈ Ioc 0 (N / n), divisorSquareMangoldt m :=
      ArithmeticFunction.sum_Ioc_mul_eq_sum_sum _ _ _
    _ ≤ ∑ n ∈ Ioc 0 N, (hooleyDelta n : ℝ) ^ 2 * (C * ((N : ℝ) / n)) := by
      apply sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have hn' := mem_Ioc.1 hn
      have hdiv : 1 ≤ N / n := (Nat.one_le_div_iff hn'.1).2 hn'.2
      have h := hbound ((N / n : ℕ) : ℝ) (by exact_mod_cast hdiv)
      rw [Nat.floor_natCast] at h
      exact h.trans (mul_le_mul_of_nonneg_left Nat.cast_div_le hC.le)
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro n _; ring

/-- Integers below `exp(log x/3)` contribute at most `x`; above this cutoff
the logarithmic weight is at least `(log x)/3`. -/
lemma delta_sq_sum_le_log_sum {x : ℝ} (hx : 2 ≤ x) :
    quadraticSum x ≤ x + 3 / log x *
      ∑ n ∈ Ioc 0 ⌊x⌋₊, (hooleyDelta n : ℝ) ^ 2 * log n := by
  classical
  let R := exp (log x / 3)
  let S := (Ioc 0 ⌊x⌋₊).filter (fun n : ℕ ↦ (n : ℝ) ≤ R)
  let L := (Ioc 0 ⌊x⌋₊).filter (fun n : ℕ ↦ ¬(n : ℝ) ≤ R)
  have hx0 : 0 ≤ x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hs0 : 0 < R := exp_pos _
  have hR : R ^ 3 = x := by
    calc
      _ = exp ((3 : ℝ) * (log x / 3)) := by simpa only [Nat.cast_ofNat] using (exp_nat_mul (log x / 3) 3).symm
      _ = x := by rw [show (3 : ℝ) * (log x / 3) = log x by ring, exp_log (by linarith : 0 < x)]
  have hsmall : (∑ n ∈ S, (hooleyDelta n : ℝ) ^ 2) ≤ x := by
    have hsub : S ⊆ Ioc 0 ⌊R⌋₊ := by
      intro n hn
      obtain ⟨hn, hs⟩ := mem_filter.1 hn
      exact mem_Ioc.2 ⟨(mem_Ioc.1 hn).1, Nat.le_floor hs⟩
    have hc : (S.card : ℝ) ≤ R := by
      have h := card_le_card hsub
      simp only [Nat.card_Ioc, Nat.sub_zero] at h
      exact (Nat.cast_le.2 h).trans (Nat.floor_le hs0.le)
    calc
      _ ≤ ∑ _ ∈ S, R ^ 2 := by
        apply sum_le_sum
        intro n hn
        exact pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (hooleyDelta n))
          ((Nat.cast_le.2 (hooleyDelta_le_self n)).trans (mem_filter.1 hn).2) 2
      _ = S.card * R ^ 2 := by simp
      _ ≤ R * R ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
      _ = x := by nlinarith [hR]
  have hlarge : (∑ n ∈ L, (hooleyDelta n : ℝ) ^ 2) ≤
      3 / log x * ∑ n ∈ Ioc 0 ⌊x⌋₊, (hooleyDelta n : ℝ) ^ 2 * log n := by
    calc
      _ ≤ ∑ n ∈ L, 3 / log x * ((hooleyDelta n : ℝ) ^ 2 * log n) := by
        apply sum_le_sum
        intro n hn
        have hn' := mem_filter.1 hn
        have hlog : log x / 3 ≤ log n := by
          rw [← log_exp (log x / 3)]
          exact log_le_log hs0 (le_of_lt (lt_of_not_ge hn'.2))
        have hfactor : 1 ≤ 3 / log x * log n := by
          rw [div_mul_eq_mul_div]
          apply (le_div_iff₀ hl).2
          linarith
        nlinarith [mul_le_mul_of_nonneg_right hfactor (sq_nonneg (hooleyDelta n : ℝ))]
      _ = 3 / log x * ∑ n ∈ L, (hooleyDelta n : ℝ) ^ 2 * log n := (mul_sum _ _ _).symm
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro n hn _
        exact mul_nonneg (sq_nonneg _) (log_nonneg (by exact_mod_cast (mem_Ioc.1 hn).1))
  have hsplit := sum_filter_add_sum_filter_not (Ioc 0 ⌊x⌋₊)
    (fun n : ℕ ↦ (n : ℝ) ≤ R) (fun n ↦ (hooleyDelta n : ℝ) ^ 2)
  have hinterval : Icc 1 ⌊x⌋₊ = Ioc 0 ⌊x⌋₊ := by ext n; simp; omega
  unfold quadraticSum
  rw [hinterval, ← hsplit]
  exact add_le_add hsmall hlarge

/-- Reduction of the ordinary mean to the harmonic sum over all integers. -/
theorem quadraticSum_le_harmonic : ∃ C > 0, ∀ x : ℝ, 2 ≤ x →
    quadraticSum x ≤ x + C * x / log x *
      ∑ n ∈ Ioc 0 ⌊x⌋₊, (hooleyDelta n : ℝ) ^ 2 / n := by
  obtain ⟨C, hC, h⟩ := delta_sq_log_sum_le_harmonic
  refine ⟨3 * C, by positivity, fun x hx ↦ ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hs : 0 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, (hooleyDelta n : ℝ) ^ 2 / n :=
    sum_nonneg (fun _ _ ↦ by positivity)
  calc
    _ ≤ x + 3 / log x * ∑ n ∈ Ioc 0 ⌊x⌋₊, (hooleyDelta n : ℝ) ^ 2 * log n :=
      delta_sq_sum_le_log_sum hx
    _ ≤ x + 3 / log x * (C * ⌊x⌋₊ * ∑ n ∈ Ioc 0 ⌊x⌋₊, (hooleyDelta n : ℝ) ^ 2 / n) := by
      gcongr
      exact h ⌊x⌋₊
    _ ≤ x + 3 / log x * (C * x * ∑ n ∈ Ioc 0 ⌊x⌋₊, (hooleyDelta n : ℝ) ^ 2 / n) := by
      gcongr
      exact Nat.floor_le hx0
    _ = _ := by ring

end BretecheTenenbaumMean
