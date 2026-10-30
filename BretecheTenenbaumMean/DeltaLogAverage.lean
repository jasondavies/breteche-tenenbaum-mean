module

public import BretecheTenenbaumMean.WeightedMangoldt
public import BretecheTenenbaumMean.GoodSets

@[expose] public section

/-! # Removing logarithmic averaging from the Delta function -/

namespace BretecheTenenbaumMean

open Finset Real
open scoped ArithmeticFunction

noncomputable def deltaArithmetic : ArithmeticFunction ℝ :=
  ⟨fun n ↦ (hooleyDelta n : ℝ), by simp⟩

@[simp] lemma deltaArithmetic_apply (n : ℕ) : deltaArithmetic n = (hooleyDelta n : ℝ) := rfl

/-- Divisor decomposition and the identity `log = 1 * Λ` control the logarithmic weight. -/
lemma delta_mul_log_le_convolution (n : ℕ) :
    (hooleyDelta n : ℝ) * log n ≤ (deltaArithmetic * divisorMangoldt) n := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal' (fun a b ↦ deltaArithmetic a * divisorMangoldt b),
    ← ArithmeticFunction.vonMangoldt_sum, mul_sum]
  apply sum_le_sum
  intro d hd
  have hdvd := Nat.dvd_of_mem_divisors hd
  have h := hooleyDelta_mul_le_tau d (n / d)
  rw [Nat.mul_div_cancel' hdvd] at h
  simpa only [divisorMangoldt_apply, deltaArithmetic_apply, mul_assoc, mul_left_comm, mul_comm]
    using mul_le_mul_of_nonneg_right h (ArithmeticFunction.vonMangoldt_nonneg (n := d))

/-- Chebyshev's bound gives a harmonic majorant for the logarithmically weighted sum. -/
theorem delta_log_sum_le_harmonic : ∃ C > 0, ∀ N : ℕ,
    (∑ n ∈ Ioc 0 N, (hooleyDelta n : ℝ) * log n) ≤
      C * N * ∑ n ∈ Ioc 0 N, (hooleyDelta n : ℝ) / n := by
  obtain ⟨C, hC, hbound⟩ := sum_divisorMangoldt_le
  refine ⟨C, hC, fun N ↦ ?_⟩
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, (deltaArithmetic * divisorMangoldt) n :=
      sum_le_sum (fun n _ ↦ delta_mul_log_le_convolution n)
    _ = ∑ n ∈ Ioc 0 N, (hooleyDelta n : ℝ) *
        ∑ m ∈ Ioc 0 (N / n), divisorMangoldt m :=
      ArithmeticFunction.sum_Ioc_mul_eq_sum_sum _ _ _
    _ ≤ ∑ n ∈ Ioc 0 N, (hooleyDelta n : ℝ) * (C * ((N : ℝ) / n)) := by
      apply sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have hn' := mem_Ioc.1 hn
      have hdiv : 1 ≤ N / n := (Nat.one_le_div_iff hn'.1).2 hn'.2
      have h := hbound ((N / n : ℕ) : ℝ) (by exact_mod_cast hdiv)
      rw [Nat.floor_natCast] at h
      exact h.trans (mul_le_mul_of_nonneg_left Nat.cast_div_le hC.le)
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro n _; ring

lemma hooleyDelta_le_self (n : ℕ) : hooleyDelta n ≤ n :=
  (hooleyDelta_le_card n).trans (Nat.card_divisors_le_self n)

/-- The integers below `sqrt x` contribute at most `x`; above it the logarithmic
weight is at least `(log x)/2`. -/
lemma delta_sum_le_log_sum {x : ℝ} (hx : 2 ≤ x) :
    meanSum x ≤ x + 2 / log x *
      ∑ n ∈ Ioc 0 ⌊x⌋₊, (hooleyDelta n : ℝ) * log n := by
  classical
  let S := (Ioc 0 ⌊x⌋₊).filter (fun n : ℕ ↦ (n : ℝ) ≤ sqrt x)
  let L := (Ioc 0 ⌊x⌋₊).filter (fun n : ℕ ↦ ¬(n : ℝ) ≤ sqrt x)
  have hx0 : 0 ≤ x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hs0 : 0 < sqrt x := sqrt_pos.2 (by linarith)
  have hsmall : (∑ n ∈ S, (hooleyDelta n : ℝ)) ≤ x := by
    have hsub : S ⊆ Ioc 0 ⌊sqrt x⌋₊ := by
      intro n hn
      obtain ⟨hn, hs⟩ := mem_filter.1 hn
      exact mem_Ioc.2 ⟨(mem_Ioc.1 hn).1, Nat.le_floor hs⟩
    have hc : (S.card : ℝ) ≤ sqrt x := by
      have h := card_le_card hsub
      simp only [Nat.card_Ioc, Nat.sub_zero] at h
      exact (Nat.cast_le.2 h).trans (Nat.floor_le hs0.le)
    calc
      _ ≤ ∑ _ ∈ S, sqrt x := by
        apply sum_le_sum
        intro n hn
        exact (Nat.cast_le.2 (hooleyDelta_le_self n)).trans (mem_filter.1 hn).2
      _ = S.card * sqrt x := by simp
      _ ≤ sqrt x * sqrt x := mul_le_mul_of_nonneg_right hc hs0.le
      _ = x := mul_self_sqrt hx0
  have hlarge : (∑ n ∈ L, (hooleyDelta n : ℝ)) ≤
      2 / log x * ∑ n ∈ Ioc 0 ⌊x⌋₊, (hooleyDelta n : ℝ) * log n := by
    calc
      _ ≤ ∑ n ∈ L, 2 / log x * ((hooleyDelta n : ℝ) * log n) := by
        apply sum_le_sum
        intro n hn
        have hn' := mem_filter.1 hn
        have hlog : log x / 2 ≤ log n := by
          rw [← log_sqrt hx0]
          exact log_le_log hs0 (le_of_lt (lt_of_not_ge hn'.2))
        have hfactor : 1 ≤ 2 / log x * log n := by
          rw [div_mul_eq_mul_div]
          apply (le_div_iff₀ hl).2
          linarith
        nlinarith [mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg (hooleyDelta n))]
      _ = 2 / log x * ∑ n ∈ L, (hooleyDelta n : ℝ) * log n := (mul_sum _ _ _).symm
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro n hn _
        exact mul_nonneg (Nat.cast_nonneg _) (log_nonneg (by exact_mod_cast (mem_Ioc.1 hn).1))
  have hsplit := sum_filter_add_sum_filter_not (Ioc 0 ⌊x⌋₊)
    (fun n : ℕ ↦ (n : ℝ) ≤ sqrt x) (fun n ↦ (hooleyDelta n : ℝ))
  have hinterval : Icc 1 ⌊x⌋₊ = Ioc 0 ⌊x⌋₊ := by ext n; simp; omega
  unfold meanSum
  rw [hinterval, ← hsplit]
  exact add_le_add hsmall hlarge

/-- Reduction of the ordinary mean to the harmonic sum over all integers. -/
theorem meanSum_le_harmonic : ∃ C > 0, ∀ x : ℝ, 2 ≤ x →
    meanSum x ≤ x + C * x / log x *
      ∑ n ∈ Ioc 0 ⌊x⌋₊, (hooleyDelta n : ℝ) / n := by
  obtain ⟨C, hC, h⟩ := delta_log_sum_le_harmonic
  refine ⟨2 * C, by positivity, fun x hx ↦ ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hs : 0 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, (hooleyDelta n : ℝ) / n :=
    sum_nonneg (fun _ _ ↦ by positivity)
  calc
    _ ≤ x + 2 / log x * ∑ n ∈ Ioc 0 ⌊x⌋₊, (hooleyDelta n : ℝ) * log n :=
      delta_sum_le_log_sum hx
    _ ≤ x + 2 / log x * (C * ⌊x⌋₊ * ∑ n ∈ Ioc 0 ⌊x⌋₊, (hooleyDelta n : ℝ) / n) := by
      gcongr
      exact h ⌊x⌋₊
    _ ≤ x + 2 / log x * (C * x * ∑ n ∈ Ioc 0 ⌊x⌋₊, (hooleyDelta n : ℝ) / n) := by
      gcongr
      exact Nat.floor_le hx0
    _ = _ := by ring

end BretecheTenenbaumMean
