module

public import BretecheTenenbaumMean.DyadicTailScale
public import BretecheTenenbaumMean.WeightedFiniteTailExpectation

@[expose] public section

/-! # Summing the weighted logarithmic probability tail -/

namespace BretecheTenenbaumMean.WeightedModel

open Finset Real

theorem expectation_le_of_logarithmic_tail (w : MultiplicativeWeight) {A B C : ℝ}
    (hA : 1 ≤ A) (hB : 0 < B) (hC : 0 < C) :
    ∃ K > 0, ∀ x s : ℝ, 1 ≤ s → ∀ f : ℕ → ℝ,
    (∀ n ∈ smoothSupport x, 0 ≤ f n) →
    (∀ T : ℝ, 3 ≤ T → probability w x {n | A * T * sqrt (log T) * s < f n} ≤ C / T) →
    expectation w x (fun n ↦ f n ^ 2) ≤ B * exp (3 * s) →
    expectation w x f ≤ K * s ^ (5 / 2 : ℝ) := by
  have hA0 : 0 < A := by linarith
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  let D : ℝ := 3 / log 2 + 3
  have hD : 0 < D := by dsimp only [D]; positivity
  let K : ℝ := 4 * A * sqrt (log 4) + 2 * A * C * D * sqrt (D * log 2) + B
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, fun x s hs f hf htail hsecond ↦ ?_⟩
  have hs0 : 0 < s := by linarith
  have hroot : 1 ≤ sqrt s := by simpa only [sqrt_one] using sqrt_le_sqrt hs
  let N := ⌈3 * s / log 2⌉₊
  let R := dyadicTailThreshold A s
  have hR : ∀ j, 0 < R j := fun j ↦ dyadicTailThreshold_pos hA hs j
  obtain ⟨hN, hN2, hlevel⟩ := dyadic_tail_cutoff_bounds hs
  change (N : ℝ) ≤ D * s at hN
  change (N : ℝ) + 2 ≤ D * s at hN2
  have hlast : exp (3 * s) ≤ R N := hlevel.trans (dyadicTailThreshold_ge_level hA hs N)
  have hbase : s ≤ s ^ 2 * sqrt s := by
    have h := mul_le_mul_of_nonneg_left hroot (sq_nonneg s)
    nlinarith
  have hbase1 : 1 ≤ s ^ 2 * sqrt s := hs.trans hbase
  have hterm : ∀ j ∈ range N,
      R (j + 1) * probability w x {n | R j < f n} ≤
        2 * A * C * s * (sqrt (D * log 2) * sqrt s) := by
    intro j hj
    have ht := htail (dyadicTailLevel j) (by linarith [dyadicTailLevel_ge_four j])
    have hjN : (j : ℝ) + 3 ≤ (N : ℝ) + 2 := by exact_mod_cast (show j + 3 ≤ N + 2 by have := mem_range.1 hj; omega)
    have hinner : ((j : ℝ) + 3) * log 2 ≤ (D * log 2) * s := by
      have h := mul_le_mul_of_nonneg_right (hjN.trans hN2) hl2.le
      nlinarith
    have hsq := sqrt_le_sqrt hinner
    rw [sqrt_mul (mul_pos hD hl2).le] at hsq
    calc
      _ ≤ R (j + 1) * (C / dyadicTailLevel j) := mul_le_mul_of_nonneg_left ht (hR _).le
      _ = C * (dyadicTailThreshold A s (j + 1) / dyadicTailLevel j) := by dsimp only [R]; ring
      _ = 2 * A * C * s * sqrt (((j : ℝ) + 3) * log 2) := by
        rw [dyadicTailThreshold_next_div]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq (by positivity)
  have hsum : (∑ j ∈ range N, R (j + 1) * probability w x {n | R j < f n}) ≤
      (2 * A * C * D * sqrt (D * log 2)) * (s ^ 2 * sqrt s) := by
    calc
      _ ≤ ∑ _ ∈ range N, 2 * A * C * s * (sqrt (D * log 2) * sqrt s) := sum_le_sum hterm
      _ = (N : ℝ) * (2 * A * C * s * (sqrt (D * log 2) * sqrt s)) := by simp only [sum_const, card_range, nsmul_eq_mul]
      _ ≤ (D * s) * (2 * A * C * s * (sqrt (D * log 2) * sqrt s)) :=
        mul_le_mul_of_nonneg_right hN (by positivity)
      _ = _ := by ring
  have hstart : R 0 ≤ (4 * A * sqrt (log 4)) * (s ^ 2 * sqrt s) := by
    rw [show R 0 = 4 * A * sqrt (log 4) * s from dyadicTailThreshold_zero A s]
    exact mul_le_mul_of_nonneg_left hbase (by positivity)
  have hrem : expectation w x (fun n ↦ f n ^ 2) / R N ≤ B := by
    apply (div_le_iff₀ (hR N)).2
    have h := mul_le_mul_of_nonneg_left hlast hB.le
    exact hsecond.trans h
  have h := expectation_le_finite_tails w x f hf R N (fun j ↦ (hR j).le) (hR N)
  have hmean : expectation w x f ≤ K * (s ^ 2 * sqrt s) := by
    have hb := mul_le_mul_of_nonneg_left hbase1 hB.le
    dsimp only [K]
    nlinarith
  have he : s ^ 2 * sqrt s = s ^ (5 / 2 : ℝ) := by
    rw [sqrt_eq_rpow, ← rpow_natCast s 2, ← rpow_add hs0]
    norm_num
  rwa [he] at hmean


end BretecheTenenbaumMean.WeightedModel
