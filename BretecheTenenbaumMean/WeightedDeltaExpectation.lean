module

public import BretecheTenenbaumMean.DeltaExpectation
public import BretecheTenenbaumMean.WeightedDeltaProbabilityTail
public import BretecheTenenbaumMean.WeightedTailToMean

@[expose] public section

/-! # The sharp weighted mean under explicit prime estimates -/

namespace BretecheTenenbaumMean.WeightedModel

open Finset Real

/-- The full weighted finite-model mean, conditional only on bounded prime
weights and the uniform prime cosine estimate in `PrimeEstimates`. -/
theorem hooleyDelta_expectation_bound (w : MultiplicativeWeight) (hpw : PrimeEstimates w) : ∃ K > 0, ∀ x : ℝ, exp (exp 4) ≤ x →
    expectation w x (fun n ↦ (hooleyDelta n : ℝ)) ≤ K * log (log x) ^ (5 / 2 : ℝ) := by
  obtain ⟨A₀, hA₀, C, hC, htail⟩ := hooleyDelta_probability_tail_bound w hpw
  obtain ⟨B, hB, hsecond⟩ := hpw.expectation_tau_pow_bound 2
  let A := max A₀ 1
  have hA : 1 ≤ A := le_max_right _ _
  obtain ⟨K, hK, hmean⟩ := expectation_le_of_logarithmic_tail w hA hB hC
  refine ⟨K, hK, fun x hx ↦ ?_⟩
  obtain ⟨hx3, hq, hqle, _⟩ := moment_order_floor_bounds hx
  have hs : 1 ≤ log (log x) := by
    have hq' : (3 : ℝ) ≤ ⌊log (log x)⌋₊ := by exact_mod_cast hq
    linarith
  have hlx : 0 < log x := log_pos (by linarith)
  apply hmean x (log (log x)) hs (fun n ↦ (hooleyDelta n : ℝ)) (fun n _ ↦ Nat.cast_nonneg _)
  · intro T hT
    have hT0 : 0 < T := by linarith
    have hlT : 0 < log T := log_pos (by linarith)
    have hth : A₀ * T * sqrt (log T) * log (log x) ≤ A * T * sqrt (log T) * log (log x) := by
      gcongr
      exact le_max_left _ _
    calc
      _ ≤ probability w x {n | A₀ * T * sqrt (log T) * log (log x) < (hooleyDelta n : ℝ)} := by
        apply probability_mono w
        intro n hn
        exact hth.trans_lt hn
      _ ≤ _ := htail x T hx hT
  · have hb := hsecond x (by linarith : 2 ≤ x)
    norm_num only [Nat.reducePow, Nat.reduceSub] at hb
    have he : exp (3 * log (log x)) = log x ^ 3 := by
      calc
        _ = (exp (log (log x))) ^ 3 := by simpa only [Nat.cast_ofNat] using exp_nat_mul (log (log x)) 3
        _ = _ := by rw [exp_log hlx]
    rw [he]
    refine (expectation_mono w x (fun n _ ↦ ?_)).trans hb
    have hn : (hooleyDelta n : ℝ) ≤ tau n := by
      unfold tau
      exact_mod_cast hooleyDelta_le_card n
    simpa only [pow_two] using mul_self_le_mul_self (Nat.cast_nonneg (α := ℝ) (hooleyDelta n)) hn


end BretecheTenenbaumMean.WeightedModel
