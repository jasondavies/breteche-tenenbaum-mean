module

public import BretecheTenenbaumMean.TailToMean

@[expose] public section

/-! # The mean of the maximum in the finite squarefree model -/

namespace BretecheTenenbaumMean

open Real

/-- The final finite-model estimate in §2.4. Transferring it to the ordinary
mean over integers is a separate arithmetic step. -/
theorem hooleyDelta_expectation_bound : ∃ K > 0, ∀ x : ℝ, exp (exp 4) ≤ x →
    expectation x (fun n ↦ (hooleyDelta n : ℝ)) ≤ K * log (log x) ^ (5 / 2 : ℝ) := by
  obtain ⟨A₀, hA₀, C, hC, htail⟩ := hooleyDelta_probability_tail_bound
  obtain ⟨B, hB, hsecond⟩ := PrimeSums.expectation_tau_pow_le 2
  let A := max A₀ 1
  have hA : 1 ≤ A := le_max_right _ _
  obtain ⟨K, hK, hmean⟩ := expectation_le_of_logarithmic_tail hA hB hC
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
      _ ≤ probability x {n | A₀ * T * sqrt (log T) * log (log x) < (hooleyDelta n : ℝ)} := by
        apply probability_mono
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
    refine (expectation_mono x (fun n _ ↦ ?_)).trans hb
    have hn : (hooleyDelta n : ℝ) ≤ tau n := by
      unfold tau
      exact_mod_cast hooleyDelta_le_card n
    simpa only [pow_two] using mul_self_le_mul_self (Nat.cast_nonneg (α := ℝ) (hooleyDelta n)) hn

end BretecheTenenbaumMean
