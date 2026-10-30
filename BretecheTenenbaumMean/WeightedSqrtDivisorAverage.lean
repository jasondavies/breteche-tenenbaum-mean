module

public import BretecheTenenbaumMean.WeightedPrimeConsequences
public import BretecheTenenbaumMean.SmoothSums

@[expose] public section

/-! # Weighted square-root divisor-count averages -/

namespace BretecheTenenbaumMean.WeightedModel

open Finset Real

/-- Exact Euler product with the arithmetic weight retained. -/
theorem sum_sqrt_tau_div_eq_prod (w : MultiplicativeWeight) (x : ℝ) :
    (∑ n ∈ smoothSupport x, w n * sqrt (tau n) / n) =
      ∏ p ∈ primesLT x, (1 + w p * sqrt 2 / p) := by
  have he := expectation_multiplicative w x (fun n ↦ sqrt (tau n)) (by simp)
    (fun m n hmn ↦ by rw [tau_mul_of_coprime hmn, sqrt_mul (show 0 ≤ tau m from Nat.cast_nonneg _)])
  have hp : (∏ p ∈ primesLT x, (1 + w p * sqrt (tau p) / p)) =
      ∏ p ∈ primesLT x, (1 + w p * sqrt 2 / p) := by
    apply prod_congr rfl
    intro p hp
    rw [tau_prime (mem_primesLT.1 hp).1]
  unfold expectation at he
  rw [hp] at he
  exact (div_left_inj' (normalizer_pos w x).ne').1 he

/-- The exponent stays `sqrt 2` under the weighted Mertens hypothesis. -/
theorem sum_sqrt_tau_div_bound (w : MultiplicativeWeight) (hp : PrimeEstimates w) :
    ∃ C > 0, ∀ y : ℝ, 1 ≤ y →
    (∑ n ∈ smoothSupport y, w n * sqrt (tau n) / n) ≤ C * log (3 * y) ^ sqrt 2 := by
  refine ⟨exp (sqrt 2 * hp.errorBound), exp_pos _, fun y hy ↦ ?_⟩
  have hx : 2 ≤ 3 * y := by linarith
  have hl : 0 < log (3 * y) := log_pos (by linarith)
  calc
    _ ≤ ∑ n ∈ smoothSupport (3 * y), w n * sqrt (tau n) / n :=
      sum_smoothSupport_mono (fun n ↦ div_nonneg
        (mul_nonneg (w.nonneg n) (sqrt_nonneg _)) (Nat.cast_nonneg _)) (by linarith)
    _ = ∏ p ∈ primesLT (3 * y), (1 + w p * sqrt 2 / p) := sum_sqrt_tau_div_eq_prod w _
    _ ≤ exp (∑ p ∈ primesLT (3 * y), w p * sqrt 2 / p) :=
      prod_one_add_le_exp_sum _ (fun p ↦ div_nonneg
        (mul_nonneg (w.nonneg p) (sqrt_nonneg _)) (Nat.cast_nonneg _))
    _ = exp (sqrt 2 * primeSum w (3 * y)) := by
      congr 1
      rw [primeSum, mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ exp (sqrt 2 * (log (log (3 * y)) + hp.errorBound)) :=
      exp_le_exp.2 (mul_le_mul_of_nonneg_left
        (by linarith [(abs_le.1 (hp.prime_sum_error hx)).2]) (sqrt_nonneg _))
    _ = _ := by
      rw [mul_add, exp_add, rpow_def_of_pos hl, mul_comm (log (log (3 * y))) (sqrt 2)]
      ring

end BretecheTenenbaumMean.WeightedModel
