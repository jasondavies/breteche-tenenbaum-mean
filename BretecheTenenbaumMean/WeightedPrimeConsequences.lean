module

public import BretecheTenenbaumMean.WeightedPrimeEstimates
public import BretecheTenenbaumMean.WeightedGoodSetExceptional

@[expose] public section

/-! # Normalization and good-set bounds from the weighted prime estimates -/

namespace BretecheTenenbaumMean.WeightedModel

open Real Finset

/-- The weighted normalizer has order `log x` under the explicit prime estimates. -/
theorem PrimeEstimates.normalizer_bounds {w : MultiplicativeWeight} (h : PrimeEstimates w) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ≥ 2,
      c * log x ≤ normalizer w x ∧ normalizer w x ≤ C * log x := by
  refine ⟨exp (-(h.primeBound ^ 2 + h.errorBound)), exp (h.primeBound ^ 2 + h.errorBound),
    exp_pos _, exp_pos _, fun x hx ↦ ?_⟩
  exact normalizer_bounds_of_prime_sum w hx
    (fun p hp ↦ h.prime_le p (mem_primesLT.1 hp).1) (h.prime_sum_error hx)

/-- Every fixed divisor-count moment has the same logarithmic exponent as
in the unit-weight model. -/
theorem PrimeEstimates.expectation_tau_pow_bound {w : MultiplicativeWeight}
    (h : PrimeEstimates w) (k : ℕ) : ∃ C > 0, ∀ x ≥ 2,
      expectation w x (fun n ↦ tau n ^ k) ≤ C * log x ^ (2 ^ k - 1) := by
  let j : ℕ := 2 ^ k - 1
  have hj : (j : ℝ) = (2 : ℝ) ^ k - 1 := by
    dsimp [j]
    rw [Nat.cast_sub (Nat.one_le_pow k 2 (by norm_num)), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  refine ⟨exp (h.primeBound ^ 2 + (j : ℝ) * h.errorBound), exp_pos _, fun x hx ↦ ?_⟩
  have he := expectation_multiplicative_le_exp w x (fun n ↦ tau n ^ k)
    (by simp) (fun m n hmn ↦ by rw [tau_mul_of_coprime hmn, mul_pow])
    (fun p _ ↦ pow_nonneg (show 0 ≤ tau p from Nat.cast_nonneg _) _)
    (fun p hp ↦ h.prime_le p (mem_primesLT.1 hp).1)
  have hs : (∑ p ∈ primesLT x, w p * (tau p ^ k - 1) / p) = (j : ℝ) * primeSum w x := by
    rw [primeSum, mul_sum]
    apply sum_congr rfl
    intro p hp
    rw [tau_prime (mem_primesLT.1 hp).1, hj]
    ring
  rw [hs] at he
  have hm := mul_le_mul_of_nonneg_left (abs_le.1 (h.prime_sum_error hx)).2
    (Nat.cast_nonneg (α := ℝ) j)
  have hl : 0 < log x := log_pos (by linarith)
  calc
    _ ≤ exp (h.primeBound ^ 2 + (j : ℝ) * primeSum w x) := he
    _ ≤ exp ((h.primeBound ^ 2 + (j : ℝ) * h.errorBound) + (j : ℝ) * log (log x)) :=
      exp_le_exp.2 (by nlinarith)
    _ = _ := by rw [exp_add, exp_nat_mul, exp_log hl]

/-- The weighted analogue of (2.1), now under the single explicit prime-estimate interface. -/
theorem PrimeEstimates.goodSet_exceptional_bound {w : MultiplicativeWeight}
    (h : PrimeEstimates w) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 1000000) :
    ∃ C > 0, ∀ x T : ℝ, 1 < T → probability w x (goodSet δ T)ᶜ ≤ C / T :=
  goodSet_exceptional_probability_bound w h.prime_le h.errorBound_nonneg
    (fun _ hx ↦ h.prime_sum_error hx) hδ hδ1

end BretecheTenenbaumMean.WeightedModel
