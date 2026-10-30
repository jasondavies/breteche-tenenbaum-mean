module

public import BretecheTenenbaumMean.PrimeSums.RealProduct
public import BretecheTenenbaumMean.SmoothSums

@[expose] public section

/-! # Square-root divisor-count averages -/

namespace BretecheTenenbaumMean

open Finset Real

/-- Exact Euler product for the unnormalized square-root divisor count. -/
theorem sum_sqrt_tau_div_eq_prod (x : ℝ) :
    (∑ n ∈ smoothSupport x, sqrt (tau n) / n) =
      ∏ p ∈ primesLT x, (1 + sqrt 2 / p) := by
  have he := expectation_multiplicative x (fun n ↦ sqrt (tau n)) (by simp)
    (fun m n hmn ↦ by rw [tau_mul_of_coprime hmn, sqrt_mul (show 0 ≤ tau m from Nat.cast_nonneg _)])
  have hp : (∏ p ∈ primesLT x, (1 + sqrt (tau p) / p)) =
      ∏ p ∈ primesLT x, (1 + sqrt 2 / p) := by
    apply prod_congr rfl
    intro p hp
    rw [tau_prime (mem_primesLT.1 hp).1]
  unfold expectation at he
  rw [hp] at he
  exact (div_left_inj' (normalizer_pos x).ne').1 he

/-- Uniform down to `y = 1`, as needed for the smoothed moment recursion. -/
theorem sum_sqrt_tau_div_bound : ∃ C > 0, ∀ y : ℝ, 1 ≤ y →
    (∑ n ∈ smoothSupport y, sqrt (tau n) / n) ≤ C * log (3 * y) ^ (sqrt 2) := by
  obtain ⟨C, hC, hprod⟩ := PrimeSums.prod_one_add_real_div_le (sqrt_nonneg 2)
  refine ⟨C, hC, fun y hy ↦ ?_⟩
  calc
    _ ≤ ∑ n ∈ smoothSupport (3 * y), sqrt (tau n) / n :=
      sum_smoothSupport_mono (fun n ↦ by positivity) (by linarith)
    _ = _ := sum_sqrt_tau_div_eq_prod _
    _ ≤ _ := hprod _ (by linarith)

end BretecheTenenbaumMean
