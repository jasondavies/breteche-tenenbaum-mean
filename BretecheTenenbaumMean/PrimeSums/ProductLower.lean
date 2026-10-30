module

public import BretecheTenenbaumMean.PrimeSums.Product

@[expose] public section

/-! # Lower bounds for constant-weight Euler products -/

namespace BretecheTenenbaumMean.PrimeSums

open Finset Real

/-- The lower half of the constant-weight Mertens product estimate. -/
theorem prod_one_add_nat_div_lower (a : ℕ) : ∃ c > 0, ∀ x : ℝ, 2 ≤ x →
    c * log x ^ a ≤ ∏ p ∈ primesLT x, (1 + (a : ℝ) / p) := by
  obtain ⟨K, _, hK⟩ := abs_SLT_sub_loglog_le
  refine ⟨exp (-((a : ℝ) * K + (a : ℝ) ^ 2)), exp_pos _, fun x hx ↦ ?_⟩
  have hl : 0 < log x := log_pos (by linarith)
  have hp : 0 < ∏ p ∈ primesLT x, (1 + (a : ℝ) / p) := prod_pos (fun _ _ ↦ by positivity)
  have h := (abs_le.1 (abs_log_prod_sub_sum_le (x := x) (A := a)
    (w := fun _ ↦ a) (fun _ _ ↦ ⟨Nat.cast_nonneg a, le_rfl⟩))).1
  have hs : (∑ p ∈ primesLT x, (a : ℝ) / p) = (a : ℝ) * SLT x := by
    simp only [SLT, div_eq_mul_inv, mul_sum]
  rw [hs] at h
  have hm := mul_le_mul_of_nonneg_left (abs_le.1 (hK x hx)).1 (Nat.cast_nonneg (α := ℝ) a)
  calc
    _ = exp (-((a : ℝ) * K + (a : ℝ) ^ 2) + (a : ℝ) * log (log x)) := by
      rw [exp_add, exp_nat_mul, exp_log hl]
    _ ≤ exp (log (∏ p ∈ primesLT x, (1 + (a : ℝ) / p))) := exp_le_exp.2 (by linarith)
    _ = _ := exp_log hp

end BretecheTenenbaumMean.PrimeSums
