module

public import BretecheTenenbaumMean.PrimeSums.Product

@[expose] public section

/-! # Euler products with constant real weights -/

namespace BretecheTenenbaumMean.PrimeSums

open Finset Real

/-- The constant-weight product bound for nonnegative real weights. -/
theorem prod_one_add_real_div_le {a : ℝ} (ha : 0 ≤ a) : ∃ C > 0, ∀ x : ℝ, 2 ≤ x →
    (∏ p ∈ primesLT x, (1 + a / p)) ≤ C * (log x) ^ a := by
  obtain ⟨K, _, hK⟩ := abs_SLT_sub_loglog_le
  refine ⟨exp (a * K + a ^ 2), exp_pos _, fun x hx ↦ ?_⟩
  have hl : 0 < log x := log_pos (by linarith)
  have hp : 0 < ∏ p ∈ primesLT x, (1 + a / p) := prod_pos (fun _ _ ↦ by positivity)
  have h := (abs_le.1 (abs_log_prod_sub_sum_le (x := x) (A := a)
    (w := fun _ ↦ a) (fun _ _ ↦ ⟨ha, le_rfl⟩))).2
  have hs : (∑ p ∈ primesLT x, a / p) = a * SLT x := by
    simp only [SLT, div_eq_mul_inv, mul_sum]
  rw [hs] at h
  have hm := mul_le_mul_of_nonneg_left (abs_le.1 (hK x hx)).2 ha
  calc
    _ = exp (log (∏ p ∈ primesLT x, (1 + a / p))) := (exp_log hp).symm
    _ ≤ exp (a * K + a ^ 2 + a * log (log x)) := exp_le_exp.2 (by linarith)
    _ = _ := by rw [exp_add, rpow_def_of_pos hl, mul_comm a (log (log x))]

end BretecheTenenbaumMean.PrimeSums
