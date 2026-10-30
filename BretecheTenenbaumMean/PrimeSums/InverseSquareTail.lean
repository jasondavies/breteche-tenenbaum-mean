module

public import BretecheTenenbaumMean.PrimeSums.Product

@[expose] public section

/-! # Uniform reciprocal-square tails over a finite set of primes -/

namespace BretecheTenenbaumMean.PrimeSums

open Finset Real

/-- A telescoping comparison, valid for any finite set beyond an integer cutoff. -/
theorem sum_inv_sq_tail_le {s : Finset ℕ} {P : ℕ} (hP : 2 ≤ P)
    (hs : ∀ n ∈ s, P ≤ n) : (∑ n ∈ s, ((n : ℝ)⁻¹) ^ 2) ≤ ((P : ℝ) - 1)⁻¹ := by
  let M := max P (s.sup id + 1)
  have hPM : P ≤ M := le_max_left _ _
  have hsub : s ⊆ Ico P M := by
    intro n hn
    exact mem_Ico.2 ⟨hs n hn, (Nat.lt_succ_of_le (le_sup (f := id) hn)).trans_le (le_max_right _ _)⟩
  have hlocal (n : ℕ) (hn : n ∈ Ico P M) :
      ((n : ℝ)⁻¹) ^ 2 ≤ ((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹ := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hP.trans (mem_Ico.1 hn).1
    have hn0 : 0 < (n : ℝ) := by linarith
    have hn1 : 0 < (n : ℝ) - 1 := by linarith
    have he : ((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹ = ((n : ℝ) - 1)⁻¹ * (n : ℝ)⁻¹ := by
      field_simp
      ring
    rw [he, pow_two]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hn1 (by linarith)) (by positivity)
  calc
    _ ≤ ∑ n ∈ Ico P M, ((n : ℝ)⁻¹) ^ 2 := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
    _ ≤ ∑ n ∈ Ico P M, (((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹) := sum_le_sum hlocal
    _ = ((P : ℝ) - 1)⁻¹ - ((M : ℝ) - 1)⁻¹ := sum_Ico_inv_sub_inv hPM
    _ ≤ _ := by
      have hM : (2 : ℝ) ≤ M := by exact_mod_cast hP.trans hPM
      have h0 : 0 ≤ ((M : ℝ) - 1)⁻¹ := inv_nonneg.2 (by linarith)
      linarith

end BretecheTenenbaumMean.PrimeSums
