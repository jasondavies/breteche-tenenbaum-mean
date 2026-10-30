module

public import BretecheTenenbaumMean.PrimeSums.InverseSquareTail

@[expose] public section

/-! # Mertens estimates after removing a fixed initial segment of primes -/

namespace BretecheTenenbaumMean.PrimeSums

open Finset Real

noncomputable def trimmedPrimes (P : ℕ) (y : ℝ) : Finset ℕ := (primesLT y).filter (P ≤ ·)

lemma trimmedPrimes_subset (P : ℕ) (y : ℝ) : trimmedPrimes P y ⊆ primesLT y := filter_subset _ _

lemma removed_prime_sum_le (P : ℕ) (y : ℝ) :
    (∑ p ∈ primesLT y with ¬P ≤ p, (p : ℝ)⁻¹) ≤ P := by
  have hsub : (primesLT y).filter (fun p ↦ ¬P ≤ p) ⊆ range P := by
    intro p hp
    exact mem_range.2 (lt_of_not_ge (mem_filter.1 hp).2)
  calc
    _ ≤ ∑ _ ∈ (primesLT y).filter (fun p ↦ ¬P ≤ p), (1 : ℝ) := by
      apply sum_le_sum
      intro p hp
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (mem_primesLT.1 (mem_filter.1 hp).1).1.one_le
      exact inv_le_one_of_one_le₀ hp1
    _ ≤ ∑ _ ∈ range P, (1 : ℝ) := sum_le_sum_of_subset_of_nonneg hsub (by intros; norm_num)
    _ = _ := by simp

lemma trimmed_prime_sum_sub_loglog_bound : ∃ K ≥ 0, ∀ P : ℕ, ∀ y : ℝ, 2 ≤ y →
    |(∑ p ∈ trimmedPrimes P y, (p : ℝ)⁻¹) - log (log y)| ≤ K + P := by
  obtain ⟨K, hK, h⟩ := abs_SLT_sub_loglog_le
  refine ⟨K, hK, fun P y hy ↦ ?_⟩
  have hs := sum_filter_add_sum_filter_not (primesLT y) (P ≤ ·) (fun p ↦ (p : ℝ)⁻¹)
  have hsmall := removed_prime_sum_le P y
  have hsmall0 : 0 ≤ ∑ p ∈ primesLT y with ¬P ≤ p, (p : ℝ)⁻¹ := sum_nonneg (fun _ _ ↦ by positivity)
  have hm := abs_le.1 (h y hy)
  rw [abs_le]
  change - (K + P) ≤ _ ∧ _ ≤ K + P
  dsimp [trimmedPrimes, SLT] at *
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) P]

lemma trimmed_prime_inv_sq_le {P : ℕ} (hP : 2 ≤ P) (y : ℝ) :
    (∑ p ∈ trimmedPrimes P y, ((p : ℝ)⁻¹) ^ 2) ≤ ((P : ℝ) - 1)⁻¹ :=
  sum_inv_sq_tail_le hP (fun _ hp ↦ (mem_filter.1 hp).2)

end BretecheTenenbaumMean.PrimeSums
