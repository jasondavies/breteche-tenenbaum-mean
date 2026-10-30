module

public import BretecheTenenbaumMean.EventBounds

@[expose] public section

/-! # Finite tail decompositions for expectations -/

namespace BretecheTenenbaumMean

open Finset

/-- A finite layer decomposition, with a quadratic remainder beyond the
last threshold. Monotonicity of the thresholds is not needed. -/
theorem le_finite_tail_majorant {t : ℝ} (ht : 0 ≤ t) (R : ℕ → ℝ) (N : ℕ)
    (hR : ∀ j, 0 ≤ R j) (hRN : 0 < R N) :
    t ≤ R 0 + (∑ j ∈ range N, R (j + 1) * if R j < t then 1 else 0) + t ^ 2 / R N := by
  classical
  have hsum : 0 ≤ ∑ j ∈ range N, R (j + 1) * if R j < t then 1 else 0 := by
    apply sum_nonneg
    intro j _
    split_ifs <;> simp only [mul_one, mul_zero, hR, le_refl]
  have hquad : 0 ≤ t ^ 2 / R N := div_nonneg (sq_nonneg _) hRN.le
  by_cases h0 : t ≤ R 0
  · linarith [hR 0]
  by_cases hN : t ≤ R N
  · have hex : ∃ k : ℕ, t ≤ R k := ⟨N, hN⟩
    let k := Nat.find hex
    have hk : t ≤ R k := Nat.find_spec hex
    have hkN : k ≤ N := Nat.find_min' hex hN
    have hkpos : 0 < k := by
      by_contra h
      have he : k = 0 := by omega
      rw [he] at hk
      exact h0 hk
    have hprev : R (k - 1) < t := lt_of_not_ge (Nat.find_min hex (show k - 1 < k by omega))
    have hterm : R k ≤ ∑ j ∈ range N, R (j + 1) * if R j < t then 1 else 0 := by
      have h := single_le_sum (s := range N)
        (f := fun j ↦ R (j + 1) * if R j < t then 1 else 0)
        (fun j _ ↦ mul_nonneg (hR _) (by split_ifs <;> norm_num))
        (show k - 1 ∈ range N by rw [mem_range]; omega)
      simpa only [hprev, ite_true, mul_one, Nat.sub_add_cancel (by omega : 1 ≤ k)] using h
    linarith [hR 0]
  · have hq : t ≤ t ^ 2 / R N := by
      apply (le_div_iff₀ hRN).2
      nlinarith
    linarith [hR 0]

end BretecheTenenbaumMean
