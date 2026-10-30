module

public import BretecheTenenbaumMean.EventBounds

@[expose] public section

/-! # Finite tail decompositions for expectations -/

namespace BretecheTenenbaumMean

open Finset

theorem expectation_const (x c : ℝ) : expectation x (fun _ ↦ c) = c := by
  have h := expectation_const_mul x c (fun _ ↦ 1)
  simpa only [mul_one, expectation_one] using h

theorem expectation_finset_sum (x : ℝ) (s : Finset ℕ) (f : ℕ → ℕ → ℝ) :
    expectation x (fun n ↦ ∑ j ∈ s, f j n) = ∑ j ∈ s, expectation x (f j) := by
  unfold expectation
  rw [← sum_div]
  congr 1
  simp_rw [sum_div]
  exact sum_comm

theorem expectation_div_const (x c : ℝ) (f : ℕ → ℝ) :
    expectation x (fun n ↦ f n / c) = expectation x f / c := by
  simpa only [div_eq_mul_inv, mul_comm] using expectation_const_mul x c⁻¹ f

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

/-- A finite sum of probability tails controls the expectation, with a
second-moment remainder at the last threshold. -/
theorem expectation_le_finite_tails (x : ℝ) (f : ℕ → ℝ) (hf : ∀ n ∈ smoothSupport x, 0 ≤ f n)
    (R : ℕ → ℝ) (N : ℕ) (hR : ∀ j, 0 ≤ R j) (hRN : 0 < R N) :
    expectation x f ≤ R 0 + (∑ j ∈ range N, R (j + 1) * probability x {n | R j < f n}) +
      expectation x (fun n ↦ f n ^ 2) / R N := by
  classical
  have h := expectation_mono x (f := f)
    (g := fun n ↦ R 0 +
      (∑ j ∈ range N, R (j + 1) * ({m | R j < f m}).indicator (fun _ ↦ (1 : ℝ)) n) + f n ^ 2 / R N)
    (fun n hn ↦ by simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using
      le_finite_tail_majorant (hf n hn) R N hR hRN)
  rw [expectation_add, expectation_add, expectation_const, expectation_finset_sum, expectation_div_const] at h
  simp_rw [expectation_const_mul] at h
  exact h

end BretecheTenenbaumMean
