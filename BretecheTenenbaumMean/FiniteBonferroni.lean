module

public import BretecheTenenbaumMean.EventBounds

@[expose] public section

/-! # The second-order inclusion-exclusion bound for finite event families -/

namespace BretecheTenenbaumMean

open Finset

/-- Exact two-event inclusion-exclusion in the finite model. -/
theorem probability_union_add_inter (x : ℝ) (E F : Set ℕ) :
    probability x (E ∪ F) + probability x (E ∩ F) =
      probability x E + probability x F := by
  classical
  unfold probability
  rw [← expectation_add, ← expectation_add]
  congr 1
  funext n
  by_cases he : n ∈ E <;> by_cases hf : n ∈ F <;> simp [Set.indicator, he, hf]

/-- Inserting one index adds exactly one term for every pair containing it. -/
theorem sum_ordered_pairs_insert (s : Finset ℕ) {a : ℕ} (ha : a ∉ s)
    (f : ℕ → ℕ → ℝ) (hf : ∀ i j, f i j = f j i) :
    (∑ i ∈ insert a s, ∑ j ∈ (insert a s).filter (fun j ↦ i < j), f i j) =
      (∑ i ∈ s, ∑ j ∈ s.filter (fun j ↦ i < j), f i j) + ∑ j ∈ s, f a j := by
  simp only [sum_filter, sum_insert ha, lt_irrefl, ite_false, zero_add, sum_add_distrib]
  have hsplit : (∑ j ∈ s, if a < j then f a j else 0) +
      (∑ j ∈ s, if j < a then f j a else 0) = ∑ j ∈ s, f a j := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    have hja : j ≠ a := fun he ↦ ha (he ▸ hj)
    rcases lt_or_gt_of_ne hja with hjlt | hjgt
    · simp [hjlt, not_lt_of_ge hjlt.le, hf j a]
    · simp [hjgt, not_lt_of_ge hjgt.le]
  linarith

/-- The Bonferroni lower bound, with each unordered pair counted exactly once. -/
theorem probability_exists_mem_ge_pairs (x : ℝ) (s : Finset ℕ) (E : ℕ → Set ℕ) :
    (∑ i ∈ s, probability x (E i)) -
      (∑ i ∈ s, ∑ j ∈ s.filter (fun j ↦ i < j), probability x (E i ∩ E j)) ≤
        probability x {n | ∃ i ∈ s, n ∈ E i} := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [probability, expectation, Set.indicator]
  | @insert a s ha ih =>
      let U : Set ℕ := {n | ∃ i ∈ s, n ∈ E i}
      have he : {n | ∃ i ∈ insert a s, n ∈ E i} = E a ∪ U := by
        ext n
        simp [U]
      have hinter : E a ∩ U = {n | ∃ i ∈ s, n ∈ E a ∩ E i} := by
        ext n
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, U]
        constructor
        · rintro ⟨hna, i, hi, hni⟩
          exact ⟨i, hi, hna, hni⟩
        · rintro ⟨i, hi, hna, hni⟩
          exact ⟨hna, i, hi, hni⟩
      have hbad : probability x (E a ∩ U) ≤ ∑ i ∈ s, probability x (E a ∩ E i) := by
        rw [hinter]
        exact probability_exists_mem_le_sum x s (fun i ↦ E a ∩ E i)
      have hunion := probability_union_add_inter x (E a) U
      rw [he, sum_insert ha, sum_ordered_pairs_insert s ha _
        (fun i j ↦ by rw [Set.inter_comm])]
      change _ ≤ probability x U at ih
      linarith

end BretecheTenenbaumMean
