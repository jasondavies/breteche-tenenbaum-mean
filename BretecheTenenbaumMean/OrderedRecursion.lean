module

public import BretecheTenenbaumMean.LargestPrime

@[expose] public section

/-! # Iteration of a recurrence over an ordered finite set -/

namespace BretecheTenenbaumMean

open Finset

/-- A finite ordered Volterra inequality. Each error is multiplied by the
Euler product of the weights at larger indices. No infinite iteration or
limiting remainder is needed. -/
theorem sum_ordered_recursion_le {α : Type*} [LinearOrder α]
    (s : Finset α) (w A V : α → ℝ) (hw : ∀ p ∈ s, 0 ≤ w p)
    (hrec : ∀ p ∈ s, A p ≤ V p + ∑ q ∈ s.filter (fun q ↦ q < p), w q * A q) :
    (∑ p ∈ s, w p * A p) ≤
      ∑ p ∈ s, w p * V p * ∏ q ∈ s.filter (fun q ↦ p < q), (1 + w q) := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert p s hp ih =>
    have hps : p ∉ s := fun h ↦ (lt_irrefl p) (hp p h)
    have hleft : (insert p s).filter (fun q ↦ q < p) = s := by
      ext q
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | h, hlt⟩
        · exact (lt_irrefl _ hlt).elim
        · exact h
      · intro h
        exact ⟨Or.inr h, hp q h⟩
    have hleftq : ∀ q ∈ s,
        (insert p s).filter (fun r ↦ r < q) = s.filter (fun r ↦ r < q) := by
      intro q hq
      rw [filter_insert]
      simp only [not_lt.2 (hp q hq).le, ite_false]
    have hright : (insert p s).filter (fun q ↦ p < q) = ∅ := by
      apply filter_eq_empty_iff.2
      intro q hq
      rcases mem_insert.1 hq with rfl | hq
      · exact lt_irrefl _
      · exact not_lt.2 (hp q hq).le
    have hrightq : ∀ q ∈ s,
        (insert p s).filter (fun r ↦ q < r) = insert p (s.filter (fun r ↦ q < r)) := by
      intro q hq
      rw [filter_insert]
      simp only [hp q hq, ite_true]
    have hrecp := hrec p (mem_insert_self p s)
    rw [hleft] at hrecp
    have hsmall := ih (fun q hq ↦ hw q (mem_insert_of_mem hq)) (fun q hq ↦ by
      have h := hrec q (mem_insert_of_mem hq)
      rw [hleftq q hq] at h
      exact h)
    have hwp := hw p (mem_insert_self p s)
    have hprod : ∀ q ∈ s,
        (∏ r ∈ (insert p s).filter (fun r ↦ q < r), (1 + w r)) =
          (1 + w p) * ∏ r ∈ s.filter (fun r ↦ q < r), (1 + w r) := by
      intro q hq
      rw [hrightq q hq, prod_insert (notMem_mono (filter_subset _ _) hps)]
    rw [sum_insert hps, sum_insert hps, hright, prod_empty, mul_one]
    calc
      _ ≤ w p * (V p + ∑ q ∈ s, w q * A q) + ∑ q ∈ s, w q * A q :=
        add_le_add (mul_le_mul_of_nonneg_left hrecp hwp) le_rfl
      _ = w p * V p + (1 + w p) * ∑ q ∈ s, w q * A q := by ring
      _ ≤ w p * V p + (1 + w p) *
          ∑ q ∈ s, w q * V q * ∏ r ∈ s.filter (fun r ↦ q < r), (1 + w r) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hsmall (by linarith))
      _ = _ := by
        rw [mul_sum]
        congr 1
        apply sum_congr rfl
        intro q hq
        rw [hprod q hq]
        ring

end BretecheTenenbaumMean
