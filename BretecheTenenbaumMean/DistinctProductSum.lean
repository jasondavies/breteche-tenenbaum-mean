module

public import BretecheTenenbaumMean.PoissonBound
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.Order.Ring.Pow

@[expose] public section

/-! # Weighted subsets of fixed size

These sums encode products of distinct primes with prescribed prime-factor count.
-/

namespace BretecheTenenbaumMean

open Finset Real

noncomputable def distinctProductSum {α : Type*} (s : Finset α) (w : α → ℝ) (r : ℕ) : ℝ :=
  ∑ t ∈ s.powersetCard r, ∏ a ∈ t, w a

theorem distinctProductSum_insert {α : Type*} [DecidableEq α] (s : Finset α) (w : α → ℝ)
    {a : α} (ha : a ∉ s) (r : ℕ) :
    distinctProductSum (insert a s) w (r + 1) =
      distinctProductSum s w (r + 1) + w a * distinctProductSum s w r := by
  have hnot : ∀ t ∈ s.powersetCard r, a ∉ t := fun t ht hat ↦
    ha ((mem_powersetCard.1 ht).1 hat)
  have hd : Disjoint (s.powersetCard (r + 1)) ((s.powersetCard r).image (insert a)) := by
    apply disjoint_left.2
    intro t ht hi
    obtain ⟨u, hu, rfl⟩ := mem_image.1 hi
    exact ha ((mem_powersetCard.1 ht).1 (mem_insert_self _ _))
  rw [distinctProductSum, powersetCard_succ_insert ha, sum_union hd, sum_image]
  · congr 1
    change (∑ t ∈ s.powersetCard r, ∏ b ∈ insert a t, w b) =
      w a * ∑ t ∈ s.powersetCard r, ∏ b ∈ t, w b
    rw [mul_sum]
    exact sum_congr rfl (fun t ht ↦ prod_insert (hnot t ht))
  · intro t ht u hu he
    have h := congrArg (fun v : Finset α ↦ v.erase a) he
    simpa only [erase_insert (hnot t ht), erase_insert (hnot u hu)] using h

/-- The elementary-symmetric sum is at most the corresponding exponential-series term. -/
theorem distinctProductSum_le {α : Type*} (s : Finset α) (w : α → ℝ) (r : ℕ)
    (hw : ∀ a ∈ s, 0 ≤ w a) :
    distinctProductSum s w r ≤ (∑ a ∈ s, w a) ^ r / (r.factorial : ℝ) := by
  classical
  induction s using Finset.induction_on generalizing r with
  | empty =>
      cases r with
      | zero => simp [distinctProductSum]
      | succ r =>
          have he : (∅ : Finset α).powersetCard (r + 1) = ∅ := powersetCard_eq_empty.2 (by simp)
          simp [distinctProductSum, he]
  | @insert a s ha ih =>
      have hwa : 0 ≤ w a := hw a (mem_insert_self _ _)
      have hws : ∀ b ∈ s, 0 ≤ w b := fun b hb ↦ hw b (mem_insert_of_mem hb)
      have hS : 0 ≤ ∑ b ∈ s, w b := sum_nonneg hws
      cases r with
      | zero => simp [distinctProductSum]
      | succ r =>
          rw [distinctProductSum_insert s w ha r, sum_insert ha]
          have hf : 0 < (r.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos r
          have hrf : 0 < ((r + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (r + 1)
          have hr1 : 0 < (r : ℝ) + 1 := by positivity
          calc distinctProductSum s w (r + 1) + w a * distinctProductSum s w r
              ≤ (∑ b ∈ s, w b) ^ (r + 1) / ((r + 1).factorial : ℝ) +
                w a * ((∑ b ∈ s, w b) ^ r / (r.factorial : ℝ)) :=
                  add_le_add (ih _ hws) (mul_le_mul_of_nonneg_left (ih _ hws) hwa)
            _ = ((∑ b ∈ s, w b) ^ (r + 1) + (r + 1 : ℕ) * (∑ b ∈ s, w b) ^ r * w a) /
                ((r + 1).factorial : ℝ) := by
                  rw [Nat.factorial_succ]
                  push_cast
                  field_simp
            _ ≤ (w a + ∑ b ∈ s, w b) ^ (r + 1) / ((r + 1).factorial : ℝ) := by
                  apply div_le_div_of_nonneg_right _ hrf.le
                  have h := pow_add_mul_le_add_pow hS (show 0 ≤ 2 * (∑ b ∈ s, w b) + w a by positivity) (r + 1)
                  simpa only [Nat.add_sub_cancel, add_comm (∑ b ∈ s, w b) (w a)] using h

/-- The uniform factorial estimate gives the square-root saving used in §2.2. -/
theorem distinctProductSum_uniform {α : Type*} (s : Finset α) (w : α → ℝ) (r : ℕ)
    (hw : ∀ a ∈ s, 0 ≤ w a) :
    distinctProductSum s w r ≤ 8 * exp (∑ a ∈ s, w a) / sqrt (1 + ∑ a ∈ s, w a) :=
  (distinctProductSum_le s w r hw).trans (factorial_term_uniform (sum_nonneg hw) r)

end BretecheTenenbaumMean
