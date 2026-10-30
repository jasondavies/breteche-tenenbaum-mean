module

public import BretecheTenenbaumMean.DistinctProductSum

@[expose] public section

/-! # Lower bounds for weighted products of distinct elements -/

namespace BretecheTenenbaumMean

open Finset Real

@[simp] lemma distinctProductSum_zero {α : Type*} (s : Finset α) (w : α → ℝ) :
    distinctProductSum s w 0 = 1 := by simp [distinctProductSum]

@[simp] lemma distinctProductSum_one {α : Type*} (s : Finset α) (w : α → ℝ) :
    distinctProductSum s w 1 = ∑ a ∈ s, w a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [distinctProductSum, powersetCard_eq_empty.2 (by simp : (∅ : Finset α).card < 1)]
  | @insert a s ha ih => rw [distinctProductSum_insert s w ha 0, distinctProductSum_zero, ih, sum_insert ha]; ring

lemma distinctProductSum_nonneg {α : Type*} (s : Finset α) (w : α → ℝ) (r : ℕ)
    (hw : ∀ a ∈ s, 0 ≤ w a) : 0 ≤ distinctProductSum s w r := by
  apply sum_nonneg
  intro t ht
  exact prod_nonneg (fun a ha ↦ hw a ((mem_powersetCard.1 ht).1 ha))

lemma distinctProductSum_mono {α : Type*} {s t : Finset α} (hst : s ⊆ t) (w : α → ℝ) (r : ℕ)
    (hw : ∀ a ∈ t, 0 ≤ w a) : distinctProductSum s w r ≤ distinctProductSum t w r := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro u hu
    obtain ⟨hus, hur⟩ := mem_powersetCard.1 hu
    exact mem_powersetCard.2 ⟨hus.trans hst, hur⟩
  · intro u hu _
    exact prod_nonneg (fun a ha ↦ hw a ((mem_powersetCard.1 hu).1 ha))

/-- Count a weighted subset once for each choice of a distinguished member. -/
theorem distinctProductSum_marked {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ) (r : ℕ) :
    (∑ a ∈ s, w a * distinctProductSum (s.erase a) w r) =
      (r + 1 : ℕ) * distinctProductSum s w (r + 1) := by
  induction s using Finset.induction_on generalizing r with
  | empty => simp [distinctProductSum, powersetCard_eq_empty.2 (by simp : (∅ : Finset α).card < r + 1)]
  | @insert a s ha ih =>
    cases r with
    | zero => simp
    | succ r =>
      rw [sum_insert ha, erase_insert ha]
      have he : (∑ b ∈ s, w b * distinctProductSum ((insert a s).erase b) w (r + 1)) =
          (∑ b ∈ s, w b * distinctProductSum (s.erase b) w (r + 1)) +
          w a * ∑ b ∈ s, w b * distinctProductSum (s.erase b) w r := by
        rw [mul_sum, ← sum_add_distrib]
        apply sum_congr rfl
        intro b hb
        have hab : a ≠ b := fun h ↦ ha (h ▸ hb)
        rw [erase_insert_of_ne hab, distinctProductSum_insert (s.erase b) w (by simp [ha]) r]
        ring
      rw [he, ih (r + 1), ih r, distinctProductSum_insert s w ha (r + 1)]
      push_cast
      ring

/-- The error in the elementary-symmetric recurrence consists precisely of
terms in which the newly chosen element repeats an earlier one. -/
theorem distinctProductSum_repeat_identity {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ) (r : ℕ) :
    (∑ a ∈ s, w a) * distinctProductSum s w (r + 1) =
      (r + 2 : ℕ) * distinctProductSum s w (r + 2) +
        ∑ a ∈ s, w a ^ 2 * distinctProductSum (s.erase a) w r := by
  rw [← distinctProductSum_marked s w (r + 1), ← sum_add_distrib, sum_mul]
  apply sum_congr rfl
  intro a ha
  have he := distinctProductSum_insert (s.erase a) w (notMem_erase a s) r
  rw [insert_erase ha] at he
  rw [he]
  ring

lemma distinctProductSum_repeat_le {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℝ) (r : ℕ) (hw : ∀ a ∈ s, 0 ≤ w a) :
    (∑ a ∈ s, w a) * distinctProductSum s w (r + 1) ≤
      (r + 2 : ℕ) * distinctProductSum s w (r + 2) +
        (∑ a ∈ s, w a ^ 2) * (∑ a ∈ s, w a) ^ r / (r.factorial : ℝ) := by
  rw [distinctProductSum_repeat_identity]
  apply add_le_add_right
  rw [mul_div_assoc, sum_mul]
  apply sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact (distinctProductSum_mono (erase_subset a s) w r hw).trans (distinctProductSum_le s w r hw)

/-- The weighted union bound for repeated elements, expressed without tuples. -/
theorem distinctProductSum_collision_bound {α : Type*}
    (s : Finset α) (w : α → ℝ) (k : ℕ) (hw : ∀ a ∈ s, 0 ≤ w a) :
    (∑ a ∈ s, w a) ^ (k + 2) ≤
      ((k + 2).factorial : ℝ) * distinctProductSum s w (k + 2) +
        (((k : ℝ) + 2) * (k + 1) / 2) * (∑ a ∈ s, w a ^ 2) * (∑ a ∈ s, w a) ^ k := by
  classical
  let S := ∑ a ∈ s, w a
  let Q := ∑ a ∈ s, w a ^ 2
  have hS : 0 ≤ S := sum_nonneg hw
  induction k with
  | zero =>
    have h := distinctProductSum_repeat_le s w 0 hw
    simpa [distinctProductSum_one, pow_two] using h
  | succ k ih =>
    change S ^ (k + 2) ≤ ((k + 2).factorial : ℝ) * distinctProductSum s w (k + 2) +
      (((k : ℝ) + 2) * (k + 1) / 2) * Q * S ^ k at ih
    have hi := mul_le_mul_of_nonneg_left ih hS
    have hr := distinctProductSum_repeat_le s w (k + 1) hw
    have hf : 0 < ((k + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    change S * distinctProductSum s w (k + 2) ≤
      (k + 3 : ℕ) * distinctProductSum s w (k + 3) + Q * S ^ (k + 1) / ((k + 1).factorial : ℝ) at hr
    have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ ((k + 2).factorial : ℝ) by positivity)
    have he : ((k + 2).factorial : ℝ) * (Q * S ^ (k + 1) / ((k + 1).factorial : ℝ)) =
        ((k : ℝ) + 2) * Q * S ^ (k + 1) := by
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    rw [mul_add, he] at hh
    have hfac : ((k + 3).factorial : ℝ) = ((k : ℝ) + 3) * ((k + 2).factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    change S ^ (k + 1 + 2) ≤ ((k + 1 + 2).factorial : ℝ) * distinctProductSum s w (k + 1 + 2) +
      ((((k + 1 : ℕ) : ℝ) + 2) * ((k + 1 : ℕ) + 1) / 2) * Q * S ^ (k + 1)
    rw [hfac]
    push_cast at hi hh ⊢
    simp only [pow_succ] at hi hh ⊢
    nlinarith

/-- If the weighted collision budget is at most one, at least half of the
unrestricted exponential-series term comes from distinct elements. -/
theorem distinctProductSum_lower_half {α : Type*} (s : Finset α) (w : α → ℝ) (r : ℕ)
    (hw : ∀ a ∈ s, 0 ≤ w a)
    (hcollision : (r : ℝ) ^ 2 * (∑ a ∈ s, w a ^ 2) ≤ (∑ a ∈ s, w a) ^ 2) :
    (∑ a ∈ s, w a) ^ r / (2 * (r.factorial : ℝ)) ≤ distinctProductSum s w r := by
  have hS : 0 ≤ ∑ a ∈ s, w a := sum_nonneg hw
  cases r with
  | zero => norm_num
  | succ r =>
    cases r with
    | zero => simpa using (show (∑ a ∈ s, w a) / 2 ≤ ∑ a ∈ s, w a by linarith)
    | succ k =>
      have h := distinctProductSum_collision_bound s w k hw
      have he := mul_le_mul_of_nonneg_right hcollision (pow_nonneg hS k)
      have hQ : 0 ≤ (∑ a ∈ s, w a ^ 2) * (∑ a ∈ s, w a) ^ k := by positivity
      have hf : 0 < ((k + 2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      apply (div_le_iff₀ (show (0 : ℝ) < 2 * ((k + 2).factorial : ℝ) by positivity)).2
      let S := ∑ a ∈ s, w a
      let Q := ∑ a ∈ s, w a ^ 2
      change S ^ (k + 2) ≤ ((k + 2).factorial : ℝ) * distinctProductSum s w (k + 2) +
        (((k : ℝ) + 2) * (k + 1) / 2) * Q * S ^ k at h
      change ((k + 1 + 1 : ℕ) : ℝ) ^ 2 * Q * S ^ k ≤ S ^ 2 * S ^ k at he
      change 0 ≤ Q * S ^ k at hQ
      change S ^ (k + 2) ≤ distinctProductSum s w (k + 2) * (2 * ((k + 2).factorial : ℝ))
      push_cast at he
      simp only [pow_succ, pow_zero, one_mul] at h he ⊢
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ k + 2 by positivity) hQ]

end BretecheTenenbaumMean
