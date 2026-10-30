module

public import BretecheTenenbaumMean.Reflection

@[expose] public section

/-! # The half-range upper recurrence (1.4) -/

namespace BretecheTenenbaumMean

open Finset

/-- Folding a nonnegative symmetric finite sum about its midpoint. For even
`q`, the midpoint is counted twice on the right, giving an inequality. -/
theorem sum_le_twice_half (q : ℕ) (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j)
    (hs : ∀ j ≤ q, f (q - j) = f j) :
    ∑ j ∈ range (q + 1), f j ≤ 2 * (f 0 + ∑ j ∈ Icc 1 (q / 2), f j) := by
  have hu : ∑ j ∈ Ico (q / 2 + 1) (q + 1), f j ≤ ∑ j ∈ range (q / 2 + 1), f j := by
    apply Finset.sum_le_sum_of_injOn (fun j => q - j)
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_Ico] at ha hb
      change q - a = q - b at hab
      omega
    · intro j hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      simp only [Finset.mem_Ico] at hk
      simp only [Finset.mem_range]
      omega
    · intro j hj
      rw [hs j (by have := (Finset.mem_Ico.mp hj).2; omega)]
    · exact fun a _ _ => hf a
  have he := Finset.sum_range_add_sum_Ico f (show q / 2 + 1 ≤ q + 1 by omega)
  have hl : ∑ j ∈ range (q / 2 + 1), f j = f 0 + ∑ j ∈ Icc 1 (q / 2), f j := by
    rw [Finset.sum_range_eq_add_Ico f (by omega), Finset.Ico_add_one_right_eq_Icc]
  linarith

/-- `W_q(n,p)` as defined in (1.5). -/
noncomputable def mixedRemainder (q n p : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (q / 2), (q.choose j : ℝ) * mixedMoment j q n p

theorem moment_mul_prime_le {n p q : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) (hq : 1 ≤ q) :
    moment q (n * p) ≤ 2 * moment q n + 2 * mixedRemainder q n p := by
  rw [moment_mul_prime hp hpn hq]
  have h := sum_le_twice_half q (fun j => (q.choose j : ℝ) * mixedMoment j q n p)
    (fun j => mul_nonneg (Nat.cast_nonneg _) (mixedMoment_nonneg _ _ _ _))
    (fun j hj => by rw [Nat.choose_symm hj, ← mixedMoment_symm n p q j hj])
  simpa [mixedRemainder, mul_add] using h

/-- Both sides of (1.4). -/
theorem moment_recurrence {n p q : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) (hq : 1 ≤ q) :
    2 * moment q n ≤ moment q (n * p) ∧
      moment q (n * p) ≤ 2 * moment q n + 2 * mixedRemainder q n p :=
  ⟨two_mul_moment_le hp hpn hq, moment_mul_prime_le hp hpn hq⟩

end BretecheTenenbaumMean
