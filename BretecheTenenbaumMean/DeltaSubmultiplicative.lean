module

public import BretecheTenenbaumMean.Probability

@[expose] public section

/-! # Multiplication bounds without a coprimality hypothesis -/

namespace BretecheTenenbaumMean

open Finset Real

/-- Divisor factorization gives submultiplicativity of the divisor count. -/
theorem tau_mul_le (m n : ℕ) : tau (m * n) ≤ tau m * tau n := by
  have h : (m * n).divisors.card ≤ m.divisors.card * n.divisors.card := by
    rw [Nat.divisors_mul]
    exact card_mul_le
  unfold tau
  exact_mod_cast h

/-- Each divisor of `m*n` factors as a divisor of `m` times a divisor of `n`.
Taking a union permits overlap, so coprimality is unnecessary for the bound. -/
theorem divisorWindow_mul_le_sum (m n : ℕ) (u : ℝ) :
    divisorWindow (m * n) u ≤ ∑ a ∈ m.divisors, divisorWindow n (u - log a) := by
  classical
  by_cases hm : m = 0
  · simp [hm, divisorWindow]
  by_cases hn : n = 0
  · simp [hn, divisorWindow]
  let W := fun a : ℕ ↦ n.divisors.filter (fun b : ℕ ↦ u - log a < log b ∧ log b ≤ u - log a + 1)
  let S := m.divisors.biUnion (fun a ↦ (W a).image (fun b ↦ a * b))
  have hsub : ((m * n).divisors.filter (fun d : ℕ ↦ u < log d ∧ log d ≤ u + 1)) ⊆ S := by
    intro d hd
    obtain ⟨hd, hdlo, hdhi⟩ := mem_filter.1 hd
    obtain ⟨a, b, ham, hbn, hdab⟩ := exists_dvd_and_dvd_of_dvd_mul (Nat.mem_divisors.1 hd).1
    have ha : a ∈ m.divisors := Nat.mem_divisors.2 ⟨ham, hm⟩
    have hb : b ∈ n.divisors := Nat.mem_divisors.2 ⟨hbn, hn⟩
    have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors ha).ne'
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hb).ne'
    rw [hdab, Nat.cast_mul, log_mul ha0 hb0] at hdlo hdhi
    apply mem_biUnion.2
    refine ⟨a, ha, mem_image.2 ⟨b, ?_, hdab.symm⟩⟩
    exact mem_filter.2 ⟨hb, by constructor <;> linarith⟩
  calc
    _ ≤ S.card := card_le_card hsub
    _ ≤ ∑ a ∈ m.divisors, ((W a).image (fun b ↦ a * b)).card := card_biUnion_le
    _ ≤ ∑ a ∈ m.divisors, (W a).card := sum_le_sum (fun a _ ↦ card_image_le)
    _ = _ := rfl

/-- A general divisor-count bound for a product window. -/
theorem divisorWindow_mul_le_general (m n : ℕ) (u : ℝ) :
    divisorWindow (m * n) u ≤ m.divisors.card * hooleyDelta n := by
  calc
    _ ≤ ∑ a ∈ m.divisors, divisorWindow n (u - log a) := divisorWindow_mul_le_sum m n u
    _ ≤ ∑ _ ∈ m.divisors, hooleyDelta n :=
      sum_le_sum (fun a _ ↦ divisorWindow_le_delta n (u - log a))
    _ = _ := by simp

/-- General submultiplicative divisor-count control for the maximum. -/
theorem hooleyDelta_mul_le_general (m n : ℕ) :
    hooleyDelta (m * n) ≤ m.divisors.card * hooleyDelta n := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨u, rfl⟩
  exact divisorWindow_mul_le_general m n u

theorem hooleyDelta_mul_le_tau (m n : ℕ) :
    (hooleyDelta (m * n) : ℝ) ≤ tau m * (hooleyDelta n : ℝ) := by
  unfold tau
  exact_mod_cast hooleyDelta_mul_le_general m n

end BretecheTenenbaumMean
