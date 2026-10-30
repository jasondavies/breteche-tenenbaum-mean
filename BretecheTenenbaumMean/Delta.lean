module

public import BretecheTenenbaumMean.Definitions

@[expose] public section

/-! # Hooley's divisor concentration function

The definition in §1 of arXiv:2309.03958v14. Adapted from the local
NairTenenbaum/Hooley.lean; see SOURCES.md. Logarithmic windows are equivalent
to exponential windows for positive divisors.
-/

namespace BretecheTenenbaumMean

open Finset Real

theorem divisorWindow_le_card (n : ℕ) (u : ℝ) : divisorWindow n u ≤ n.divisors.card :=
  Finset.card_filter_le _ _

theorem divisorWindow_bddAbove (n : ℕ) : BddAbove (Set.range (divisorWindow n)) :=
  ⟨n.divisors.card, fun _ ⟨u, hu⟩ => hu ▸ divisorWindow_le_card n u⟩

theorem divisorWindow_le_delta (n : ℕ) (u : ℝ) : divisorWindow n u ≤ hooleyDelta n :=
  le_csSup (divisorWindow_bddAbove n) (Set.mem_range_self u)

theorem hooleyDelta_le_card (n : ℕ) : hooleyDelta n ≤ n.divisors.card :=
  csSup_le (Set.range_nonempty _) (fun _ ⟨u, hu⟩ => hu ▸ divisorWindow_le_card n u)

theorem hooleyDelta_attained (n : ℕ) : ∃ u, divisorWindow n u = hooleyDelta n :=
  Nat.sSup_mem (Set.range_nonempty _) (divisorWindow_bddAbove n)

@[simp] theorem hooleyDelta_zero : hooleyDelta 0 = 0 := by
  exact Nat.eq_zero_of_le_zero (by simpa using hooleyDelta_le_card 0)

theorem one_le_hooleyDelta {n : ℕ} (hn : n ≠ 0) : 1 ≤ hooleyDelta n := by
  apply le_trans _ (divisorWindow_le_delta n (-(1 / 2)))
  apply Finset.one_le_card.mpr
  exact ⟨1, Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr hn, by norm_num⟩⟩

@[simp] theorem hooleyDelta_one : hooleyDelta 1 = 1 :=
  le_antisymm (by simpa using hooleyDelta_le_card 1) (one_le_hooleyDelta one_ne_zero)

theorem divisorWindow_eq_sum (n : ℕ) (u : ℝ) :
    divisorWindow n u = ∑ d ∈ n.divisors, if u < log d ∧ log d ≤ u + 1 then 1 else 0 := by
  classical
  simp [divisorWindow]

/-- The logarithmic definition agrees exactly with the paper's exponential window. -/
theorem divisorWindow_eq_exp (n : ℕ) (u : ℝ) :
    divisorWindow n u = (n.divisors.filter fun d : ℕ => exp u < d ∧ (d : ℝ) ≤ exp (u + 1)).card := by
  classical
  unfold divisorWindow
  congr 1
  apply Finset.filter_congr
  intro d hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  rw [Real.lt_log_iff_exp_lt hdpos, Real.log_le_iff_le_exp hdpos]

theorem sum_divisors_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n) (f : ℕ → ℕ) :
    ∑ d ∈ (m * n).divisors, f d = ∑ a ∈ m.divisors, ∑ b ∈ n.divisors, f (a * b) := by
  rw [hmn.divisors_mul, Finset.sum_map]
  change (∑ d ∈ (m.divisors ×ˢ n.divisors).attach, f (d.val.1 * d.val.2)) = _
  rw [Finset.sum_attach _ (fun d : ℕ × ℕ => f (d.1 * d.2)), Finset.sum_product]

/-- Exact splitting of a divisor window over coprime factors. -/
theorem divisorWindow_mul {m n : ℕ} (hmn : m.Coprime n) (u : ℝ) :
    divisorWindow (m * n) u = ∑ a ∈ m.divisors, divisorWindow n (u - log a) := by
  classical
  rw [divisorWindow_eq_sum, sum_divisors_mul_of_coprime hmn]
  apply Finset.sum_congr rfl
  intro a ha
  rw [divisorWindow_eq_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors ha).ne'
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hb).ne'
  rw [Nat.cast_mul, Real.log_mul ha0 hb0]
  congr 1
  apply propext
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- A coprime multiplication bound. -/
theorem hooleyDelta_mul_le {m n : ℕ} (hmn : m.Coprime n) :
    hooleyDelta (m * n) ≤ m.divisors.card * hooleyDelta n := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨u, rfl⟩
  rw [divisorWindow_mul hmn]
  calc
    ∑ a ∈ m.divisors, divisorWindow n (u - log a) ≤ ∑ _a ∈ m.divisors, hooleyDelta n :=
      Finset.sum_le_sum fun a _ => divisorWindow_le_delta n _
    _ = m.divisors.card * hooleyDelta n := by simp

/-- An arbitrary logarithmic window dominates every shorter interval of divisors. -/
theorem divisor_interval_le_delta {n : ℕ} {D E : ℝ} (hD : 0 < D) (hE : E ≤ exp 1 * D) :
    (n.divisors.filter fun d : ℕ => D < d ∧ (d : ℝ) ≤ E).card ≤ hooleyDelta n := by
  apply le_trans _ (divisorWindow_le_delta n (log D))
  apply Finset.card_le_card
  intro d hd
  obtain ⟨hdn, hdD, hdE⟩ := Finset.mem_filter.mp hd
  have hdpos : (0 : ℝ) < d := hD.trans hdD
  apply Finset.mem_filter.mpr
  refine ⟨hdn, (Real.log_lt_log hD hdD), ?_⟩
  calc
    log d ≤ log (exp 1 * D) := Real.log_le_log hdpos (hdE.trans hE)
    _ = log D + 1 := by rw [Real.log_mul (ne_of_gt (exp_pos _)) hD.ne', log_exp]; ring

/-- The pointwise dyadic divisor bound used in Corollary 5. -/
theorem dyadic_divisors_le_delta {n : ℕ} {D : ℝ} (hD : 0 < D) :
    (n.divisors.filter fun d : ℕ => D < d ∧ (d : ℝ) ≤ 2 * D).card ≤ hooleyDelta n := by
  apply divisor_interval_le_delta hD
  exact mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (1 : ℝ)]) hD.le

end BretecheTenenbaumMean
