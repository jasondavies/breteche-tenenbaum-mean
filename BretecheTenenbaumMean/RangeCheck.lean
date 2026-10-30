module

public import BretecheTenenbaumMean.Probability

@[expose] public section

/-! # The lower tail needs a range condition

The upper exceptional-set bound in Proposition 2.1 is uniform in `x ≥ 2`.
The lower side of (2.5) cannot have that same uniform range.
-/

namespace BretecheTenenbaumMean

open Real Finset

@[simp] theorem primesLT_two : primesLT 2 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hp, hlt⟩ := mem_primesLT.mp hp
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  linarith

@[simp] theorem expectation_two (f : ℕ → ℝ) : expectation 2 f = f 1 := by
  simp [expectation, smoothSupport, primeProduct, normalizer]

@[simp] theorem moment_two_one : moment 2 1 = 1 := by
  simp [moment_two_eq_sum]

theorem lower_tail_at_two {T : ℝ} (hT : 1 ≤ T) :
    probability 2 {n | T < moment 2 n / tau n} = 0 := by
  rw [probability, expectation_two]
  simp [Set.indicator, tau, not_lt.mpr hT]

/-- No positive constant gives the lower side of (2.5) for all `x ≥ 2,T ≥ 3`. -/
theorem not_uniform_lower_tail :
    ¬ ∃ c > (0 : ℝ), ∀ x T : ℝ, 2 ≤ x → 3 ≤ T →
      c / T ≤ probability x {n | T < moment 2 n / tau n} := by
  rintro ⟨c, hc, h⟩
  have hbad := h 2 3 le_rfl le_rfl
  rw [lower_tail_at_two (by norm_num : (1 : ℝ) ≤ 3)] at hbad
  linarith

end BretecheTenenbaumMean
