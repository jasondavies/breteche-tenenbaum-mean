module

public import BretecheTenenbaumMean.PrimeSums.Strict
public import NairTenenbaum.PrimeLogSums

@[expose] public section

/-! # Reciprocal-prime sums with the small power tilt used in §3 -/

namespace BretecheTenenbaumMean.PrimeSums

open Finset Real

/-- An elementary tangent-line bound, uniform on the unit interval. -/
lemma exp_le_one_add_exp_one_mul {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    exp v ≤ 1 + exp 1 * v := by
  have h := mul_le_mul_of_nonneg_right (add_one_le_exp (-v)) (exp_pos v).le
  rw [← exp_add, neg_add_cancel, exp_zero] at h
  have hm := mul_le_mul_of_nonneg_right (exp_le_exp.2 hv1) hv
  nlinarith

/-- Tilting by `p^(1/log y)` changes the reciprocal-prime sum by only a
bounded amount, independently of the cutoff. -/
theorem tilted_prime_sum_le : ∃ H ≥ 0, ∀ y : ℝ, 2 ≤ y →
    (∑ p ∈ primesLT y, (p : ℝ) ^ (1 / log y) / p) ≤ log (log y) + H := by
  obtain ⟨K, hK, herr⟩ := abs_SLT_sub_loglog_le
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hl4 : 0 < log (4 : ℝ) := log_pos (by norm_num)
  let D := log 4 * (1 + (log 2)⁻¹)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨K + exp 1 * D, by positivity, fun y hy ↦ ?_⟩
  have hly : 0 < log y := log_pos (by linarith)
  have hlogs : (∑ p ∈ primesLT y, log p / p) ≤ D * log y := by
    have hsub : primesLT y ⊆ (Icc 0 ⌊y⌋₊).filter Nat.Prime := by
      intro p hp
      obtain ⟨hp, hpy⟩ := mem_primesLT.1 hp
      exact mem_filter.2 ⟨mem_Icc.2 ⟨Nat.zero_le _, Nat.le_floor hpy.le⟩, hp⟩
    have hone : 1 ≤ (log 2)⁻¹ * log y := by
      have h := mul_le_mul_of_nonneg_left (log_le_log (by norm_num) hy) (inv_nonneg.2 hl2.le)
      rwa [inv_mul_cancel₀ hl2.ne'] at h
    calc
      _ ≤ NairTenenbaum.primeLogSum y := by
        apply sum_le_sum_of_subset_of_nonneg hsub
        intro p hp _
        exact div_nonneg (log_nonneg (by exact_mod_cast (mem_filter.1 hp).2.one_le))
          (Nat.cast_nonneg _)
      _ ≤ log 4 * (1 + log y) := NairTenenbaum.primeLogSum_le hy
      _ ≤ _ := by dsimp [D]; nlinarith [mul_le_mul_of_nonneg_left hone hl4.le]
  have hterm : ∀ p ∈ primesLT y,
      (p : ℝ) ^ (1 / log y) / p ≤ (p : ℝ)⁻¹ + (exp 1 / log y) * (log p / p) := by
    intro p hp
    obtain ⟨hp, hpy⟩ := mem_primesLT.1 hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hlp : 0 ≤ log p := log_nonneg (by exact_mod_cast hp.one_le)
    have hratio : log p / log y ≤ 1 := (div_le_one hly).2 (log_le_log hp0 hpy.le)
    have he := exp_le_one_add_exp_one_mul (div_nonneg hlp hly.le) hratio
    rw [rpow_def_of_pos hp0]
    have hid : log (p : ℝ) * (1 / log y) = log p / log y := by ring
    rw [hid]
    have hh := div_le_div_of_nonneg_right he hp0.le
    convert hh using 1; ring
  calc
    _ ≤ ∑ p ∈ primesLT y, ((p : ℝ)⁻¹ + (exp 1 / log y) * (log p / p)) :=
      sum_le_sum hterm
    _ = SLT y + (exp 1 / log y) * ∑ p ∈ primesLT y, log p / p := by
      rw [sum_add_distrib, ← mul_sum]; rfl
    _ ≤ (log (log y) + K) + (exp 1 / log y) * (D * log y) :=
      add_le_add (by have := (abs_le.1 (herr y hy)).2; linarith)
        (mul_le_mul_of_nonneg_left hlogs (by positivity))
    _ = _ := by field_simp; ring

end BretecheTenenbaumMean.PrimeSums
