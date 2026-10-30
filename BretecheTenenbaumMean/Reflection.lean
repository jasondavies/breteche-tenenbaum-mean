module

public import BretecheTenenbaumMean.MomentRecurrence

@[expose] public section

/-! # Reflection of divisor windows

The involution `d ↦ n/d` reflects logarithmic divisors. Half-open endpoint
conventions change under reflection, so the symmetry is almost everywhere.
-/

namespace BretecheTenenbaumMean

open Real MeasureTheory Set

theorem delta_reflect_eq_sum (n : ℕ) (u : ℝ) :
    delta n (log n - 1 - u) = ∑ d ∈ n.divisors,
      (Ioc (log d - 1) (log d)).indicator (fun _ : ℝ => (1 : ℝ)) u := by
  classical
  rw [delta_eq_sum_indicator, ← Nat.sum_div_divisors n
    (fun d => (Ico (log d - 1) (log d)).indicator (fun _ : ℝ => (1 : ℝ)) (log n - 1 - u))]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_mem_divisors hd
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd0, Real.log_div hn0 hd0]
  have h : (log n - 1 - u ∈ Ico (log n - log d - 1) (log n - log d)) ↔
      u ∈ Ioc (log d - 1) (log d) := by
    simp only [Set.mem_Ico, Set.mem_Ioc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simp only [Set.indicator, h]

theorem delta_reflect_ae (n : ℕ) :
    (fun u => delta n (log n - 1 - u)) =ᵐ[volume] delta n := by
  have h (d : ℕ) :
      (Ioc (log d - 1) (log d)).indicator (fun _ : ℝ => (1 : ℝ)) =ᵐ[volume]
        (Ico (log d - 1) (log d)).indicator (fun _ : ℝ => (1 : ℝ)) :=
    indicator_ae_eq_of_ae_eq_set Ico_ae_eq_Ioc.symm
  filter_upwards [ae_all_iff.mpr h] with u hu
  rw [delta_reflect_eq_sum, delta_eq_sum_indicator]
  exact Finset.sum_congr rfl (fun d _ => hu d)

/-- Reflection and translation interchange the two factors of a mixed moment. -/
theorem mixedMoment_symm (n p q j : ℕ) (hj : j ≤ q) :
    mixedMoment j q n p = mixedMoment (q - j) q n p := by
  have hshift := (measurePreserving_sub_right volume (log (p : ℝ))).quasiMeasurePreserving.ae
    (delta_reflect_ae n)
  calc
    mixedMoment j q n p = ∫ u : ℝ,
        delta n (log n - 1 + log p - u) ^ j *
          delta n (log n - 1 + log p - u - log p) ^ (q - j) :=
      (integral_sub_left_eq_self
        (fun u => delta n u ^ j * delta n (u - log p) ^ (q - j))
        volume (log n - 1 + log p)).symm
    _ = mixedMoment (q - j) q n p := by
      apply integral_congr_ae
      filter_upwards [delta_reflect_ae n, hshift] with u hu hs
      change delta n (log n - 1 - (u - log p)) = delta n (u - log p) at hs
      have h₁ : log (n : ℝ) - 1 + log p - u = log n - 1 - (u - log p) := by ring
      have h₂ : log (n : ℝ) - 1 + log p - u - log p = log n - 1 - u := by ring
      change delta n (log n - 1 + log p - u) ^ j *
        delta n (log n - 1 + log p - u - log p) ^ (q - j) = _
      rw [h₂, h₁, hu, hs, Nat.sub_sub_self hj]
      exact mul_comm _ _

end BretecheTenenbaumMean
