module

public import BretecheTenenbaumMean.SqrtDivisorAverage
public import BretecheTenenbaumMean.RecursionErrorProducts

@[expose] public section

/-! # The product sum in the third-moment base case -/

namespace BretecheTenenbaumMean

open Finset Real

/-- The positive saving in (2.18), equal to `(3 - sqrt 8)/2`. -/
noncomputable def thirdMomentSaving : ℝ := 3 / 2 - sqrt 2

theorem thirdMomentSaving_pos : 0 < thirdMomentSaving := by
  have h := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs := sqrt_nonneg (2 : ℝ)
  dsimp only [thirdMomentSaving]
  nlinarith

theorem thirdMomentSaving_pow_identity {L : ℝ} (hL : 0 < L) :
    sqrt L * L ^ (sqrt 2) * L ^ thirdMomentSaving = L ^ 2 := by
  rw [sqrt_eq_rpow, ← rpow_add hL, ← rpow_add hL]
  have he : (1 / 2 : ℝ) + sqrt 2 + thirdMomentSaving = 2 := by
    dsimp only [thirdMomentSaving]
    ring
  rw [he]
  norm_num

theorem momentProductSum_three_one_eq (δ T y : ℝ) (θ : ℕ → ℝ) :
    momentProductSum δ T θ 3 1 y =
      ∑ m ∈ smoothSupport y, (momentGoodSet δ T θ 2).indicator (fun m ↦ moment 2 m / m) m := by
  classical
  unfold momentProductSum
  norm_num only [Nat.reduceSub, moment_one]
  apply sum_congr rfl
  intro m hm
  by_cases hE : m ∈ momentGoodSet δ T θ 2
  · simp only [Set.indicator_of_mem hE]
    have ht := tau_pos (mem_smoothSupport.1 hm).1.ne_zero
    field_simp
  · simp only [Set.indicator_of_notMem hE]

/-- The two independent elementary bounds underlying (2.18). -/
theorem momentProductSum_three_one_two_bounds : ∃ A > 0, ∃ B > 0,
    ∀ δ T (θ : ℕ → ℝ) (y : ℝ), 0 ≤ δ → 1 ≤ T → 1 ≤ y →
    momentProductSum δ T θ 3 1 y ≤ A * T * log (3 * y) ^ 2 ∧
    momentProductSum δ T θ 3 1 y ≤ B * T * sqrt T * sqrt (log (3 * y)) * log (3 * y) ^ (sqrt 2) := by
  classical
  obtain ⟨A, hA, hsum⟩ := sum_tau_div_bound
  obtain ⟨B, hB, hsqrt⟩ := sum_sqrt_tau_div_bound
  refine ⟨A, hA, B, hB, fun δ T θ y hδ hT hy ↦ ?_⟩
  have hT0 : 0 < T := by linarith
  have hL : 0 < log (3 * y) := log_pos (by linarith)
  let E := momentGoodSet δ T θ 2
  have hpoint : ∀ m ∈ smoothSupport y,
      E.indicator (fun m ↦ moment 2 m / m) m ≤ T * (tau m / m) ∧
      E.indicator (fun m ↦ moment 2 m / m) m ≤
        (T * sqrt T * sqrt (log (3 * y))) * (sqrt (tau m) / m) := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (mem_smoothSupport.1 hm).1.ne_zero
    have ht := tau_pos (mem_smoothSupport.1 hm).1.ne_zero
    by_cases hE : m ∈ E
    · rw [Set.indicator_of_mem hE]
      have hM : moment 2 m ≤ T * tau m := (div_le_iff₀ ht).1 hE.1.2
      have hτ := tau_le_goodSet_log hδ hT hy hm hE.1.1
      have hs := sqrt_le_sqrt hτ
      rw [sqrt_mul hT0.le] at hs
      have htau : tau m ≤ sqrt T * sqrt (log (3 * y)) * sqrt (tau m) := by
        have h := mul_le_mul_of_nonneg_right hs (sqrt_nonneg (tau m))
        rw [mul_self_sqrt ht.le] at h
        exact h
      constructor
      · simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hM hm0.le
      · have h := div_le_div_of_nonneg_right (hM.trans (mul_le_mul_of_nonneg_left htau hT0.le)) hm0.le
        convert h using 1; ring
    · rw [Set.indicator_of_notMem hE]
      constructor <;> positivity
  rw [momentProductSum_three_one_eq]
  constructor
  · calc
      _ ≤ ∑ m ∈ smoothSupport y, T * (tau m / m) := sum_le_sum (fun m hm ↦ (hpoint m hm).1)
      _ = T * ∑ m ∈ smoothSupport y, tau m / m := (mul_sum ..).symm
      _ ≤ T * (A * log (3 * y) ^ 2) := mul_le_mul_of_nonneg_left (hsum y hy) hT0.le
      _ = _ := by ring
  · calc
      _ ≤ ∑ m ∈ smoothSupport y, (T * sqrt T * sqrt (log (3 * y))) * (sqrt (tau m) / m) :=
        sum_le_sum (fun m hm ↦ (hpoint m hm).2)
      _ = (T * sqrt T * sqrt (log (3 * y))) * ∑ m ∈ smoothSupport y, sqrt (tau m) / m := (mul_sum ..).symm
      _ ≤ (T * sqrt T * sqrt (log (3 * y))) * (B * log (3 * y) ^ (sqrt 2)) :=
        mul_le_mul_of_nonneg_left (hsqrt y hy) (by positivity)
      _ = _ := by ring

/-- Equation (2.18), retaining `log(3y)` at the small endpoint. -/
theorem momentProductSum_three_one_bound : ∃ C > 0,
    ∀ δ T (θ : ℕ → ℝ) (y : ℝ), 0 ≤ δ → 1 ≤ T → 1 ≤ y →
    momentProductSum δ T θ 3 1 y ≤
      C * T * sqrt T * log (3 * y) ^ 2 / (sqrt T + log (3 * y) ^ thirdMomentSaving) := by
  obtain ⟨A, hA, B, hB, hbounds⟩ := momentProductSum_three_one_two_bounds
  refine ⟨A + B, by linarith, fun δ T θ y hδ hT hy ↦ ?_⟩
  have hT0 : 0 < T := by linarith
  have hL : 0 < log (3 * y) := log_pos (by linarith)
  obtain ⟨h1, h2⟩ := hbounds δ T θ y hδ hT hy
  have hfirst := mul_le_mul_of_nonneg_right h1 (sqrt_nonneg T)
  have hsecond := mul_le_mul_of_nonneg_right h2 (rpow_nonneg hL.le thirdMomentSaving)
  have he : (B * T * sqrt T * sqrt (log (3 * y)) * log (3 * y) ^ (sqrt 2)) *
      log (3 * y) ^ thirdMomentSaving = B * T * sqrt T * log (3 * y) ^ 2 := by
    have hh := thirdMomentSaving_pow_identity hL
    calc
      _ = B * T * sqrt T * (sqrt (log (3 * y)) * log (3 * y) ^ (sqrt 2) *
        log (3 * y) ^ thirdMomentSaving) := by ring
      _ = _ := by rw [hh]
  rw [he] at hsecond
  apply (le_div_iff₀ (by positivity : 0 < sqrt T + log (3 * y) ^ thirdMomentSaving)).2
  nlinarith

end BretecheTenenbaumMean
