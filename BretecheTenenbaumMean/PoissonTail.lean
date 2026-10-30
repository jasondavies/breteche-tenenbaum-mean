module

public import BretecheTenenbaumMean.PoissonBound
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! # Factorial tails and the Poisson rate function -/

namespace BretecheTenenbaumMean

open Real Finset

noncomputable def poissonTerm (u : ℝ) (k : ℕ) : ℝ := u ^ k / (k.factorial : ℝ)

theorem poissonTerm_nonneg {u : ℝ} (hu : 0 ≤ u) (k : ℕ) : 0 ≤ poissonTerm u k := by
  unfold poissonTerm
  positivity

theorem poissonTerm_succ (u : ℝ) (k : ℕ) :
    poissonTerm u (k + 1) = poissonTerm u k * (u / (k + 1)) := by
  simp only [poissonTerm, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Above a threshold, successive factorial terms decrease geometrically. -/
theorem poissonTerm_shift_le {u ρ : ℝ} {k : ℕ} (hu : 0 ≤ u) (hρ : 0 ≤ ρ)
    (hk : u ≤ ρ * (k + 1)) (j : ℕ) :
    poissonTerm u (k + j) ≤ poissonTerm u k * ρ ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show k + (j + 1) = (k + j) + 1 by omega, poissonTerm_succ, pow_succ]
    have hden : 0 < ((k + j : ℕ) : ℝ) + 1 := by positivity
    have hratio : u / (((k + j : ℕ) : ℝ) + 1) ≤ ρ := by
      rw [div_le_iff₀ hden]
      push_cast
      nlinarith [mul_nonneg hρ (Nat.cast_nonneg j)]
    calc _ ≤ (poissonTerm u k * ρ ^ j) * ρ :=
        mul_le_mul ih hratio (div_nonneg hu hden.le)
          (mul_nonneg (poissonTerm_nonneg hu k) (pow_nonneg hρ j))
      _ = _ := by ring

/-- Any finite portion of a factorial tail has the same geometric bound. -/
theorem sum_poissonTerm_tail_le {u ρ : ℝ} {k : ℕ} (hu : 0 ≤ u) (hρ : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hk : u ≤ ρ * (k + 1)) (s : Finset ℕ) (hs : ∀ r ∈ s, k ≤ r) :
    (∑ r ∈ s, poissonTerm u r) ≤ poissonTerm u k / (1 - ρ) := by
  classical
  let J := s.image (fun r ↦ r - k)
  have hinj : Set.InjOn (fun r : ℕ ↦ r - k) s := by
    intro r hr t ht he
    change r - k = t - k at he
    have := hs r hr
    have := hs t ht
    omega
  have he : (∑ r ∈ s, poissonTerm u r) = ∑ j ∈ J, poissonTerm u (k + j) := by
    rw [Finset.sum_image hinj]
    apply sum_congr rfl
    intro r hr
    rw [Nat.add_sub_of_le (hs r hr)]
  rw [he]
  calc _ ≤ ∑ j ∈ J, poissonTerm u k * ρ ^ j :=
      sum_le_sum (fun j _ ↦ poissonTerm_shift_le hu hρ hk j)
    _ = poissonTerm u k * ∑ j ∈ J, ρ ^ j := (mul_sum _ _ _).symm
    _ ≤ poissonTerm u k * (1 - ρ)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (poissonTerm_nonneg hu k)
      calc _ ≤ ∑' j : ℕ, ρ ^ j :=
          (summable_geometric_of_lt_one hρ hρ1).sum_le_tsum _ (fun _ _ ↦ pow_nonneg hρ _)
        _ = _ := tsum_geometric_of_lt_one hρ hρ1
    _ = _ := (div_eq_mul_inv _ _).symm

/-- The standard rate function governing large Poisson deviations. -/
noncomputable def poissonRate (v : ℝ) : ℝ := v * log v - v + 1

/-- Stirling's lower bound, retaining the large-deviation exponential. -/
theorem poissonTerm_le_rate {u : ℝ} (hu : 0 < u) {k : ℕ} (hk : k ≠ 0) :
    poissonTerm u k ≤ exp (u * (1 - poissonRate (k / u))) / sqrt (2 * π * k) := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hfac : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hs : 0 < sqrt (2 * π * k) := sqrt_pos.2 (by positivity)
  have hpower : u ^ k = exp (u * (1 - poissonRate (k / u))) * ((k : ℝ) / exp 1) ^ k := by
    have he : u * (1 - poissonRate (k / u)) = (k : ℝ) * (1 + log u - log k) := by
      rw [poissonRate, log_div hk0.ne' hu.ne']
      field_simp
      ring
    rw [he, exp_nat_mul, ← mul_pow]
    congr 1
    rw [exp_sub, exp_add, exp_log hu, exp_log hk0]
    field_simp
  unfold poissonTerm
  rw [div_le_div_iff₀ hfac hs, hpower]
  have h := mul_le_mul_of_nonneg_left (Stirling.le_factorial_stirling k)
    (exp_pos (u * (1 - poissonRate (k / u)))).le
  convert h using 1
  ring

/-- A factorial tail with the sharp exponential and square-root prefactor. -/
theorem sum_poissonTerm_tail_le_rate {u ρ : ℝ} {k : ℕ}
    (hu : 0 < u) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hk0 : k ≠ 0)
    (hk : u ≤ ρ * (k + 1)) (s : Finset ℕ) (hs : ∀ r ∈ s, k ≤ r) :
    (∑ r ∈ s, poissonTerm u r) ≤
      exp (u * (1 - poissonRate (k / u))) / ((1 - ρ) * sqrt (2 * π * k)) := by
  calc _ ≤ poissonTerm u k / (1 - ρ) := sum_poissonTerm_tail_le hu.le hρ hρ1 hk s hs
    _ ≤ (exp (u * (1 - poissonRate (k / u))) / sqrt (2 * π * k)) / (1 - ρ) :=
      div_le_div_of_nonneg_right (poissonTerm_le_rate hu hk0) (by linarith)
    _ = _ := by rw [div_div]; congr 1; ring

end BretecheTenenbaumMean
