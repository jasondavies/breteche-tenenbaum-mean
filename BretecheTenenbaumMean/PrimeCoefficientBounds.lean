module

public import BretecheTenenbaumMean.DistinctProductLower
public import BretecheTenenbaumMean.PowerComparison
public import BretecheTenenbaumMean.PrimeSums.Trimmed

@[expose] public section

/-! # Uniform Poisson-size coefficients of the reciprocal-prime Euler product -/

namespace BretecheTenenbaumMean

open Finset Real

/-- Uniform two-sided bounds when the number of primes is at most a fixed
multiple of `log log y`. The cutoff depends on that fixed multiple. -/
theorem reciprocal_prime_coefficient_bounds {A : ℝ} (hA : 0 < A) :
    ∃ c > 0, ∃ C > 0, ∃ L₀ > 0, ∀ y : ℝ, 2 ≤ y → L₀ ≤ log (log y) →
    ∀ k : ℕ, (k : ℝ) ≤ A * log (log y) →
      c * log (log y) ^ k / (k.factorial : ℝ) ≤
        distinctProductSum (primesLT y) (fun p ↦ (p : ℝ)⁻¹) k ∧
      distinctProductSum (primesLT y) (fun p ↦ (p : ℝ)⁻¹) k ≤
        C * log (log y) ^ k / (k.factorial : ℝ) := by
  obtain ⟨K, hK, hmertens⟩ := PrimeSums.trimmed_prime_sum_sub_loglog_bound
  obtain ⟨P, hP⟩ := exists_nat_gt (4 * A ^ 2 + 2)
  have hP2 : 2 ≤ P := by
    have hp : (2 : ℝ) < P := by nlinarith [sq_nonneg A]
    exact_mod_cast hp.le
  have hP1 : 0 < (P : ℝ) - 1 := by
    have hp : (2 : ℝ) ≤ P := by exact_mod_cast hP2
    linarith
  let H := K + P + 1
  have hH : 0 < H := by dsimp [H]; positivity
  let E := exp (2 * A * H)
  have hE : 0 < E := exp_pos _
  refine ⟨1 / (2 * E), by positivity, exp (A * H), exp_pos _, 2 * H, by positivity,
    fun y hy hL k hk ↦ ?_⟩
  let L := log (log y)
  let s := PrimeSums.trimmedPrimes P y
  let S := ∑ p ∈ s, (p : ℝ)⁻¹
  let Q := ∑ p ∈ s, ((p : ℝ)⁻¹) ^ 2
  let U := ∑ p ∈ primesLT y, (p : ℝ)⁻¹
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hSabs : |S - L| ≤ H := (hmertens P y hy).trans (by dsimp [H]; linarith)
  have hSL : L / 2 ≤ S := by
    have := (abs_le.1 hSabs).1
    dsimp [L] at *
    linarith
  have hS : 0 < S := by linarith
  have hSU : S ≤ U := sum_le_sum_of_subset_of_nonneg (PrimeSums.trimmedPrimes_subset P y)
    (fun _ _ _ ↦ by positivity)
  have hU : 0 < U := hS.trans_le hSU
  have hUL : U - L ≤ H := by
    have h := (hmertens 0 y hy)
    simp only [PrimeSums.trimmedPrimes, Nat.zero_le, filter_true_of_mem (fun _ _ ↦ True.intro),
      Nat.cast_zero, add_zero] at h
    have h' := (abs_le.1 h).2
    dsimp [U, L, H]
    linarith [Nat.cast_nonneg (α := ℝ) P]
  have hkS : (k : ℝ) ≤ (2 * A) * S := by nlinarith
  have hQ0 : 0 ≤ Q := sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hQ : 4 * A ^ 2 * Q ≤ 1 := by
    calc
      _ ≤ 4 * A ^ 2 * ((P : ℝ) - 1)⁻¹ :=
        mul_le_mul_of_nonneg_left (PrimeSums.trimmed_prime_inv_sq_le hP2 y) (by positivity)
      _ ≤ 1 := by rw [← div_eq_mul_inv]; apply (div_le_iff₀ hP1).2; nlinarith
  have hcollision : (k : ℝ) ^ 2 * Q ≤ S ^ 2 := by
    have hk2 : (k : ℝ) ^ 2 ≤ 4 * A ^ 2 * S ^ 2 := by nlinarith [mul_self_le_mul_self (Nat.cast_nonneg (α := ℝ) k) hkS]
    have h₁ := mul_le_mul_of_nonneg_right hk2 hQ0
    have h₂ := mul_le_mul_of_nonneg_right hQ (sq_nonneg S)
    nlinarith
  have hlow := distinctProductSum_lower_half s (fun p ↦ (p : ℝ)⁻¹) k
    (fun _ _ ↦ by positivity) hcollision
  have hpower := pow_le_exp_mul_pow_of_sub_le hL0 hS hH.le
    (by linarith [(abs_le.1 hSabs).1] : L - S ≤ H) hkS
  have hfac : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  constructor
  · calc
      _ = L ^ k / (2 * E * (k.factorial : ℝ)) := by dsimp [L]; ring
      _ ≤ E * S ^ k / (2 * E * (k.factorial : ℝ)) := div_le_div_of_nonneg_right hpower (by positivity)
      _ = S ^ k / (2 * (k.factorial : ℝ)) := by field_simp
      _ ≤ distinctProductSum s (fun p ↦ (p : ℝ)⁻¹) k := hlow
      _ ≤ _ := distinctProductSum_mono (PrimeSums.trimmedPrimes_subset P y) _ _ (fun _ _ ↦ by positivity)
  · calc
      _ ≤ U ^ k / (k.factorial : ℝ) := distinctProductSum_le _ _ _ (fun _ _ ↦ by positivity)
      _ ≤ _ := div_le_div_of_nonneg_right (pow_le_exp_mul_pow_of_sub_le hU hL0 hH.le hUL hk) hfac.le

end BretecheTenenbaumMean
