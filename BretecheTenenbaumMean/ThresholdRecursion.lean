module

public import BretecheTenenbaumMean.RecursionDecay
public import BretecheTenenbaumMean.Targets

@[expose] public section

/-! # Absorbing the factorial error in the threshold sequence -/

namespace BretecheTenenbaumMean

open Finset Real MeasureTheory

/-- The factorial lower bound on `θ(q-1)` absorbs the accumulated error
with a geometric saving in `q`. -/
theorem factorial_error_le_threshold {B C₀ T : ℝ} (hB : 1 ≤ B) (hC : 4 * B ≤ C₀)
    (hT : 1 ≤ T) {q : ℕ} (hq : 3 ≤ q) {θ : ℕ → ℝ}
    (hθ : ((q - 1).factorial : ℝ) * (C₀ * T) ^ (q - 2) ≤ θ (q - 1)) :
    1 + B ^ q * (q.factorial : ℝ) * T ^ (q - 2) ≤
      32 * B ^ 2 * θ (q - 1) / 2 ^ q := by
  have hB0 : 0 < B := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hqpow : (q : ℝ) ≤ 2 ^ q := by exact_mod_cast (Nat.lt_two_pow_self (n := q)).le
  have hfac : (q.factorial : ℝ) = (q : ℝ) * ((q - 1).factorial : ℝ) := by
    have he : q = (q - 1) + 1 := by omega
    conv_lhs => rw [he, Nat.factorial_succ, Nat.cast_mul]
    congr 1
    exact_mod_cast he.symm
  have herror : 1 ≤ B ^ q * (q.factorial : ℝ) * T ^ (q - 2) := by
    have hb : 1 ≤ B ^ q := one_le_pow₀ hB
    have ht : 1 ≤ T ^ (q - 2) := one_le_pow₀ hT
    have hf : (1 : ℝ) ≤ q.factorial := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero q))
    nlinarith [mul_le_mul_of_nonneg_left hf (pow_nonneg hB0.le q)]
  have hpow : (4 * B * T) ^ (q - 2) ≤ (C₀ * T) ^ (q - 2) :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hC hT0) _
  have hθ' : ((q - 1).factorial : ℝ) * (4 * B * T) ^ (q - 2) ≤ θ (q - 1) :=
    (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)).trans hθ
  have hleft : (2 : ℝ) ^ q * (1 + B ^ q * (q.factorial : ℝ) * T ^ (q - 2)) ≤
      32 * B ^ 2 * (((q - 1).factorial : ℝ) * (4 * B * T) ^ (q - 2)) := by
    calc
      _ ≤ 2 * 2 ^ q * (B ^ q * (q.factorial : ℝ) * T ^ (q - 2)) := by
        have h := mul_le_mul_of_nonneg_left herror (by positivity : 0 ≤ (2 : ℝ) ^ q)
        nlinarith
      _ = 2 * 2 ^ q * B ^ q * (q : ℝ) * ((q - 1).factorial : ℝ) * T ^ (q - 2) := by
        rw [hfac]
        ring
      _ ≤ 2 * 2 ^ q * B ^ q * 2 ^ q * ((q - 1).factorial : ℝ) * T ^ (q - 2) := by
        gcongr
      _ = _ := by
        have htwo : (2 : ℝ) ^ q = 2 ^ (q - 2) * 4 := by
          conv_lhs => rw [show q = (q - 2) + 2 by omega, pow_add]
          norm_num
        have hBpow : B ^ q = B ^ (q - 2) * B ^ 2 := by
          conv_lhs => rw [show q = (q - 2) + 2 by omega, pow_add]
        have hfour : (4 : ℝ) ^ (q - 2) = 2 ^ (q - 2) * 2 ^ (q - 2) := by
          rw [← mul_pow]
          norm_num
        rw [htwo, hBpow]
        simp only [mul_pow, hfour]
        ring
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ q)).2
  have h := mul_le_mul_of_nonneg_left hθ' (by positivity : 0 ≤ 32 * B ^ 2)
  nlinarith

/-- Equation (2.16), with constants chosen uniformly before the penalty,
thresholds, moment order and ambient cutoff. -/
theorem truncatedMoment_threshold_recursion : ∃ Cmin ≥ (1 : ℝ), ∃ C > 0, ∀ C₀ : ℝ, Cmin ≤ C₀ →
    ∀ δ T (θ : ℕ → ℝ) (q : ℕ), 0 ≤ δ → 1 ≤ T →
    AdmissibleThresholds C₀ T θ → 3 ≤ q → ∀ x : ℝ, 2 ≤ x →
    truncatedMoment δ T θ q x ≤ C * (θ (q - 1) / 2 ^ q +
      ∫ y in 1..x ^ 2, recursionMainKernel δ T θ q y) := by
  obtain ⟨A, hA, B, hB, hrec⟩ := truncatedMoment_factorial_recursion
  let D := max B 1
  have hD : 1 ≤ D := le_max_right _ _
  have hD0 : 0 < D := by linarith
  let Cmin := 4 * D
  have hCmin : 1 ≤ Cmin := by dsimp only [Cmin]; linarith
  refine ⟨Cmin, hCmin, A * (32 * D ^ 2), by positivity,
    fun C₀ hC₀ δ T θ q hδ hT hθ hq x hx ↦ ?_⟩
  have hx2 : 1 ≤ x ^ 2 := by nlinarith
  have hI : 0 ≤ ∫ y in 1..x ^ 2, recursionMainKernel δ T θ q y :=
    intervalIntegral.integral_nonneg hx2 (fun y hy ↦ recursionMainKernel_nonneg δ T θ q hy.1)
  have he := hθ.2.2.2.2.1 (q - 1) (by omega)
  have hsub : q - 1 - 1 = q - 2 := by omega
  rw [hsub] at he
  have herror := factorial_error_le_threshold hD hC₀ hT hq he
  have hpow : B ^ q ≤ D ^ q := pow_le_pow_left₀ hB.le (le_max_left _ _) q
  have hcoef : 1 ≤ 32 * D ^ 2 := by nlinarith [sq_nonneg (D - 1)]
  have hBerror : B ^ q * (q.factorial : ℝ) * T ^ (q - 2) ≤
      D ^ q * (q.factorial : ℝ) * T ^ (q - 2) := by
    have hT0 : 0 ≤ T := by linarith
    gcongr
  have h := hrec δ T θ q hδ hT (by omega) x hx
  have hbound : 1 + B ^ q * (q.factorial : ℝ) * T ^ (q - 2) +
      (∫ y in 1..x ^ 2, recursionMainKernel δ T θ q y) ≤
      (32 * D ^ 2) * (θ (q - 1) / 2 ^ q +
        ∫ y in 1..x ^ 2, recursionMainKernel δ T θ q y) := by
    have hI' := mul_le_mul_of_nonneg_right hcoef hI
    rw [mul_div_assoc] at herror
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hbound hA.le
  nlinarith

end BretecheTenenbaumMean
