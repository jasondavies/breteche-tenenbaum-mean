module

public import BretecheTenenbaumMean.JointPrimeLayers
public import BretecheTenenbaumMean.PowerComparison
public import BretecheTenenbaumMean.PrimeSums.Product

@[expose] public section

/-! # Exponential decay between separated dyadic prime-count events -/

namespace BretecheTenenbaumMean

open Finset Real

/-- The geometric overlap ratio in §3; its negative logarithm is the paper's
positive exponent `β`. -/
noncomputable def primeGapRatio : ℝ := exp 1 * log 2 / 2

theorem primeGapRatio_pos : 0 < primeGapRatio := by
  unfold primeGapRatio
  exact div_pos (mul_pos (exp_pos _) (log_pos (by norm_num))) (by norm_num)

theorem primeGapRatio_lt_one : primeGapRatio < 1 := by
  have he : exp 1 < (11 : ℝ) / 4 := by linarith [exp_one_lt_d9]
  have hl : log 2 < (7 : ℝ) / 10 := by linarith [log_two_lt_d9]
  have hp : 0 < log (2 : ℝ) := log_pos (by norm_num)
  unfold primeGapRatio
  nlinarith [mul_lt_mul_of_pos_right he hp]

/-- The factorial coefficient and Euler-product normalization for the prime
block between `exp(2^h)` and `exp(2^(h+l))` decay geometrically in `l`. -/
theorem dyadic_prime_gap_bound : ∃ C > 0, ∀ h l : ℕ, 0 < l →
    ((∑ p ∈ primesLT (exp ((2 : ℝ) ^ (h + l))) \
        primesLT (exp ((2 : ℝ) ^ h)), (p : ℝ)⁻¹) ^ l / (l.factorial : ℝ)) *
      (normalizer (exp ((2 : ℝ) ^ h)) /
        normalizer (exp ((2 : ℝ) ^ (h + l)))) ≤ C * primeGapRatio ^ l := by
  obtain ⟨K, hK, herr⟩ := PrimeSums.abs_SLT_sub_loglog_le
  obtain ⟨a, b, ha, hb, hnorm⟩ := PrimeSums.normalizer_ratio_bounds
  let D := exp ((1 / log 2) * (2 * K))
  have hD : 0 < D := exp_pos _
  refine ⟨b * D, by positivity, fun h l hl ↦ ?_⟩
  let y := exp ((2 : ℝ) ^ h)
  let z := exp ((2 : ℝ) ^ (h + l))
  let S := ∑ p ∈ primesLT z \ primesLT y, (p : ℝ)⁻¹
  have hy : 2 ≤ y := exp_one_gt_two.le.trans
    (exp_le_exp.2 (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
  have hz : 2 ≤ z := exp_one_gt_two.le.trans
    (exp_le_exp.2 (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
  have hyz : y ≤ z := by
    apply exp_le_exp.2
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_add_right h l)
  have hl0 : 0 < (l : ℝ) := by exact_mod_cast hl
  have hlog : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hS0 : 0 ≤ S := sum_nonneg (fun _ _ ↦ by positivity)
  have hS : S ≤ (l : ℝ) * log 2 + 2 * K := by
    have he : S = PrimeSums.SLT z - PrimeSums.SLT y := by
      dsimp [S, PrimeSums.SLT]
      rw [← sum_sdiff (PrimeSums.primesLT_mono hyz), add_sub_cancel_right]
    rw [he]
    have h1 := (abs_le.1 (herr z hz)).2
    have h2 := (abs_le.1 (herr y hy)).1
    simp only [y, z, log_exp, log_pow, Nat.cast_add] at h1 h2
    linarith
  have hpow : S ^ l ≤ D * ((l : ℝ) * log 2) ^ l := by
    calc
      _ ≤ ((l : ℝ) * log 2 + 2 * K) ^ l := pow_le_pow_left₀ hS0 hS _
      _ ≤ _ := pow_le_exp_mul_pow_of_sub_le (by positivity) (by positivity)
        (by positivity : 0 ≤ 2 * K) (by linarith)
        (by field_simp; rfl)
  have hfac : ((l : ℝ) * log 2) ^ l / (l.factorial : ℝ) ≤
      (exp 1 * log 2) ^ l := by
    have he := pow_div_factorial_le_exp (l : ℝ) (Nat.cast_nonneg l) l
    calc
      _ = log 2 ^ l * ((l : ℝ) ^ l / (l.factorial : ℝ)) := by rw [mul_pow]; ring
      _ ≤ log 2 ^ l * exp (l : ℝ) := mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by
        rw [show exp (l : ℝ) = (exp 1) ^ l by
          simpa only [mul_one] using exp_nat_mul (1 : ℝ) l, ← mul_pow]
        rw [mul_comm]
  have hratio : normalizer y / normalizer z ≤ b / (2 : ℝ) ^ l := by
    have he := (hnorm z y hz hy).2
    have hid : log y / log z = 1 / (2 : ℝ) ^ l := by
      simp only [y, z, log_exp, pow_add]
      field_simp
    rw [hid] at he
    simpa only [mul_one_div] using he
  change (S ^ l / (l.factorial : ℝ)) * (normalizer y / normalizer z) ≤ _
  calc
    _ ≤ (D * ((exp 1 * log 2) ^ l)) * (b / (2 : ℝ) ^ l) := by
      apply mul_le_mul _ hratio (by positivity [normalizer_pos y, normalizer_pos z])
        (by positivity)
      calc
        _ ≤ (D * ((l : ℝ) * log 2) ^ l) / (l.factorial : ℝ) :=
          div_le_div_of_nonneg_right hpow (by positivity)
        _ = D * (((l : ℝ) * log 2) ^ l / (l.factorial : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hfac hD.le
    _ = _ := by rw [primeGapRatio, div_pow]; ring

/-- Joint dyadic-layer probabilities are a first marginal times a geometrically
small factor, uniformly in the marginal index and ambient cutoff. -/
theorem probability_dyadic_joint_decay : ∃ C > 0, ∀ x : ℝ, ∀ h l r : ℕ,
    0 < l → exp ((2 : ℝ) ^ (h + l)) ≤ x →
    probability x {n | (smallPrimePart n (exp ((2 : ℝ) ^ h))).primeFactors.card = r ∧
      (smallPrimePart n (exp ((2 : ℝ) ^ (h + l)))).primeFactors.card = r + l} ≤
    C * primeGapRatio ^ l * probability (exp ((2 : ℝ) ^ h))
      {n | n.primeFactors.card = r} := by
  obtain ⟨C, hC, hgap⟩ := dyadic_prime_gap_bound
  refine ⟨C, hC, fun x h l r hl hx ↦ ?_⟩
  have hyz : exp ((2 : ℝ) ^ h) ≤ exp ((2 : ℝ) ^ (h + l)) := by
    apply exp_le_exp.2
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_add_right h l)
  calc
    _ ≤ _ := probability_joint_prime_layers_le hyz hx r l
    _ ≤ probability (exp ((2 : ℝ) ^ h)) {n | n.primeFactors.card = r} *
        (C * primeGapRatio ^ l) :=
      mul_le_mul_of_nonneg_left (hgap h l hl) (probability_nonneg _ _)
    _ = _ := by ring

end BretecheTenenbaumMean
