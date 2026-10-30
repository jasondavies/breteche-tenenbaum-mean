module

public import BretecheTenenbaumMean.PrimeLayerAsymptotic
public import BretecheTenenbaumMean.PoissonLower

@[expose] public section

/-! # Prime-count probabilities in the central window of Lemma 3.1 -/

namespace BretecheTenenbaumMean

open Real

/-- The tilted central window is centered at twice the logarithmic mean. -/
theorem tilted_factorial_central {L B : ℝ} (hL : 0 < L) {k : ℕ}
    (hk : k ≠ 0) (hkhi : (k : ℝ) ≤ 4 * L)
    (hgap : ((k : ℝ) - 2 * L) ^ 2 ≤ B * L) :
    (1 / (2 * Stirling.stirlingSeq 1 * exp (B / 2))) *
        (exp (L - k * log 2) / sqrt (2 * L)) ≤
      L ^ k / (exp L * (k.factorial : ℝ)) ∧
    L ^ k / (exp L * (k.factorial : ℝ)) ≤
      8 * (exp (L - k * log 2) / sqrt (2 * L)) := by
  have h := factorial_term_central (u := 2 * L) (B := B / 2) (by positivity) hk
    (by linarith) (by nlinarith)
  have hd : 0 < (2 : ℝ) ^ k * exp L := by positivity
  have hid : (exp (2 * L) / sqrt (2 * L)) / ((2 : ℝ) ^ k * exp L) =
      exp (L - k * log 2) / sqrt (2 * L) := by
    rw [exp_sub, exp_nat_mul, exp_log (by norm_num : (0 : ℝ) < 2),
      show (2 : ℝ) * L = L + L by ring, exp_add]
    field_simp
  have hterm : ((2 * L) ^ k / (k.factorial : ℝ)) / ((2 : ℝ) ^ k * exp L) =
      L ^ k / (exp L * (k.factorial : ℝ)) := by
    rw [mul_pow]
    field_simp
  constructor
  · have hh := div_le_div_of_nonneg_right h.1 hd.le
    rw [hterm, mul_div_assoc, hid] at hh
    exact hh
  · have hh := div_le_div_of_nonneg_right h.2 hd.le
    rw [hterm, mul_div_assoc, hid] at hh
    exact hh

/-- Uniform two-sided bounds for prime-count layers in any fixed Gaussian
window about twice the logarithmic mean. -/
theorem probability_prime_layer_central {B : ℝ} (hB : 0 ≤ B) :
    ∃ c > 0, ∃ C > 0, ∃ L₀ > 0, ∀ y : ℝ, 2 ≤ y → L₀ ≤ log (log y) →
    ∀ k : ℕ, ((k : ℝ) - 2 * log (log y)) ^ 2 ≤ B * log (log y) →
      c * (exp (log (log y) - k * log 2) / sqrt (2 * log (log y))) ≤
        probability y {n | n.primeFactors.card = k} ∧
      probability y {n | n.primeFactors.card = k} ≤
        C * (exp (log (log y) - k * log 2) / sqrt (2 * log (log y))) := by
  obtain ⟨c, hc, C, hC, L₁, hL₁, hprob⟩ := probability_prime_layer_bounds
    (show (0 : ℝ) < 4 by norm_num)
  let d := 1 / (2 * Stirling.stirlingSeq 1 * exp (B / 2))
  have hd : 0 < d := by
    have : 0 < Stirling.stirlingSeq 1 := Stirling.stirlingSeq'_pos 0
    dsimp [d]
    positivity
  refine ⟨c * d, by positivity, C * 8, by positivity, max L₁ (B + 1),
    lt_of_lt_of_le hL₁ (le_max_left _ _), fun y hy hL k hgap ↦ ?_⟩
  let L := log (log y)
  have hLL : L₁ ≤ L := (le_max_left _ _).trans hL
  have hBL : B + 1 ≤ L := (le_max_right _ _).trans hL
  have hLpos : 0 < L := hL₁.trans_le hLL
  have hgap' : ((k : ℝ) - 2 * L) ^ 2 ≤ L ^ 2 := by
    exact hgap.trans (by nlinarith)
  have hklo : L ≤ (k : ℝ) := by nlinarith [sq_nonneg ((k : ℝ) - L)]
  have hkhi : (k : ℝ) ≤ 4 * L := by nlinarith [sq_nonneg ((k : ℝ) - 3 * L)]
  have hk : k ≠ 0 := by intro hk; subst k; norm_num at hklo; linarith
  have hp := hprob y hy hLL k hkhi
  have ht := tilted_factorial_central hLpos hk hkhi hgap
  have hexp : exp L = log y := exp_log (log_pos (by linarith))
  rw [hexp] at ht
  constructor
  · calc
      _ = c * (d * (exp (L - k * log 2) / sqrt (2 * L))) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left ht.1 hc.le).trans hp.1
  · calc
      _ ≤ C * (8 * (exp (L - k * log 2) / sqrt (2 * L))) :=
        hp.2.trans (mul_le_mul_of_nonneg_left ht.2 hC.le)
      _ = _ := by ring

end BretecheTenenbaumMean
