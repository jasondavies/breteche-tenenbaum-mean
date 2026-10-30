module

public import BretecheTenenbaumMean.GridEntropy
public import BretecheTenenbaumMean.PrimeSums.Grid
public import BretecheTenenbaumMean.WeightedPrimeCountTail

@[expose] public section

/-! # Weighted Gaussian bounds for divisor tails on the grid -/

namespace BretecheTenenbaumMean.WeightedModel

open Real PrimeSums

/-- A weighted Mertens estimate gives the same bounded error on the grid. -/
theorem abs_primeSum_grid_sub_index_le (w : MultiplicativeWeight) {B : ℝ}
    (hB : 0 ≤ B) (hmean : ∀ x ≥ 2, |primeSum w x - log (log x)| ≤ B) :
    ∃ K ≥ 0, ∀ j : ℕ, 1 ≤ j → |primeSum w (goodSetGrid j) - j| ≤ K := by
  refine ⟨B + log 2, by have := log_pos (by norm_num : (1 : ℝ) < 2); linarith,
    fun j hj ↦ ?_⟩
  have h := hmean (goodSetGrid j) (two_lt_goodSetGrid hj).le
  have hlog := loglog_grid_bounds hj
  have hdiff : |log (log (goodSetGrid j)) - j| ≤ log 2 := by
    rw [abs_le]
    constructor <;> linarith [log_pos (by norm_num : (1 : ℝ) < 2)]
  exact (abs_sub_le _ _ _).trans (add_le_add h hdiff)

/-- The one-cutoff tails have a Gaussian majorant in the square-root grid
coordinate. The constants are independent of `δ,T` and the grid index. -/
theorem grid_divisor_tail_bound (w : MultiplicativeWeight) {A B : ℝ}
    (hw : ∀ p : ℕ, p.Prime → w p ≤ A) (hB : 0 ≤ B)
    (hmean : ∀ x ≥ 2, |primeSum w x - log (log x)| ≤ B) : ∃ C > 0, ∃ t₀ ≥ 100, ∀ δ T (j : ℕ),
    0 ≤ δ → δ ≤ 1 / 1000000 → 0 < T → t₀ ≤ log T →
    probability w (goodSetGrid (j + 1)) {n | gridDivisorThreshold δ T j ≤ tau n} ≤
      (C / T) * exp (-(δ / 9) * (sqrt (j + 1 : ℝ) - sqrt (criticalSlope * log T)) ^ 2) /
        sqrt (j + 1 : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := abs_primeSum_grid_sub_index_le w hB hmean
  let E := K + 7
  refine ⟨10 * exp (A ^ 2 + E + E ^ 2), by positivity, 100 * (K + 1), by nlinarith,
    fun δ T j hδ hδ1 hT ht ↦ ?_⟩
  let t := log T
  let r := (j : ℝ) + 1
  let u := primeSum w (goodSetGrid (j + 1))
  let f := δ * min (t + r) ((r - criticalSlope * t) ^ 2 / t)
  let k := ⌈(t + r - f - 7) / log 2⌉₊
  have ht100 : 100 ≤ t := by dsimp only [t]; nlinarith
  have ht0 : 0 < t := by linarith
  have hr : 0 < r := by dsimp only [r]; positivity
  have hu : |u - r| ≤ K := by
    simpa only [Nat.cast_add, Nat.cast_one] using hK (j + 1) (by omega)
  obtain ⟨hf0, hf100, hklo, hkhi, he⟩ := rounded_grid_threshold_bounds hδ hδ1 ht100 hr.le
  change 0 ≤ f at hf0
  change f ≤ (t + r) / 100 at hf100
  change (5 / 4 : ℝ) * (t + r) ≤ (k : ℝ) at hklo
  change (k : ℝ) ≤ 2 * (t + r) at hkhi
  change |(k : ℝ) * log 2 - (t + r - f)| ≤ 7 at he
  have hkpos : 0 < (k : ℝ) := by nlinarith
  have hk0 : k ≠ 0 := by exact_mod_cast hkpos.ne'
  have hkceil : ⌈log (gridDivisorThreshold δ T j) / log 2⌉₊ = k := by
    rw [log_gridDivisorThreshold hT]
    rfl
  by_cases hu0 : 0 < u
  swap
  · have hune : 0 ≤ u := Finset.sum_nonneg (fun p _ ↦ div_nonneg (w.nonneg p) (Nat.cast_nonneg _))
    have huz : primeSum w (goodSetGrid (j + 1)) = 0 := by change u = 0; linarith
    rw [probability_tau_ge_eq w _ (gridDivisorThreshold_pos hT j), hkceil,
      probability_prime_ge_eq_zero w _ huz hk0]
    positivity
  have hk : u ≤ (9 / 10 : ℝ) * (k + 1) := by
    have h := (abs_le.1 hu).2
    change 100 * (K + 1) ≤ t at ht
    nlinarith
  have hrate := grid_entropy_lower hδ hδ1 hK0 ht hr.le hu0 hu hklo hkhi he
  change t + f - E - E ^ 2 ≤ u * poissonRate (k / u) at hrate
  have hfgauss : (δ / 9) * (sqrt r - sqrt (criticalSlope * t)) ^ 2 ≤ f := by
    have h := mul_le_mul_of_nonneg_left (clipped_penalty_ge_sqrt_distance ht0 hr.le) hδ
    convert h using 1
    ring
  have hnum : exp (A ^ 2 - u * poissonRate (k / u)) ≤
      (exp (A ^ 2 + E + E ^ 2) / T) * exp (-(δ / 9) * (sqrt r - sqrt (criticalSlope * t)) ^ 2) := by
    calc _ ≤ exp (A ^ 2 + E + E ^ 2 - t - (δ / 9) * (sqrt r - sqrt (criticalSlope * t)) ^ 2) :=
        exp_le_exp.2 (by linarith)
      _ = _ := by rw [exp_sub, exp_sub, exp_log hT, neg_mul, exp_neg]; ring
  have hroot : sqrt r ≤ sqrt (2 * π * k) := by
    apply sqrt_le_sqrt
    have hpi : 1 ≤ 2 * π := by linarith [pi_gt_three]
    have h := mul_le_mul_of_nonneg_right hpi hkpos.le
    nlinarith
  have hden : sqrt r / 10 ≤ (1 - (9 / 10 : ℝ)) * sqrt (2 * π * k) := by linarith
  rw [probability_tau_ge_eq w _ (gridDivisorThreshold_pos hT j), hkceil]
  refine (probability_prime_ge_exp_rate w _ (fun p hp ↦ hw p (mem_primesLT.1 hp).1) hu0 (by norm_num) (by norm_num) hk0 hk).trans ?_
  have hdiv := div_le_div₀ (by positivity) hnum (by positivity : 0 < sqrt r / 10) hden
  convert hdiv using 1
  dsimp only [r, t]
  ring

end BretecheTenenbaumMean.WeightedModel
