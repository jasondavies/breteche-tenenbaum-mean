module

public import BretecheTenenbaumMean.GoodSetGrid
public import BretecheTenenbaumMean.PrimeCountTail
public import BretecheTenenbaumMean.PrimeSums.Product

@[expose] public section

/-! # Mertens estimates on the logarithmic grid -/

namespace BretecheTenenbaumMean

open Real Finset PrimeSums

/-- Every grid cutoff used for exceptional events includes the prime two. -/
theorem two_lt_goodSetGrid {j : ℕ} (hj : 1 ≤ j) : 2 < goodSetGrid j := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have he : 2 < exp (j : ℝ) := exp_one_gt_two.trans_le (exp_le_exp.2 hj')
  have h6 : 6 < exp (2 : ℝ) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
    nlinarith [exp_one_gt_d9]
  have h := h6.trans (exp_lt_exp.2 he)
  unfold goodSetGrid
  linarith

/-- Replacing `log log y` by the integer grid coordinate costs a bounded error. -/
theorem loglog_grid_bounds {j : ℕ} (hj : 1 ≤ j) :
    (j : ℝ) - log 2 ≤ log (log (goodSetGrid j)) ∧ log (log (goodSetGrid j)) ≤ j := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h3 : 0 < log 3 := log_pos (by norm_num)
  have he : exp 1 ≤ exp (j : ℝ) := exp_le_exp.2 hj'
  have hhalf : exp (j : ℝ) / 2 ≤ exp (j : ℝ) - log 3 := by
    linarith [exp_one_gt_d9, log_three_lt_d9]
  have hpos : 0 < exp (j : ℝ) / 2 := by positivity
  have hupper : exp (j : ℝ) - log 3 ≤ exp (j : ℝ) := by linarith
  have hlog : log (goodSetGrid j) = exp (j : ℝ) - log 3 := by
    rw [goodSetGrid, log_div (exp_ne_zero _) (by norm_num : (3 : ℝ) ≠ 0), log_exp]
  rw [hlog]
  constructor
  · have h := log_le_log hpos hhalf
    simpa only [log_div (exp_ne_zero _) (by norm_num : (2 : ℝ) ≠ 0), log_exp] using h
  · simpa only [log_exp] using log_le_log (hpos.trans_le hhalf) hupper

/-- The mean parameter in the factorial tail differs from the grid index by
an absolute constant. -/
theorem abs_SLT_grid_sub_index_le : ∃ K ≥ 0, ∀ j : ℕ, 1 ≤ j →
    |SLT (goodSetGrid j) - j| ≤ K := by
  obtain ⟨K, hK0, hK⟩ := abs_SLT_sub_loglog_le
  refine ⟨K + log 2, by have := log_pos (by norm_num : (1 : ℝ) < 2); linarith,
    fun j hj ↦ ?_⟩
  have h := hK (goodSetGrid j) (two_lt_goodSetGrid hj).le
  have hlog := loglog_grid_bounds hj
  have hdiff : |log (log (goodSetGrid j)) - j| ≤ log 2 := by
    rw [abs_le]
    constructor <;> linarith [log_pos (by norm_num : (1 : ℝ) < 2)]
  calc _ ≤ |SLT (goodSetGrid j) - log (log (goodSetGrid j))| +
      |log (log (goodSetGrid j)) - j| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add h hdiff

/-- Positivity is explicit, so the rate-function quotient at grid points is defined. -/
theorem SLT_grid_pos {j : ℕ} (hj : 1 ≤ j) : 0 < SLT (goodSetGrid j) := by
  have hp : 2 ∈ primesLT (goodSetGrid j) := mem_primesLT.2 ⟨Nat.prime_two, two_lt_goodSetGrid hj⟩
  have h := single_le_sum (fun p (_ : p ∈ primesLT (goodSetGrid j)) ↦
    (inv_nonneg.2 (Nat.cast_nonneg p) : 0 ≤ (p : ℝ)⁻¹)) hp
  change (2 : ℝ)⁻¹ ≤ SLT (goodSetGrid j) at h
  norm_num at h
  linarith

/-- The Euler normalizer cancels the leading Poisson exponential, leaving the
probabilistic rate function with only an absolute factor `exp 1`. -/
theorem probability_prime_ge_exp_rate (x : ℝ) {ρ : ℝ} {k : ℕ}
    (hu : 0 < SLT x) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hk0 : k ≠ 0)
    (hk : SLT x ≤ ρ * (k + 1)) :
    probability x {n | k ≤ n.primeFactors.card} ≤
      exp (1 - SLT x * poissonRate (k / SLT x)) / ((1 - ρ) * sqrt (2 * π * k)) := by
  have hnorm := abs_le.1 (abs_log_normalizer_sub_SLT_le x)
  have he : exp (SLT x * (1 - poissonRate (k / SLT x))) / normalizer x ≤
      exp (1 - SLT x * poissonRate (k / SLT x)) := by
    rw [← exp_log (normalizer_pos x), ← exp_sub]
    apply exp_le_exp.2
    linarith [hnorm.1]
  have hd : 0 ≤ (1 - ρ) * sqrt (2 * π * k) := by positivity
  have h := div_le_div_of_nonneg_right he hd
  refine (probability_prime_ge_le_rate x hu hρ hρ1 hk0 hk).trans ?_
  convert h using 1
  rw [div_div]
  congr 1
  ring

end BretecheTenenbaumMean
