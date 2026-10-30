module

public import BretecheTenenbaumMean.OmegaWeight

@[expose] public section

/-! # Retaining a fixed fraction of the weighted Euler product below the cutoff -/

namespace BretecheTenenbaumMean

open Finset Real

lemma omegaThree_prime_log_bound : ∃ D > 0, ∀ y : ℝ, 2 ≤ y →
    (∑ p ∈ primesLT y, (3 / (p + 3 : ℝ)) * log p) ≤ D * log y := by
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hl4 : 0 < log (4 : ℝ) := log_pos (by norm_num)
  refine ⟨3 * log 4 * (1 + (log 2)⁻¹), by positivity, fun y hy ↦ ?_⟩
  have hsub : primesLT y ⊆ (Icc 0 ⌊y⌋₊).filter Nat.Prime := by
    intro p hp
    obtain ⟨hp, hpy⟩ := mem_primesLT.1 hp
    exact mem_filter.2 ⟨mem_Icc.2 ⟨Nat.zero_le _, Nat.le_floor hpy.le⟩, hp⟩
  have hlog : log 2 ≤ log y := log_le_log (by norm_num) hy
  have hone : 1 ≤ (log 2)⁻¹ * log y := by
    have h := mul_le_mul_of_nonneg_left hlog (inv_nonneg.2 hl2.le)
    rwa [inv_mul_cancel₀ hl2.ne'] at h
  calc
    _ ≤ 3 * ∑ p ∈ primesLT y, log p / p := by
      rw [mul_sum]
      apply sum_le_sum
      intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_primesLT.1 hp).1.pos
      have hlp : 0 ≤ log p := log_nonneg (by exact_mod_cast (mem_primesLT.1 hp).1.one_le)
      have h := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 3 by norm_num) hp0 (by linarith : (p : ℝ) ≤ p + 3)) hlp
      convert h using 1; ring
    _ ≤ 3 * NairTenenbaum.primeLogSum y := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      have hpp := (mem_filter.1 hp).2
      exact div_nonneg (log_nonneg (by exact_mod_cast hpp.one_le)) (Nat.cast_nonneg _)
    _ ≤ 3 * (log 4 * (1 + log y)) := mul_le_mul_of_nonneg_left (NairTenenbaum.primeLogSum_le hy) (by norm_num)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hone (show 0 ≤ 3 * log 4 from by positivity)]

/-- A logarithmic first moment controls the mass above any cutoff. -/
lemma omegaThree_log_tail (y R : ℝ) (hR : 0 < R) :
    log R * (omegaThreeProduct y -
      ∑ n ∈ smoothSupport y, if (n : ℝ) ≤ R then omegaThree n / n else 0) ≤
      omegaThreeProduct y * ∑ p ∈ primesLT y, (3 / (p + 3 : ℝ)) * log p := by
  classical
  rw [← omegaThreeProduct_log_moment, omegaThreeProduct, ← sum_sub_distrib, mul_sum]
  apply sum_le_sum
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_mem_divisors hn
  have hw : 0 ≤ omegaThree n / n := div_nonneg (omegaThree_nonneg _) (Nat.cast_nonneg _)
  split_ifs with h
  · simp only [sub_self, mul_zero]
    exact mul_nonneg hw (log_nonneg hn1)
  · simp only [sub_zero]
    exact (mul_le_mul_of_nonneg_right (log_le_log hR (le_of_not_ge h)) hw).trans_eq (mul_comm _ _)

/-- A sufficiently small fixed power of `R` supplies a logarithmically cubic
mass of integers below `R`. No asymptotic divisor-count theorem is assumed. -/
theorem omegaThree_harmonic_lower : ∃ c > 0, ∃ R₀ ≥ (2 : ℝ), ∀ R : ℝ, R₀ ≤ R →
    c * log R ^ 3 ≤ ∑ n ∈ Ioc 0 ⌊R⌋₊, omegaThree n / n := by
  classical
  obtain ⟨D, hD, hmoment⟩ := omegaThree_prime_log_bound
  obtain ⟨c, hc, hprod⟩ := PrimeSums.prod_one_add_nat_div_lower 3
  let K := 2 * D + 1
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hK0 : 0 < K := by linarith
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hR₀ : 2 ≤ exp (K * log 2) := by
    rw [← exp_log (show (0 : ℝ) < 2 by norm_num)]
    apply exp_le_exp.2
    rw [log_exp]
    nlinarith
  refine ⟨c / (2 * K ^ 3), by positivity, exp (K * log 2), hR₀, fun R hR ↦ ?_⟩
  have hR2 := hR₀.trans hR
  have hR0 : 0 < R := by linarith
  have hlR : 0 < log R := log_pos (by linarith)
  have hlogR : K * log 2 ≤ log R := by
    have h := log_le_log (exp_pos (K * log 2)) hR
    simpa only [log_exp] using h
  let y := exp (log R / K)
  have hy : 2 ≤ y := by
    calc
      _ = exp (log 2) := (exp_log (show (0 : ℝ) < 2 by norm_num)).symm
      _ ≤ _ := exp_le_exp.2 ((le_div_iff₀ hK0).2 (by nlinarith))
  have hly : log y = log R / K := log_exp _
  have hloc : (∑ p ∈ primesLT y, (3 / (p + 3 : ℝ)) * log p) ≤ log R / 2 := by
    apply (hmoment y hy).trans
    rw [hly]
    have hDK : 2 * D ≤ K := by dsimp [K]; linarith
    have h := mul_le_mul_of_nonneg_right hDK (div_nonneg hlR.le hK0.le)
    have he : K * (log R / K) = log R := by field_simp
    rw [he] at h
    linarith
  let T := ∑ n ∈ smoothSupport y, if (n : ℝ) ≤ R then omegaThree n / n else 0
  have hhalf : omegaThreeProduct y / 2 ≤ T := by
    have htail := (omegaThree_log_tail y R hR0).trans
      (mul_le_mul_of_nonneg_left hloc (omegaThreeProduct_pos y).le)
    change log R * (omegaThreeProduct y - T) ≤ omegaThreeProduct y * (log R / 2) at htail
    nlinarith
  have hT : T ≤ ∑ n ∈ Ioc 0 ⌊R⌋₊, omegaThree n / n := by
    dsimp [T]
    rw [← sum_filter]
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨hn, hnR⟩ := mem_filter.1 hn
      exact mem_Ioc.2 ⟨Nat.pos_of_mem_divisors hn, Nat.le_floor hnR⟩
    · intro n _ _
      exact div_nonneg (omegaThree_nonneg _) (Nat.cast_nonneg _)
  calc
    _ = (c * log y ^ 3) / 2 := by rw [hly]; field_simp
    _ ≤ omegaThreeProduct y / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      rw [omegaThreeProduct_eq]
      simpa only [Nat.cast_ofNat] using hprod y hy
    _ ≤ T := hhalf
    _ ≤ _ := hT

end BretecheTenenbaumMean
