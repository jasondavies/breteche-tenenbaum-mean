module

public import BretecheTenenbaumMean.TwoFrequencyWeight
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! # Dyadic decomposition of the good-set divisor bound

The exact envelope uses `log (3*y)`, as in the definition of the good set.
No rounding of a real logarithm to a prime-count index is left implicit.
-/

namespace BretecheTenenbaumMean

open Real Finset

noncomputable def goodEnvelope (δ T y : ℝ) : ℝ :=
  T * log (3 * y) * exp (-penalty δ T y)

theorem goodEnvelope_pos {δ T y : ℝ} (hT : 0 < T) (hy : 1 ≤ y) :
    0 < goodEnvelope δ T y := by
  unfold goodEnvelope
  exact mul_pos (mul_pos hT (log_pos (by linarith))) (exp_pos _)

/-- The lower endpoint is open and the upper endpoint closed. -/
def dyadicGoodSet (δ T y : ℝ) (j : ℕ) : Set ℕ :=
  {n | n ∈ goodSet δ T ∧
    goodEnvelope δ T y / (2 : ℝ) ^ (j + 1) < tau (smallPrimePart n y) ∧
    tau (smallPrimePart n y) ≤ goodEnvelope δ T y / (2 : ℝ) ^ j}

/-- Every good integer belongs to a dyadic layer. -/
theorem exists_mem_dyadicGoodSet {δ T y : ℝ} {n : ℕ} (hy : 1 ≤ y)
    (hn : n ∈ goodSet δ T) : ∃ j, n ∈ dyadicGoodSet δ T y j := by
  have hτ := tau_pos (smallPrimePart_ne_zero n y)
  have hbound : tau (smallPrimePart n y) ≤ goodEnvelope δ T y := hn.2 y hy
  obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near ((one_le_div hτ).2 hbound)
    (by norm_num : (1 : ℝ) < 2)
  refine ⟨j, hn, ?_, ?_⟩
  · apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ (j + 1))).2
    have h := (div_lt_iff₀ hτ).1 hj'
    nlinarith
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ j)).2
    have h := (le_div_iff₀ hτ).1 hj
    nlinarith

/-- The dyadic layers are disjoint, including at powers of two. -/
theorem dyadicGoodSet_index_unique {δ T y : ℝ} {n j k : ℕ}
    (hj : n ∈ dyadicGoodSet δ T y j) (hk : n ∈ dyadicGoodSet δ T y k) : j = k := by
  have hτ := tau_pos (smallPrimePart_ne_zero n y)
  have hB : 0 < goodEnvelope δ T y :=
    (mul_pos hτ (by positivity : (0 : ℝ) < 2 ^ j)).trans_le
      ((le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ j)).1 hj.2.2)
  have hnot : ∀ {i l : ℕ}, n ∈ dyadicGoodSet δ T y i →
      n ∈ dyadicGoodSet δ T y l → ¬ i < l := by
    intro i l hi hl hil
    have hp : (2 : ℝ) ^ (i + 1) ≤ 2 ^ l :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hdiv := div_le_div_of_nonneg_left hB.le (by positivity) hp
    exact (not_lt_of_ge (hl.2.2.trans hdiv)) hi.2.1
  exact le_antisymm (le_of_not_gt (hnot hk hj)) (le_of_not_gt (hnot hj hk))

/-- A factor-two half-open band contains at most one nonnegative power of two. -/
theorem pow_two_band_unique {B : ℝ} {j r s : ℕ}
    (hr : B / (2 : ℝ) ^ (j + 1) < 2 ^ r ∧ 2 ^ r ≤ B / (2 : ℝ) ^ j)
    (hs : B / (2 : ℝ) ^ (j + 1) < 2 ^ s ∧ 2 ^ s ≤ B / (2 : ℝ) ^ j) : r = s := by
  have hnot : ∀ {u v : ℕ},
      B / (2 : ℝ) ^ (j + 1) < 2 ^ u → 2 ^ v ≤ B / (2 : ℝ) ^ j → ¬ u < v := by
    intro u v hu hv huv
    have hp : (2 : ℝ) ^ (u + 1) ≤ 2 ^ v :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h1 := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ (j + 1))).1 hu
    have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ j)).1 hv
    rw [pow_succ] at h1 hp
    nlinarith [mul_le_mul_of_nonneg_right hp (by positivity : (0 : ℝ) ≤ 2 ^ j)]
  exact le_antisymm (le_of_not_gt (hnot hs.1 hr.2)) (le_of_not_gt (hnot hr.1 hs.2))

/-- All integers in one layer have exactly the same small-prime count. -/
theorem dyadicGoodSet_prime_count_eq {δ T y : ℝ} {m n j : ℕ}
    (hm : m ∈ dyadicGoodSet δ T y j) (hn : n ∈ dyadicGoodSet δ T y j) :
    (smallPrimePart m y).primeFactors.card = (smallPrimePart n y).primeFactors.card := by
  apply pow_two_band_unique (B := goodEnvelope δ T y) (j := j)
  · simpa only [tau_squarefree (hm.1.1.squarefree_of_dvd (smallPrimePart_dvd m y))] using hm.2
  · simpa only [tau_squarefree (hn.1.1.squarefree_of_dvd (smallPrimePart_dvd n y))] using hn.2

/-- An index exists even for an empty layer, avoiding any truncated logarithm convention. -/
theorem dyadicGoodSet_fixed_prime_count (δ T y : ℝ) (j : ℕ) :
    ∃ r : ℕ, ∀ n ∈ dyadicGoodSet δ T y j, (smallPrimePart n y).primeFactors.card = r := by
  by_cases h : (dyadicGoodSet δ T y j).Nonempty
  · obtain ⟨m, hm⟩ := h
    exact ⟨_, fun n hn ↦ dyadicGoodSet_prime_count_eq hn hm⟩
  · exact ⟨0, fun n hn ↦ (h ⟨n, hn⟩).elim⟩

/-- The two good-set constraints extract the geometric saving of a dyadic layer. -/
theorem dyadicGoodSet_sqrt_tau_le {δ T a b : ℝ} {n j : ℕ}
    (hT : 0 < T) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hn : n ∈ dyadicGoodSet δ T a j) :
    sqrt (tau (smallPrimePart n a) * tau (smallPrimePart n b)) ≤
      sqrt (goodEnvelope δ T a * goodEnvelope δ T b) / sqrt ((2 : ℝ) ^ j) := by
  have hBa := goodEnvelope_pos (δ := δ) hT ha
  have hprod := mul_le_mul hn.2.2 (hn.1.2 b hb)
    (tau_pos (smallPrimePart_ne_zero n b)).le (div_nonneg hBa.le (by positivity))
  have he : goodEnvelope δ T a / (2 : ℝ) ^ j * goodEnvelope δ T b =
      (goodEnvelope δ T a * goodEnvelope δ T b) / (2 : ℝ) ^ j := by ring
  change tau (smallPrimePart n a) * tau (smallPrimePart n b) ≤
    goodEnvelope δ T a / (2 : ℝ) ^ j * goodEnvelope δ T b at hprod
  rw [he] at hprod
  simpa only [sqrt_div (mul_nonneg hBa.le (goodEnvelope_pos (δ := δ) hT hb).le)] using sqrt_le_sqrt hprod

/-- The unweighted two-frequency product is recovered from its multiplicative weight. -/
theorem normalizedPolynomial_mul_eq_twoFrequencyWeight (n : ℕ) (a b θ φ : ℝ) :
    normalizedPolynomial n θ * normalizedPolynomial n φ =
      sqrt (tau (smallPrimePart n a) * tau (smallPrimePart n b)) *
        twoFrequencyWeight n a b θ φ := by
  have hs : 0 < sqrt (tau (smallPrimePart n a) * tau (smallPrimePart n b)) :=
    sqrt_pos.2 (mul_pos (tau_pos (smallPrimePart_ne_zero n a))
      (tau_pos (smallPrimePart_ne_zero n b)))
  unfold twoFrequencyWeight
  field_simp

/-- Only finitely many layers can be nonempty at a fixed cutoff. -/
theorem exists_dyadicGoodSet_cutoff (δ T y : ℝ) : ∃ N : ℕ,
    ∀ n j, n ∈ dyadicGoodSet δ T y j → j < N := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (goodEnvelope δ T y) (by norm_num : (1 : ℝ) < 2)
  refine ⟨N, fun n j hn ↦ ?_⟩
  have hτ : 1 ≤ tau (smallPrimePart n y) := by
    rw [tau_squarefree (hn.1.1.squarefree_of_dvd (smallPrimePart_dvd n y))]
    exact one_le_pow₀ (by norm_num)
  have hB : (2 : ℝ) ^ j ≤ goodEnvelope δ T y := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ j)).1 hn.2.2
    nlinarith [mul_le_mul_of_nonneg_right hτ (by positivity : (0 : ℝ) ≤ 2 ^ j)]
  by_contra hj
  have hp : (2 : ℝ) ^ N ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

/-- Exact finite partition, valid for any test function. -/
theorem goodSet_indicator_eq_dyadic_sum {δ T y : ℝ} (hy : 1 ≤ y) {N : ℕ}
    (hN : ∀ n j, n ∈ dyadicGoodSet δ T y j → j < N) (f : ℕ → ℝ) (n : ℕ) :
    (goodSet δ T).indicator f n =
      ∑ j ∈ range N, (dyadicGoodSet δ T y j).indicator f n := by
  classical
  by_cases hn : n ∈ goodSet δ T
  · obtain ⟨j, hj⟩ := exists_mem_dyadicGoodSet hy hn
    rw [Set.indicator_of_mem hn]
    symm
    calc _ = (dyadicGoodSet δ T y j).indicator f n := by
          apply sum_eq_single j
          · intro k _ hkj
            apply Set.indicator_of_notMem
            intro hk
            exact hkj (dyadicGoodSet_index_unique hk hj)
          · intro hjN
            exact (hjN (mem_range.2 (hN n j hj))).elim
      _ = f n := Set.indicator_of_mem hj f
  · rw [Set.indicator_of_notMem hn]
    symm
    apply sum_eq_zero
    intro j _
    exact Set.indicator_of_notMem (fun hj ↦ hn hj.1) f

/-- The geometric square-root saving is summable, with an explicit universal bound. -/
theorem sum_inv_sqrt_two_pow_le (N : ℕ) :
    (∑ j ∈ range N, (sqrt ((2 : ℝ) ^ j))⁻¹) ≤ 4 := by
  have hs : 0 < sqrt (2 : ℝ) := sqrt_pos.2 (by norm_num)
  have hr : (sqrt (2 : ℝ))⁻¹ ≤ 3 / 4 := by
    rw [inv_eq_one_div, div_le_iff₀ hs]
    have := sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith
  calc _ ≤ ∑ j ∈ range N, (3 / 4 : ℝ) ^ j := by
        apply sum_le_sum
        intro j hj
        clear hj
        have he : sqrt ((2 : ℝ) ^ j) = (sqrt 2) ^ j := by
          induction j with
          | zero => simp
          | succ j ih => rw [pow_succ, sqrt_mul (by positivity), ih, pow_succ]
        rw [he, ← inv_pow]
        exact pow_le_pow_left₀ (inv_nonneg.2 hs.le) hr j
    _ ≤ ∑' j : ℕ, (3 / 4 : ℝ) ^ j :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).sum_le_tsum _
        (fun _ _ ↦ by positivity)
    _ = 4 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num

end BretecheTenenbaumMean
