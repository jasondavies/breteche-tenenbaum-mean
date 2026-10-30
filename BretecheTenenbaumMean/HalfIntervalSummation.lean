module

public import BretecheTenenbaumMean.PolynomialShortSum

@[expose] public section

/-! # Summing estimates on the upper half of an interval

A strong induction handles odd endpoints without rounding losses. A finite
initial segment is retained explicitly for estimates valid only eventually.
-/

namespace BretecheTenenbaumMean

open Finset

/-- A uniform upper-half estimate sums geometrically, with an explicit
initial-segment contribution. The majorant `L` can be fixed at the final cutoff. -/
theorem sum_le_of_half_interval_bound (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (N₀ N : ℕ) {A L : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hhalf : ∀ n : ℕ, N₀ ≤ n → n ≤ N →
      (∑ i ∈ Ioc (n / 2) n, f i) ≤ A * n * L) :
    (∑ i ∈ Icc 1 N, f i) ≤ (∑ i ∈ Icc 1 N₀, f i) + 2 * A * N * L := by
  have H : ∀ n : ℕ, n ≤ N →
      (∑ i ∈ Icc 1 n, f i) ≤ (∑ i ∈ Icc 1 N₀, f i) + 2 * A * n * L := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hnN
      by_cases hn₀ : n ≤ N₀
      · have hs : (∑ i ∈ Icc 1 n, f i) ≤ ∑ i ∈ Icc 1 N₀, f i :=
          sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hn₀) (fun i _ _ ↦ hf i)
        exact hs.trans (le_add_of_nonneg_right (by positivity))
      · have hnpos : 0 < n := by omega
        have hdn : n / 2 ≤ n := Nat.div_le_self _ _
        have hdlt : n / 2 < n := Nat.div_lt_self hnpos (by norm_num)
        have he : Icc 1 n = Icc 1 (n / 2) ∪ Ioc (n / 2) n := by
          ext i
          simp only [mem_Icc, mem_union, mem_Ioc]
          omega
        have hdis : Disjoint (Icc 1 (n / 2)) (Ioc (n / 2) n) := by
          apply disjoint_left.2
          intro i hi hj
          have := (mem_Icc.1 hi).2
          have := (mem_Ioc.1 hj).1
          omega
        rw [he, sum_union hdis]
        have hsmall := ih (n / 2) hdlt (hdn.trans hnN)
        have hlarge := hhalf n (by omega) hnN
        have hd : (2 : ℝ) * (n / 2 : ℕ) ≤ n := by
          exact_mod_cast Nat.mul_div_le n 2
        have hmul := mul_le_mul_of_nonneg_left hd (mul_nonneg hA hL)
        nlinarith
  exact H N le_rfl

end BretecheTenenbaumMean
