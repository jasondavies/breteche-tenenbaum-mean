module

public import BretecheTenenbaumMean.FiniteBonferroni
public import BretecheTenenbaumMean.PrimeGapDecay

@[expose] public section

/-! # Summing the overlaps of separated events -/

namespace BretecheTenenbaumMean

open Finset Real

/-- A finite set of positive integer gaps contributes at most a geometric tail. -/
theorem sum_geometric_gaps_le {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (s : Finset ℕ) (i : ℕ) :
    (∑ j ∈ s.filter (fun j ↦ i < j), ρ ^ (j - i)) ≤ ρ / (1 - ρ) := by
  classical
  let J := (s.filter (fun j ↦ i < j)).image (fun j ↦ j - (i + 1))
  have hinj : Set.InjOn (fun j : ℕ ↦ j - (i + 1)) (s.filter (fun j ↦ i < j)) := by
    intro a ha b hb he
    have := (mem_filter.1 ha).2
    have := (mem_filter.1 hb).2
    change a - (i + 1) = b - (i + 1) at he
    omega
  calc
    _ = ρ * ∑ d ∈ J, ρ ^ d := by
      rw [mul_sum, sum_image hinj]
      apply sum_congr rfl
      intro j hj
      have he : j - i = (j - (i + 1)) + 1 := by
        have := (mem_filter.1 hj).2
        omega
      rw [he, pow_succ, mul_comm]
    _ ≤ ρ * (1 - ρ)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ hρ
      calc
        _ ≤ ∑' d : ℕ, ρ ^ d := (summable_geometric_of_lt_one hρ hρ1).sum_le_tsum _
          (fun _ _ ↦ pow_nonneg hρ _)
        _ = _ := tsum_geometric_of_lt_one hρ hρ1
    _ = _ := by ring

/-- Geometrically decaying overlaps preserve a fixed fraction of the sum of
marginal probabilities. -/
theorem probability_union_ge_of_geometric_pairs (x : ℝ) (s : Finset ℕ)
    (E : ℕ → Set ℕ) {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hpairs : ∀ i ∈ s, ∀ j ∈ s, i < j →
      probability x (E i ∩ E j) ≤ C * ρ ^ (j - i) * probability x (E i)) :
    (1 - C * ρ / (1 - ρ)) * (∑ i ∈ s, probability x (E i)) ≤
      probability x {n | ∃ i ∈ s, n ∈ E i} := by
  have hp : (∑ i ∈ s, ∑ j ∈ s.filter (fun j ↦ i < j), probability x (E i ∩ E j)) ≤
      (C * ρ / (1 - ρ)) * (∑ i ∈ s, probability x (E i)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    calc
      _ ≤ ∑ j ∈ s.filter (fun j ↦ i < j),
          C * ρ ^ (j - i) * probability x (E i) :=
        sum_le_sum (fun j hj ↦ hpairs i hi j (mem_filter.1 hj).1 (mem_filter.1 hj).2)
      _ = (C * probability x (E i)) * ∑ j ∈ s.filter (fun j ↦ i < j), ρ ^ (j - i) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        ring
      _ ≤ (C * probability x (E i)) * (ρ / (1 - ρ)) :=
        mul_le_mul_of_nonneg_left (sum_geometric_gaps_le hρ hρ1 s i)
          (mul_nonneg hC (probability_nonneg _ _))
      _ = _ := by ring
  have hb := probability_exists_mem_ge_pairs x s E
  nlinarith

/-- One fixed spacing makes the overlaps of every finite family of dyadic
prime-count events consume at most half its total marginal probability. -/
theorem exists_dyadic_spacing : ∃ m : ℕ, 0 < m ∧ ∀ x : ℝ, ∀ s : Finset ℕ,
    ∀ t : ℕ, (∀ i ∈ s, exp ((2 : ℝ) ^ (m * i)) ≤ x) →
    (1 / 2 : ℝ) * (∑ i ∈ s, probability (exp ((2 : ℝ) ^ (m * i)))
      {n | n.primeFactors.card = m * i + t}) ≤
    probability x {n | ∃ i ∈ s,
      (smallPrimePart n (exp ((2 : ℝ) ^ (m * i)))).primeFactors.card = m * i + t} := by
  obtain ⟨C, hC, hdecay⟩ := probability_dyadic_joint_decay
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < 1 / (2 * C + 1) by positivity) primeGapRatio_lt_one
  have hmpos : 0 < m := by
    by_contra h
    have he : m = 0 := by omega
    rw [he, pow_zero] at hm
    have := (lt_div_iff₀ (show (0 : ℝ) < 2 * C + 1 by positivity)).1 hm
    linarith
  have hρ : 0 ≤ primeGapRatio ^ m := pow_nonneg primeGapRatio_pos.le _
  have hρ1 : primeGapRatio ^ m < 1 := by
    have hsmall := (lt_div_iff₀ (show (0 : ℝ) < 2 * C + 1 by positivity)).1 hm
    nlinarith [mul_nonneg hC.le hρ]
  have hcoef : (1 / 2 : ℝ) ≤ 1 - C * primeGapRatio ^ m / (1 - primeGapRatio ^ m) := by
    have hsmall := (lt_div_iff₀ (show (0 : ℝ) < 2 * C + 1 by positivity)).1 hm
    have hquot : C * primeGapRatio ^ m / (1 - primeGapRatio ^ m) ≤ 1 / 2 := by
      apply (div_le_iff₀ (by linarith)).2
      nlinarith
    linarith
  refine ⟨m, hmpos, fun x s t hx ↦ ?_⟩
  let E : ℕ → Set ℕ := fun i ↦ {n |
    (smallPrimePart n (exp ((2 : ℝ) ^ (m * i)))).primeFactors.card = m * i + t}
  have hmarg : ∀ i ∈ s, probability x (E i) =
      probability (exp ((2 : ℝ) ^ (m * i))) {n | n.primeFactors.card = m * i + t} :=
    fun i hi ↦ probability_smallPrime_layer_eq (hx i hi) _
  have hpairs : ∀ i ∈ s, ∀ j ∈ s, i < j →
      probability x (E i ∩ E j) ≤ C * (primeGapRatio ^ m) ^ (j - i) * probability x (E i) := by
    intro i hi j hj hij
    have hgap : 0 < m * (j - i) := Nat.mul_pos hmpos (Nat.sub_pos_of_lt hij)
    have hsum : m * i + m * (j - i) = m * j := by
      rw [← Nat.mul_add, Nat.add_sub_of_le hij.le]
    have hsumt : m * i + t + m * (j - i) = m * j + t := by omega
    have he := hdecay x (m * i) (m * (j - i)) (m * i + t) hgap
      (by simpa only [hsum] using hx j hj)
    rw [hsum, hsumt, pow_mul primeGapRatio m (j - i), ← hmarg i hi] at he
    exact he
  have hu := probability_union_ge_of_geometric_pairs x s E hC.le hρ hρ1 hpairs
  have hsum : (∑ i ∈ s, probability x (E i)) =
      ∑ i ∈ s, probability (exp ((2 : ℝ) ^ (m * i)))
        {n | n.primeFactors.card = m * i + t} := sum_congr rfl hmarg
  calc
    _ = (1 / 2 : ℝ) * ∑ i ∈ s, probability x (E i) := by rw [hsum]
    _ ≤ _ := (mul_le_mul_of_nonneg_right hcoef
      (sum_nonneg (fun _ _ ↦ probability_nonneg _ _))).trans hu

end BretecheTenenbaumMean
