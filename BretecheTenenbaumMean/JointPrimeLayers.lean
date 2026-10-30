module

public import BretecheTenenbaumMean.PrimeMarginal
public import BretecheTenenbaumMean.DistinctProductLower

@[expose] public section

/-! # Exact joint distributions at two prime cutoffs -/

namespace BretecheTenenbaumMean

open Finset Real

/-- Two specified counts in disjoint prime blocks give a product of elementary
symmetric coefficients. The second count is expressed as an increment. -/
theorem joint_layer_product_split {α : Type*} [DecidableEq α]
    (P A : Finset α) (hA : A ⊆ P) (w : α → ℝ) (r l : ℕ) :
    (∑ s ∈ P.powerset, if (s ∩ A).card = r ∧ s.card = r + l
      then ∏ p ∈ s, w p else 0) =
    distinctProductSum A w r * distinctProductSum (P \ A) w l := by
  have hd : Disjoint A (P \ A) := disjoint_sdiff_self_right
  conv_lhs => rw [← union_sdiff_of_subset hA]
  rw [sum_powerset_disjoint_union A (P \ A) hd]
  calc
    _ = ∑ a ∈ A.powerset, ∑ b ∈ (P \ A).powerset,
        (if a.card = r then ∏ p ∈ a, w p else 0) *
        (if b.card = l then ∏ p ∈ b, w p else 0) := by
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      have haA := mem_powerset.1 ha
      have hbB := mem_powerset.1 hb
      have hab : Disjoint a b := hd.mono haA hbB
      have hbA : Disjoint b A := hd.symm.mono_left hbB
      rw [union_inter_distrib_right, inter_eq_left.2 haA,
        disjoint_iff_inter_eq_empty.1 hbA, union_empty, card_union_of_disjoint hab,
        prod_union hab]
      by_cases har : a.card = r <;> simp [har]
    _ = _ := by
      simp_rw [← mul_sum]
      rw [← sum_mul]
      simp only [distinctProductSum, powersetCard_eq_filter, sum_filter]

/-- Exact probability of `r` primes below `y` and `r+l` below `z`, in any
ambient model with cutoff at least `z`. -/
theorem probability_joint_prime_layers {x y z : ℝ} (hyz : y ≤ z) (hzx : z ≤ x)
    (r l : ℕ) :
    probability x {n | (smallPrimePart n y).primeFactors.card = r ∧
      (smallPrimePart n z).primeFactors.card = r + l} =
    probability y {n | n.primeFactors.card = r} *
      (distinctProductSum (primesLT z \ primesLT y) (fun p ↦ (p : ℝ)⁻¹) l *
        (normalizer y / normalizer z)) := by
  classical
  rw [probability_smallPrime_joint_marginal hyz hzx, probability_prime_layer_eq]
  have hsum : (∑ n ∈ smoothSupport z,
      ({n | (smallPrimePart n y).primeFactors.card = r ∧ n.primeFactors.card = r + l} :
        Set ℕ).indicator (fun _ ↦ (1 : ℝ)) n / n) =
    distinctProductSum (primesLT y) (fun p ↦ (p : ℝ)⁻¹) r *
      distinctProductSum (primesLT z \ primesLT y) (fun p ↦ (p : ℝ)⁻¹) l := by
    rw [sum_smoothSupport_eq_powerset]
    rw [← joint_layer_product_split (primesLT z) (primesLT y)
      (PrimeSums.primesLT_mono hyz)]
    apply sum_congr rfl
    intro s hs
    have hprime : ∀ p ∈ s, p.Prime := fun p hp ↦
      (mem_primesLT.1 (mem_powerset.1 hs hp)).1
    have hfilter : s.filter (fun p : ℕ ↦ (p : ℝ) < y) = s ∩ primesLT y := by
      ext p
      simp only [mem_filter, mem_inter, mem_primesLT]
      exact ⟨fun hp ↦ ⟨hp.1, hprime p hp.1, hp.2⟩,
        fun hp ↦ ⟨hp.1, hp.2.2⟩⟩
    simp only [Set.indicator, Set.mem_ofPred_eq, primeFactors_smallPrimePart_prod hprime,
      hfilter, Nat.primeFactors_prod hprime]
    split_ifs
    · rw [Nat.cast_prod, one_div, ← prod_inv_distrib]
    · simp
  unfold probability expectation
  rw [hsum]
  have hn := (normalizer_pos y).ne'
  field_simp

/-- The exact joint probability is bounded by its first marginal times the
factorial coefficient for the intervening prime interval. -/
theorem probability_joint_prime_layers_le {x y z : ℝ} (hyz : y ≤ z) (hzx : z ≤ x)
    (r l : ℕ) :
    probability x {n | (smallPrimePart n y).primeFactors.card = r ∧
      (smallPrimePart n z).primeFactors.card = r + l} ≤
    probability y {n | n.primeFactors.card = r} *
      (((∑ p ∈ primesLT z \ primesLT y, (p : ℝ)⁻¹) ^ l / (l.factorial : ℝ)) *
        (normalizer y / normalizer z)) := by
  rw [probability_joint_prime_layers hyz hzx]
  apply mul_le_mul_of_nonneg_left _ (probability_nonneg _ _)
  apply mul_le_mul_of_nonneg_right _ (by positivity [normalizer_pos y, normalizer_pos z])
  exact distinctProductSum_le _ _ _ (fun _ _ ↦ by positivity)

end BretecheTenenbaumMean
