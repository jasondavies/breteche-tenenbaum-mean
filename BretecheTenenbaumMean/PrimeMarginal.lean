module

public import BretecheTenenbaumMean.SmallPrimeDistribution
public import BretecheTenenbaumMean.PrimeSums.Strict

@[expose] public section

/-! # Arbitrary marginals of the small-prime projection -/

namespace BretecheTenenbaumMean

open Finset Real

/-- Summing out a disjoint block leaves its Euler product, for any statistic
of the retained subset. -/
theorem sum_powerset_projection {α : Type*} [DecidableEq α]
    (P A : Finset α) (hA : A ⊆ P) (w : α → ℝ) (F : Finset α → ℝ) :
    (∑ s ∈ P.powerset, F (s ∩ A) * ∏ p ∈ s, w p) =
      (∑ a ∈ A.powerset, F a * ∏ p ∈ a, w p) *
        ∏ p ∈ P \ A, (1 + w p) := by
  have hd : Disjoint A (P \ A) := disjoint_sdiff_self_right
  conv_lhs => rw [← union_sdiff_of_subset hA]
  rw [sum_powerset_disjoint_union A (P \ A) hd]
  calc
    _ = ∑ a ∈ A.powerset, ∑ b ∈ (P \ A).powerset,
        (F a * ∏ p ∈ a, w p) * ∏ p ∈ b, w p := by
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      have haA := mem_powerset.1 ha
      have hbB := mem_powerset.1 hb
      have hab : Disjoint a b := hd.mono haA hbB
      have hbA : Disjoint b A := hd.symm.mono_left hbB
      rw [union_inter_distrib_right, inter_eq_left.2 haA,
        disjoint_iff_inter_eq_empty.1 hbA, union_empty, prod_union hab]
      ring
    _ = _ := by simp_rw [← mul_sum, ← prod_one_add]; rw [← sum_mul]

/-- Projecting to a smaller cutoff preserves every real-valued expectation. -/
theorem expectation_smallPrimePart {x y : ℝ} (hyx : y ≤ x) (f : ℕ → ℝ) :
    expectation x (fun n ↦ f (smallPrimePart n y)) = expectation y f := by
  classical
  have hsub := PrimeSums.primesLT_mono hyx
  let B := ∏ p ∈ primesLT x \ primesLT y, (1 + (p : ℝ)⁻¹)
  have hB : 0 < B := prod_pos (fun _ _ ↦ by positivity)
  have hnorm : normalizer x = normalizer y * B := by
    simpa only [normalizer, B, mul_comm] using
      (prod_sdiff (f := fun p : ℕ ↦ 1 + (p : ℝ)⁻¹) hsub).symm
  have hsum : (∑ n ∈ smoothSupport x, f (smallPrimePart n y) / n) =
      (∑ n ∈ smoothSupport y, f n / n) * B := by
    rw [sum_smoothSupport_eq_powerset, sum_smoothSupport_eq_powerset]
    have he := sum_powerset_projection (primesLT x) (primesLT y) hsub
      (fun p ↦ (p : ℝ)⁻¹) (fun s ↦ f (∏ p ∈ s, p))
    convert he using 1
    · apply sum_congr rfl
      intro s hs
      have hprime : ∀ p ∈ s, p.Prime := fun p hp ↦
        (mem_primesLT.1 (mem_powerset.1 hs hp)).1
      have hfilter : s.filter (fun p : ℕ ↦ (p : ℝ) < y) = s ∩ primesLT y := by
        ext p
        simp only [mem_filter, mem_inter, mem_primesLT]
        exact ⟨fun hp ↦ ⟨hp.1, hprime p hp.1, hp.2⟩,
          fun hp ↦ ⟨hp.1, hp.2.2⟩⟩
      rw [smallPrimePart_prod hprime, hfilter, Nat.cast_prod, div_eq_mul_inv,
        ← prod_inv_distrib]
    · congr 1
      apply sum_congr rfl
      intro s _
      rw [Nat.cast_prod, div_eq_mul_inv, ← prod_inv_distrib]
  unfold expectation
  rw [hsum, hnorm]
  exact mul_div_mul_right _ _ hB.ne'

/-- Event probabilities are likewise preserved by projection. -/
theorem probability_smallPrimePart {x y : ℝ} (hyx : y ≤ x) (E : Set ℕ) :
    probability x {n | smallPrimePart n y ∈ E} = probability y E := by
  classical
  unfold probability
  rw [← expectation_smallPrimePart hyx]
  congr 1

/-- Nested small-prime projections collapse to the smaller cutoff. -/
theorem smallPrimePart_smallPrimePart (n : ℕ) {y z : ℝ} (hyz : y ≤ z) :
    smallPrimePart (smallPrimePart n z) y = smallPrimePart n y := by
  classical
  unfold smallPrimePart
  rw [Nat.primeFactors_prod (fun p hp ↦
    Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1), filter_filter]
  congr 1
  ext p
  simp only [mem_filter]
  exact ⟨fun hp ↦ ⟨hp.1, hp.2.2⟩,
    fun hp ↦ ⟨hp.1, hp.2.trans_le hyz, hp.2⟩⟩

/-- The joint distribution at two nested cutoffs is independent of any larger
ambient cutoff. -/
theorem probability_smallPrime_joint_marginal {x y z : ℝ}
    (hyz : y ≤ z) (hzx : z ≤ x) (r s : ℕ) :
    probability x {n | (smallPrimePart n y).primeFactors.card = r ∧
      (smallPrimePart n z).primeFactors.card = s} =
    probability z {n | (smallPrimePart n y).primeFactors.card = r ∧
      n.primeFactors.card = s} := by
  have h := probability_smallPrimePart hzx
    {n | (smallPrimePart n y).primeFactors.card = r ∧ n.primeFactors.card = s}
  simpa only [Set.mem_ofPred_eq, smallPrimePart_smallPrimePart _ hyz] using h

end BretecheTenenbaumMean
