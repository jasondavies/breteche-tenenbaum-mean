module

public import BretecheTenenbaumMean.WeightedProbability

@[expose] public section

/-! # Marginal distributions in the weighted finite model -/

namespace BretecheTenenbaumMean.WeightedModel

open Finset Real

/-- Arbitrary weighted expectations commute with projection to a smaller
prime cutoff; the prime weights themselves are retained. -/
theorem expectation_smallPrimePart (w : MultiplicativeWeight) {x y : ℝ}
    (hyx : y ≤ x) (f : ℕ → ℝ) :
    expectation w x (fun n ↦ f (smallPrimePart n y)) = expectation w y f := by
  classical
  have hsub := PrimeSums.primesLT_mono hyx
  let B := ∏ p ∈ primesLT x \ primesLT y, (1 + w p / p)
  have hB : 0 < B := by
    apply prod_pos
    intro p _
    have := w.nonneg p
    positivity
  have hnorm : normalizer w x = normalizer w y * B := by
    simpa only [normalizer, B, mul_comm] using
      (prod_sdiff (f := fun p : ℕ ↦ 1 + w p / p) hsub).symm
  have hsum : (∑ n ∈ smoothSupport x, w n * f (smallPrimePart n y) / n) =
      (∑ n ∈ smoothSupport y, w n * f n / n) * B := by
    rw [sum_eq_powerset, sum_eq_powerset]
    have he := sum_powerset_projection (primesLT x) (primesLT y) hsub
      (fun p ↦ w p / p) (fun s ↦ f (∏ p ∈ s, p))
    convert he using 1
    apply sum_congr rfl
    intro s hs
    have hprime : ∀ p ∈ s, p.Prime := fun p hp ↦
      (mem_primesLT.1 (mem_powerset.1 hs hp)).1
    have hfilter : s.filter (fun p : ℕ ↦ (p : ℝ) < y) = s ∩ primesLT y := by
      ext p
      simp only [mem_filter, mem_inter, mem_primesLT]
      exact ⟨fun hp ↦ ⟨hp.1, hprime p hp.1, hp.2⟩,
        fun hp ↦ ⟨hp.1, hp.2.2⟩⟩
    rw [smallPrimePart_prod hprime, hfilter]
  unfold expectation
  rw [hsum, hnorm]
  exact mul_div_mul_right _ _ hB.ne'

/-- Exact weighted count-layer probability. -/
theorem probability_prime_layer_eq (w : MultiplicativeWeight) (x : ℝ) (k : ℕ) :
    probability w x {n | n.primeFactors.card = k} =
      distinctProductSum (primesLT x) (fun p ↦ w p / p) k / normalizer w x := by
  classical
  unfold probability expectation
  congr 1
  rw [sum_eq_powerset, distinctProductSum, powersetCard_eq_filter, sum_filter]
  apply sum_congr rfl
  intro s hs
  have hprime : ∀ p ∈ s, p.Prime := fun p hp ↦
    (mem_primesLT.1 (mem_powerset.1 hs hp)).1
  simp only [Set.indicator, Set.mem_ofPred_eq, Nat.primeFactors_prod hprime]
  split_ifs <;> simp

/-- Every event on the smaller support has exactly the same probability
when evaluated through the small-prime projection. -/
theorem probability_smallPrimePart (w : MultiplicativeWeight) {x y : ℝ}
    (hyx : y ≤ x) (E : Set ℕ) :
    probability w x {n | smallPrimePart n y ∈ E} = probability w y E := by
  classical
  unfold probability
  rw [← expectation_smallPrimePart w hyx]
  congr 1

/-- The weighted count distribution at a smaller cutoff is its marginal. -/
theorem probability_smallPrime_layer_eq (w : MultiplicativeWeight) {x y : ℝ}
    (hyx : y ≤ x) (k : ℕ) :
    probability w x {n | (smallPrimePart n y).primeFactors.card = k} =
      probability w y {n | n.primeFactors.card = k} :=
  probability_smallPrimePart w hyx {n | n.primeFactors.card = k}

end BretecheTenenbaumMean.WeightedModel
