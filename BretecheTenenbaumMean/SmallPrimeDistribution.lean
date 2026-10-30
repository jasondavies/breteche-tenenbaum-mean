module

public import BretecheTenenbaumMean.PrimeCountTail
public import BretecheTenenbaumMean.PrimePartition

@[expose] public section

/-! # Distribution of the small-prime part

Projection to a smaller prime cutoff preserves exactly the finite Euler-product
probability distribution. The upper-tail comparison also covers cutoffs beyond
that of the original probability space.
-/

namespace BretecheTenenbaumMean

open Real Finset

/-- The marginal distribution of the small-prime count is independent of the
larger ambient prime cutoff. -/
theorem probability_smallPrime_layer_eq {x y : ℝ} (hyx : y ≤ x) (r : ℕ) :
    probability x {n | (smallPrimePart n y).primeFactors.card = r} =
      probability y {n | n.primeFactors.card = r} := by
  classical
  have hA : (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < y) = primesLT y := by
    ext p
    simp only [mem_filter, mem_primesLT]
    exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.2.trans_le hyx⟩, h.2⟩⟩
  have hsub : primesLT y ⊆ primesLT x := by
    rw [← hA]
    exact filter_subset _ _
  let B := ∏ p ∈ primesLT x \ primesLT y, (1 + (1 : ℝ) / p)
  have hB : 0 < B := by
    apply prod_pos
    intro p _
    positivity
  have hnorm : normalizer x = B * normalizer y := by
    simpa only [normalizer, B, one_div] using
      (prod_sdiff (f := fun p : ℕ ↦ 1 + (1 : ℝ) / p) hsub).symm
  have he := sum_smallPrime_layer_eq_product x y r (fun _ ↦ (1 : ℝ)) rfl
    (fun _ _ _ ↦ by norm_num)
  rw [hA] at he
  rw [probability_prime_layer_eq]
  unfold probability expectation
  have hsum : (∑ n ∈ smoothSupport x,
      ({n | (smallPrimePart n y).primeFactors.card = r} : Set ℕ).indicator (fun _ ↦ (1 : ℝ)) n / n) =
      distinctProductSum (primesLT y) (fun p ↦ (p : ℝ)⁻¹) r * B := by
    simpa only [Set.indicator, Set.mem_ofPred_eq, ite_div, zero_div, B, one_div] using he
  rw [hsum, hnorm]
  field_simp

/-- Upper-tail distributions agree as well; the finite summation range is
chosen to contain both sets of possible prime counts. -/
theorem probability_smallPrime_ge_eq {x y : ℝ} (hyx : y ≤ x) (k : ℕ) :
    probability x {n | k ≤ (smallPrimePart n y).primeFactors.card} =
      probability y {n | k ≤ n.primeFactors.card} := by
  classical
  let s := (smoothSupport x).image (fun n ↦ (smallPrimePart n y).primeFactors.card) ∪
    (smoothSupport y).image (fun n ↦ n.primeFactors.card)
  have hx : ∀ n ∈ smoothSupport x, (smallPrimePart n y).primeFactors.card ∈ s :=
    fun n hn ↦ mem_union_left _ (mem_image.2 ⟨n, hn, rfl⟩)
  have hy : ∀ n ∈ smoothSupport y, n.primeFactors.card ∈ s :=
    fun n hn ↦ mem_union_right _ (mem_image.2 ⟨n, hn, rfl⟩)
  rw [probability_ge_eq_sum_fibers_of_mem x _ k s hx,
    probability_ge_eq_sum_fibers_of_mem y _ k s hy]
  exact sum_congr rfl (fun r _ ↦ probability_smallPrime_layer_eq hyx r)

/-- Exact distribution of the small-prime divisor count at every positive
real threshold, with the correct ceiling convention. -/
theorem probability_smallPrime_tau_ge_eq {x y R : ℝ} (hyx : y ≤ x) (hR : 0 < R) :
    probability x {n | R ≤ tau (smallPrimePart n y)} = probability y {n | R ≤ tau n} := by
  have he : probability x {n | R ≤ tau (smallPrimePart n y)} =
      probability x {n | ⌈log R / log 2⌉₊ ≤ (smallPrimePart n y).primeFactors.card} := by
    apply probability_congr_on_support
    intro n hn
    exact tau_ge_iff_prime_count_ge_ceil
      ((mem_smoothSupport.1 hn).1.squarefree_of_dvd (smallPrimePart_dvd n y)) hR
  rw [he, probability_smallPrime_ge_eq hyx, probability_tau_ge_eq y hR]

/-- Divisor-count upper tails are monotone in the prime cutoff. -/
theorem probability_tau_ge_mono {x y R : ℝ} (hxy : x ≤ y) (hR : 0 < R) :
    probability x {n | R ≤ tau n} ≤ probability y {n | R ≤ tau n} := by
  rw [← probability_smallPrime_tau_ge_eq hxy hR]
  apply probability_mono_on_support
  intro n hn h
  exact h.trans (tau_le_of_dvd (mem_smoothSupport.1 hn).1.ne_zero (smallPrimePart_dvd n x))

/-- A cutoff beyond the ambient support leaves each supported integer unchanged. -/
theorem smallPrimePart_eq_self_on_support {x y : ℝ} (hxy : x ≤ y) {n : ℕ}
    (hn : n ∈ smoothSupport x) : smallPrimePart n y = n := by
  obtain ⟨hsq, hp⟩ := mem_smoothSupport.1 hn
  apply smallPrimePart_eq_self hsq
  intro p hpn
  exact (hp p hpn).trans_le hxy

end BretecheTenenbaumMean
