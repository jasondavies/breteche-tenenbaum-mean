module

public import BretecheTenenbaumMean.WeightedEventBounds
public import BretecheTenenbaumMean.WeightedMarginal
public import BretecheTenenbaumMean.GoodSetReduction

@[expose] public section

/-! # Weighted good-set exceptions reduced to divisor tails -/

namespace BretecheTenenbaumMean.WeightedModel

open Real Finset

theorem probability_smallPrime_tau_ge_eq (w : MultiplicativeWeight)
    {x y : ℝ} (hyx : y ≤ x) (R : ℝ) :
    probability w x {n | R ≤ tau (smallPrimePart n y)} =
      probability w y {n | R ≤ tau n} :=
  probability_smallPrimePart w hyx {n | R ≤ tau n}

theorem probability_tau_ge_mono (w : MultiplicativeWeight)
    {x y : ℝ} (hxy : x ≤ y) (R : ℝ) :
    probability w x {n | R ≤ tau n} ≤ probability w y {n | R ≤ tau n} := by
  rw [← probability_smallPrime_tau_ge_eq w hxy R]
  apply probability_mono_on_support
  intro n hn h
  exact h.trans (tau_le_of_dvd (mem_smoothSupport.1 hn).1.ne_zero (smallPrimePart_dvd n x))

theorem probability_smallPrime_tau_ge_le (w : MultiplicativeWeight) (x y R : ℝ) :
    probability w x {n | R ≤ tau (smallPrimePart n y)} ≤
      probability w y {n | R ≤ tau n} := by
  rcases le_total y x with hyx | hxy
  · exact (probability_smallPrime_tau_ge_eq w hyx R).le
  · have he : probability w x {n | R ≤ tau (smallPrimePart n y)} =
        probability w x {n | R ≤ tau n} := by
      apply probability_congr_on_support
      intro n hn
      simp only [Set.mem_ofPred_eq, smallPrimePart_eq_self_on_support hxy hn]
    rw [he]
    exact probability_tau_ge_mono w hxy R

/-- The deterministic discretization is unchanged under multiplicative weights. -/
theorem goodSet_compl_le_finite_grid_sum (w : MultiplicativeWeight) {δ T : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hT : 1 < T) (x : ℝ) :
    ∃ s : Finset ℕ, probability w x (goodSet δ T)ᶜ ≤
      ∑ j ∈ s, probability w (goodSetGrid (j + 1)) {n | gridDivisorThreshold δ T j ≤ tau n} := by
  classical
  let E := fun j ↦ {n | gridDivisorThreshold δ T j ≤ tau (smallPrimePart n (goodSetGrid (j + 1)))}
  have hcover : probability w x (goodSet δ T)ᶜ ≤ probability w x {n | ∃ j, n ∈ E j} := by
    apply probability_mono_on_support
    intro n hn hbad
    obtain ⟨r, hr, h⟩ := goodSet_failure_grid hδ hδ1 hT (mem_smoothSupport.1 hn).1 hbad
    refine ⟨r - 1, ?_⟩
    change exp (-7) * goodEnvelope δ T (goodSetGrid (r - 1 + 1)) ≤
      tau (smallPrimePart n (goodSetGrid (r - 1 + 1)))
    rw [Nat.sub_add_cancel hr]
    exact h.le
  obtain ⟨s, hs⟩ := probability_exists_le_finite_sum w x E
  refine ⟨s, hcover.trans (hs.trans ?_)⟩
  apply sum_le_sum
  intro j _
  exact probability_smallPrime_tau_ge_le w x (goodSetGrid (j + 1)) (gridDivisorThreshold δ T j)

theorem probability_goodSet_compl_le_of_grid_sum (w : MultiplicativeWeight) {δ T C : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hT : 1 < T)
    (hgrid : ∀ s : Finset ℕ,
      (∑ j ∈ s, probability w (goodSetGrid (j + 1))
        {n | gridDivisorThreshold δ T j ≤ tau n}) ≤ C / T)
    (x : ℝ) : probability w x (goodSet δ T)ᶜ ≤ C / T := by
  obtain ⟨s, hs⟩ := goodSet_compl_le_finite_grid_sum w hδ hδ1 hT x
  exact hs.trans (hgrid s)

end BretecheTenenbaumMean.WeightedModel
