module

public import BretecheTenenbaumMean.GoodSetGrid
public import BretecheTenenbaumMean.SmallPrimeDistribution

@[expose] public section

/-! # Reduction of the good-set exception to one-cutoff divisor tails -/

namespace BretecheTenenbaumMean

open Real Finset

/-- The fixed loss from rounding a cutoff upward to the logarithmic grid. -/
noncomputable def gridDivisorThreshold (δ T : ℝ) (j : ℕ) : ℝ :=
  exp (-7) * goodEnvelope δ T (goodSetGrid (j + 1))

theorem gridDivisorThreshold_pos {δ T : ℝ} (hT : 0 < T) (j : ℕ) :
    0 < gridDivisorThreshold δ T j :=
  mul_pos (exp_pos _) (goodEnvelope_pos hT (goodSetGrid_ge_one (by omega)))

/-- Exact formula for the threshold in the Poisson large-deviation variables. -/
theorem gridDivisorThreshold_eq_exp {δ T : ℝ} (hT : 0 < T) (j : ℕ) :
    gridDivisorThreshold δ T j = exp (barrierProfile δ (log T) (j + 1) - 7) := by
  rw [gridDivisorThreshold, goodEnvelope_eq_exp_profile hT (goodSetGrid_ge_one (by omega)),
    loglog_goodSetGrid, ← exp_add]
  push_cast
  congr 1
  ring

theorem log_gridDivisorThreshold {δ T : ℝ} (hT : 0 < T) (j : ℕ) :
    log (gridDivisorThreshold δ T j) = barrierProfile δ (log T) (j + 1) - 7 := by
  rw [gridDivisorThreshold_eq_exp hT, log_exp]

/-- The exceptional probability is bounded by a finite sum of divisor tails
at grid cutoffs. The finite subfamily may depend on `x`; the summands themselves
are independent of the ambient model. -/
theorem goodSet_compl_le_finite_grid_sum {δ T : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hT : 1 < T) (x : ℝ) :
    ∃ s : Finset ℕ, probability x (goodSet δ T)ᶜ ≤
      ∑ j ∈ s, probability (goodSetGrid (j + 1)) {n | gridDivisorThreshold δ T j ≤ tau n} := by
  classical
  let E := fun j ↦ {n | gridDivisorThreshold δ T j ≤ tau (smallPrimePart n (goodSetGrid (j + 1)))}
  have hcover : probability x (goodSet δ T)ᶜ ≤ probability x {n | ∃ j, n ∈ E j} := by
    apply probability_mono_on_support
    intro n hn hbad
    obtain ⟨r, hr, h⟩ := goodSet_failure_grid hδ hδ1 hT (mem_smoothSupport.1 hn).1 hbad
    refine ⟨r - 1, ?_⟩
    change exp (-7) * goodEnvelope δ T (goodSetGrid (r - 1 + 1)) ≤
      tau (smallPrimePart n (goodSetGrid (r - 1 + 1)))
    rw [Nat.sub_add_cancel hr]
    exact h.le
  obtain ⟨s, hs⟩ := probability_exists_le_finite_sum x E
  refine ⟨s, hcover.trans (hs.trans ?_)⟩
  apply sum_le_sum
  intro j _
  exact probability_smallPrime_tau_ge_le x (goodSetGrid (j + 1))
    (gridDivisorThreshold_pos (by linarith : 0 < T) j)

/-- A uniform bound for finite grid sums suffices for the original continuum
of constraints. This separates the proved discretization from the analytic summation estimate,
assembled in `GoodSetExceptional`. -/
theorem probability_goodSet_compl_le_of_grid_sum {δ T C : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hT : 1 < T)
    (hgrid : ∀ s : Finset ℕ,
      (∑ j ∈ s, probability (goodSetGrid (j + 1)) {n | gridDivisorThreshold δ T j ≤ tau n}) ≤ C / T)
    (x : ℝ) : probability x (goodSet δ T)ᶜ ≤ C / T := by
  obtain ⟨s, hs⟩ := goodSet_compl_le_finite_grid_sum hδ hδ1 hT x
  exact hs.trans (hgrid s)

end BretecheTenenbaumMean
