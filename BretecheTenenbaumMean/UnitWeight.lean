module

public import BretecheTenenbaumMean.WeightedDeltaExpectation
public import BretecheTenenbaumMean.WeightedPropositionTwoTwo
public import BretecheTenenbaumMean.WeightedSecondMomentTail

@[expose] public section

/-! # The unweighted model as the unit-weight case

The moment and frequency arguments of §2 are carried out once, for a general
weight satisfying `PrimeEstimates`. Constant unit weight recovers the paper's
finite model, and the cosine estimate (2.12) supplies the only analytic hypothesis.
-/

namespace BretecheTenenbaumMean.WeightedModel

open Finset Real

/-- Strict and weak prime cutoffs differ by at most one reciprocal prime. -/
theorem abs_cosinePrimeSum_unit_sub_le {x : ℝ} (hx : 2 ≤ x) (ψ : ℝ) :
    |cosinePrimeSum unitWeight x ψ - PrimeSums.cosinePrimeSum x ψ| ≤ 1 := by
  classical
  have hweak : PrimeSums.cosinePrimeSum x ψ =
      ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, cos (ψ * log p) / p := by
    rw [PrimeSums.cosinePrimeSum, sum_filter]
  have hstrict : cosinePrimeSum unitWeight x ψ = ∑ p ∈ primesLT x, cos (ψ * log p) / p := by
    simp only [cosinePrimeSum, unitWeight, one_mul]
  have hsub : primesLT x ⊆ (range (⌊x⌋₊ + 1)).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpp, hpx⟩ := mem_primesLT.1 hp
    exact mem_filter.2 ⟨mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hpx.le)), hpp⟩
  have hend : (range (⌊x⌋₊ + 1)).filter Nat.Prime \ primesLT x ⊆ {⌊x⌋₊} := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := mem_sdiff.1 hp
    obtain ⟨hr, hpp⟩ := mem_filter.1 hp1
    have hnot : ¬ (p : ℝ) < x := fun h ↦ hp2 (mem_primesLT.2 ⟨hpp, h⟩)
    exact mem_singleton.2 (le_antisymm (Nat.lt_succ_iff.1 (mem_range.1 hr))
      (Nat.floor_le_of_le (le_of_not_gt hnot)))
  have hbound : |∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime \ primesLT x,
      cos (ψ * log (p : ℝ)) / (p : ℝ)| ≤ 1 := by
    calc
      _ ≤ ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime \ primesLT x,
          |cos (ψ * log (p : ℝ)) / (p : ℝ)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ ({⌊x⌋₊} : Finset ℕ), |cos (ψ * log (p : ℝ)) / (p : ℝ)| :=
        sum_le_sum_of_subset_of_nonneg hend (fun _ _ _ ↦ abs_nonneg _)
      _ ≤ 1 := by
        rw [sum_singleton, abs_div, Nat.abs_cast]
        have hf : (1 : ℝ) ≤ ⌊x⌋₊ := by
          exact_mod_cast Nat.le_floor (by simpa using (by linarith : (1 : ℝ) ≤ x))
        exact div_le_one_of_le₀ ((abs_cos_le_one _).trans hf) (by linarith)
  rw [hstrict, hweak, ← sum_sdiff hsub, abs_sub_comm, add_sub_cancel_right]
  exact hbound

theorem cosinePrimeSum_unit_abs (x θ : ℝ) :
    cosinePrimeSum unitWeight x |θ| = cosinePrimeSum unitWeight x θ := by
  simp only [cosinePrimeSum]
  apply sum_congr rfl
  intro p _
  rcases abs_cases θ with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h, cos_neg]

/-- The unit weight satisfies the weighted model's only analytic hypothesis. -/
theorem nonempty_primeEstimates_unitWeight : Nonempty (PrimeEstimates unitWeight) := by
  obtain ⟨K, hK, h⟩ := PrimeSums.cosinePrimeSum_log_ratio_two
  refine ⟨{
    primeBound := 1
    primeBound_nonneg := zero_le_one
    prime_le := fun _ _ ↦ le_rfl
    errorBound := K + 1
    errorBound_nonneg := by positivity
    cosine_error := fun x θ hx hθ ↦ ?_ }⟩
  rw [← cosinePrimeSum_unit_abs]
  have hmain := h x |θ| hx (abs_nonneg θ) hθ
  have hcut := abs_cosinePrimeSum_unit_sub_le hx |θ|
  have := abs_sub_le (cosinePrimeSum unitWeight x |θ|) (PrimeSums.cosinePrimeSum x |θ|)
    (log (log x / (1 + |θ| * log x)))
  linarith

@[simp] theorem truncatedMoment_unit (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ) (x : ℝ) :
    truncatedMoment unitWeight δ T θ q x = BretecheTenenbaumMean.truncatedMoment δ T θ q x := by
  simp only [truncatedMoment, BretecheTenenbaumMean.truncatedMoment, expectation_unit]

end BretecheTenenbaumMean.WeightedModel
