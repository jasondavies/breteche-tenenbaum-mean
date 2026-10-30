module

public import BretecheTenenbaumMean.PrimeIdealFibers
public import BretecheTenenbaumMean.DedekindEulerLog
public import Mathlib.Analysis.PSeries
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

/-! # The uniformly bounded contribution of higher residue degrees -/

namespace BretecheTenenbaumMean

open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The reciprocal squares of rational primes remain summable when each prime
is repeated once for each prime ideal lying over it. -/
theorem summable_rationalPrimeBelow_inv_sq :
    Summable (fun P : HeightOneSpectrum (𝓞 K) ↦ (rationalPrimeBelow P : ℝ)⁻¹ ^ 2) := by
  classical
  let s : ℕ → Set (HeightOneSpectrum (𝓞 K)) := fun p ↦ {P | rationalPrimeBelow P = p}
  have hfinite (p : ℕ) : Finite (s p) := rationalPrimeFiber_finite p
  have hpart : ∀ P, ∃! p, P ∈ s p := fun P ↦ ⟨rationalPrimeBelow P, rfl, fun _ h ↦ h.symm⟩
  apply (summable_partition (fun _ ↦ sq_nonneg _) hpart).mpr
  constructor
  · intro p
    exact Summable.of_finite
  · have hbase : Summable (fun p : ℕ ↦ ((p : ℝ) ^ 2)⁻¹) :=
      Real.summable_nat_pow_inv.mpr (by norm_num)
    have hsum : Summable (fun p : ℕ ↦ (Module.finrank ℚ K : ℝ) * (p : ℝ)⁻¹ ^ 2) := by
      simpa only [inv_pow] using hbase.mul_left (Module.finrank ℚ K : ℝ)
    apply Summable.of_nonneg_of_le (fun _ ↦ tsum_nonneg (fun _ ↦ sq_nonneg _)) ?_ hsum
    intro p
    have hconst : (∑' P : s p, (rationalPrimeBelow P.val : ℝ)⁻¹ ^ 2) =
        (Nat.card (s p) : ℝ) * (p : ℝ)⁻¹ ^ 2 := by
      simp only [show ∀ P : s p, rationalPrimeBelow P.val = p from fun P ↦ P.prop]
      simp [nsmul_eq_mul]
    rw [hconst]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (card_rationalPrimeFiber_le_degree_all (K := K) p)) (sq_nonneg _)

/-- The reciprocal norms of the prime ideals of residue degree at least two
form a convergent series, including on the line `Re(s)=1`. -/
theorem summable_higherDegree_primeIdeal_inv_norm :
    Summable (fun P : {P : HeightOneSpectrum (𝓞 K) // P.asIdeal.inertiaDeg ℤ ≠ 1} ↦
      (Ideal.absNorm P.val.asIdeal : ℝ)⁻¹) := by
  apply Summable.of_nonneg_of_le (fun _ ↦ by positivity) ?_
    ((summable_rationalPrimeBelow_inv_sq K).subtype _)
  intro P
  have hp : 0 < (rationalPrimeBelow P.val : ℝ) :=
    Nat.cast_pos.mpr (rationalPrimeBelow_prime P.val).pos
  have hnorm : (rationalPrimeBelow P.val : ℝ) ^ 2 ≤ (Ideal.absNorm P.val.asIdeal : ℝ) :=
    by exact_mod_cast primeIdeal_norm_ge_sq P.val P.prop
  change _ ≤ (rationalPrimeBelow P.val : ℝ)⁻¹ ^ 2
  rw [inv_pow]
  exact inv_anti₀ (sq_pos_of_pos hp) hnorm

/-- Higher residue degrees contribute a bounded complex sum throughout the
closed right half-plane. The majorant is independent of the imaginary part. -/
theorem higherDegree_primeIdeal_sum_bound {s : ℂ} (hs : 1 ≤ s.re) :
    Summable (fun P : {P : HeightOneSpectrum (𝓞 K) // P.asIdeal.inertiaDeg ℤ ≠ 1} ↦
      primeIdealDirichletTerm K s P.val) ∧
    ‖∑' P : {P : HeightOneSpectrum (𝓞 K) // P.asIdeal.inertiaDeg ℤ ≠ 1},
      primeIdealDirichletTerm K s P.val‖ ≤
        ∑' P : {P : HeightOneSpectrum (𝓞 K) // P.asIdeal.inertiaDeg ℤ ≠ 1},
          (Ideal.absNorm P.val.asIdeal : ℝ)⁻¹ := by
  have hnorm : Summable (fun P : {P : HeightOneSpectrum (𝓞 K) // P.asIdeal.inertiaDeg ℤ ≠ 1} ↦
      ‖primeIdealDirichletTerm K s P.val‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun P ↦
      primeIdealDirichletTerm_norm_le K hs P.val) (summable_higherDegree_primeIdeal_inv_norm K)
  refine ⟨hnorm.of_norm, (norm_tsum_le_tsum_norm hnorm).trans ?_⟩
  exact hnorm.tsum_le_tsum (fun P ↦ primeIdealDirichletTerm_norm_le K hs P.val)
    (summable_higherDegree_primeIdeal_inv_norm K)

end BretecheTenenbaumMean
