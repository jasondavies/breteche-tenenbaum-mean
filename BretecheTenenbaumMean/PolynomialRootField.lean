module

public import BretecheTenenbaumMean.PrimitiveConductor
public import Mathlib.RingTheory.Polynomial.IntegralNormalization
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

@[expose] public section

/-! # A primitive integral generator attached to an irreducible polynomial -/

namespace BretecheTenenbaumMean

open Polynomial NumberField
open scoped NumberField

/-- Scaling an adjoined root by the leading coefficient gives an integral
primitive element. Its minimal polynomial is the integral normalization of
`F`, so no assumption that `F` is monic is required. -/
theorem exists_integralPrimitive_integralNormalization (F : ℤ[X])
    (hF : Irreducible F) (hdeg : 0 < F.natDegree) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (θ : 𝓞 K),
      Algebra.adjoin ℚ {(θ : K)} = ⊤ ∧ minpoly ℤ θ = F.integralNormalization := by
  let f := F.map (algebraMap ℤ ℚ)
  have hf : Irreducible f :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      (hF.isPrimitive hdeg.ne')).mp hF
  let : Fact (Irreducible f) := ⟨hf⟩
  let K := AdjoinRoot f
  let α : K := AdjoinRoot.root f
  have hα : aeval α F = 0 := by
    rw [AdjoinRoot.aeval_eq_of_algebra, AdjoinRoot.mk_self]
  have hint : IsIntegral ℤ (F.leadingCoeff • α) :=
    isIntegral_leadingCoeff_smul F α hα
  let θ : 𝓞 K := ⟨F.leadingCoeff • α, hint⟩
  have hlc : (F.leadingCoeff : ℚ) ≠ 0 := by
    exact_mod_cast (leadingCoeff_ne_zero.mpr hF.ne_zero)
  have hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤ := by
    apply top_unique
    have htop : Algebra.adjoin ℚ {α} = (⊤ : Subalgebra ℚ K) :=
      AdjoinRoot.adjoinRoot_eq_top
    rw [← htop]
    apply Algebra.adjoin_le
    intro a ha
    have ha' : a = α := Set.mem_singleton_iff.mp ha
    rw [ha']
    have hm := (Algebra.adjoin ℚ {(θ : K)}).toSubmodule.smul_mem (F.leadingCoeff : ℚ)⁻¹
      (Algebra.subset_adjoin (Set.mem_singleton (θ : K)))
    have heq : (F.leadingCoeff : ℚ)⁻¹ • (θ : K) = α := by
      change (F.leadingCoeff : ℚ)⁻¹ • (F.leadingCoeff • α) = α
      rw [← IsScalarTower.algebraMap_smul ℚ F.leadingCoeff α, smul_smul]
      change ((F.leadingCoeff : ℚ)⁻¹ * (F.leadingCoeff : ℚ)) • α = α
      rw [inv_mul_cancel₀ hlc, one_smul]
    rw [heq] at hm
    exact hm
  refine ⟨K, inferInstance, inferInstance, θ, hθ, ?_⟩
  have hzero : aeval (θ : K) F.integralNormalization = 0 := by
    simpa [θ, Algebra.smul_def] using integralNormalization_aeval_eq_zero hα
      (fun x hx ↦ (algebraMap ℤ K).injective_int (by simpa using hx))
  have hd : (minpoly ℤ θ).natDegree = F.natDegree := by
    calc
      _ = Module.finrank ℤ (Algebra.adjoin ℤ {θ}) :=
        (Algebra.adjoin.powerBasis' θ.isIntegral).finrank.symm
      _ = Module.finrank ℤ (𝓞 K) := integralPrimitive_finrank_adjoin θ hθ
      _ = Module.finrank ℚ K := NumberField.RingOfIntegers.rank K
      _ = f.natDegree := (AdjoinRoot.powerBasis hf.ne_zero).finrank.trans
        (AdjoinRoot.powerBasis_dim hf.ne_zero)
      _ = F.natDegree := natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int F
  rw [← NumberField.RingOfIntegers.minpoly_coe]
  apply Eq.symm
  apply eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic θ.isIntegral_coe)
    (monic_integralNormalization hF.ne_zero)
    (minpoly.isIntegrallyClosed_dvd θ.isIntegral_coe hzero)
  rw [NumberField.RingOfIntegers.minpoly_coe, hd, natDegree_integralNormalization]

end BretecheTenenbaumMean
