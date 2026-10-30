module

public import BretecheTenenbaumMean.LinearPrimeFactors
public import BretecheTenenbaumMean.PrimeIdealFibers
public import BretecheTenenbaumMean.PrimitiveConductor
public import BretecheTenenbaumMean.PolynomialRootField
public import BretecheTenenbaumMean.IntegralNormalizationRoots

@[expose] public section

/-! # Polynomial root counts as counts of prime ideals of prime norm -/

namespace BretecheTenenbaumMean

open NumberField IsDedekindDomain
open scoped NumberField

/-- Away from the conductor exponent, roots of the minimal polynomial modulo
`p` correspond exactly to the prime ideals of norm `p`. -/
noncomputable def minpolyRootsEquivNormPrimes {K : Type*} [Field K] [NumberField K]
    (θ : 𝓞 K) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ RingOfIntegers.exponent θ) :
    NairTenenbaum.ResidueRoots (minpoly ℤ θ) p ≃
      {P : HeightOneSpectrum (𝓞 K) // Ideal.absNorm P.asIdeal = p} :=
  (minpolyRootsEquivDegreeOnePrimes θ p hp).trans (degreeOnePrimesEquivNormPrimes p)

theorem rootCount_minpoly_eq_normPrimes {K : Type*} [Field K] [NumberField K]
    (θ : 𝓞 K) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ RingOfIntegers.exponent θ) :
    NairTenenbaum.rootCount (minpoly ℤ θ) p =
      Nat.card {P : HeightOneSpectrum (𝓞 K) // Ideal.absNorm P.asIdeal = p} :=
  Nat.card_congr (minpolyRootsEquivNormPrimes θ p hp)

/-- For an integral primitive element, the root/prime-ideal identity holds
outside an explicitly finite set of rational primes. -/
theorem integralPrimitive_rootCount_eq_normPrimes_cofinite {K : Type*}
    [Field K] [NumberField K] (θ : 𝓞 K) (hθ : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      NairTenenbaum.rootCount (minpoly ℤ θ) p =
        Nat.card {P : HeightOneSpectrum (𝓞 K) // Ideal.absNorm P.asIdeal = p} := by
  classical
  let S := (integralPrimitive_finite_badPrimes θ hθ).toFinset
  refine ⟨S, fun p hp hS ↦ ?_⟩
  let : Fact p.Prime := ⟨hp⟩
  apply rootCount_minpoly_eq_normPrimes θ p
  intro hdvd
  exact hS ((Set.Finite.mem_toFinset _).mpr ⟨hp, hdvd⟩)

/-- Every irreducible nonconstant integer polynomial has a number field whose
prime-norm ideal counts equal its root counts at all but finitely many primes.
The integer `N` contains both the conductor and the leading-coefficient exceptions. -/
theorem exists_numberField_rootCount_eq_normPrimes (F : Polynomial ℤ)
    (hF : Irreducible F) (hdeg : 0 < F.natDegree) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (N : ℕ), 0 < N ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        NairTenenbaum.rootCount F p =
          Nat.card {P : HeightOneSpectrum (𝓞 K) // Ideal.absNorm P.asIdeal = p} := by
  obtain ⟨K, hK, hNF, θ, hθ, hmin⟩ :=
    exists_integralPrimitive_integralNormalization F hF hdeg
  let N := RingOfIntegers.exponent θ * F.leadingCoeff.natAbs
  have hN : 0 < N := Nat.mul_pos (integralPrimitive_exponent_pos θ hθ)
    (Int.natAbs_pos.mpr (Polynomial.leadingCoeff_ne_zero.mpr hF.ne_zero))
  refine ⟨K, hK, hNF, N, hN, fun p hp hbad ↦ ?_⟩
  let : Fact p.Prime := ⟨hp⟩
  have hcond : ¬ p ∣ RingOfIntegers.exponent θ :=
    fun h ↦ hbad (dvd_mul_of_dvd_left h _)
  have hlead : (F.leadingCoeff : ZMod p) ≠ 0 := by
    intro hzero
    have h := Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero)
    exact hbad (dvd_mul_of_dvd_right h _)
  rw [← rootCount_integralNormalization F hdeg p hlead, ← hmin]
  exact rootCount_minpoly_eq_normPrimes θ p hcond

end BretecheTenenbaumMean
