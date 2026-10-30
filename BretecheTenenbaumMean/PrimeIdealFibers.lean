module

public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.Algebra.CharZero.Infinite

@[expose] public section

/-! # Rational primes below prime ideals and bounds for their fibers -/

namespace BretecheTenenbaumMean

open NumberField IsDedekindDomain
open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The rational prime below a nonzero prime ideal. -/
noncomputable def rationalPrimeBelow (P : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Ideal.absNorm (P.asIdeal.under ℤ)

omit [NumberField K] in
theorem rationalPrimeBelow_prime (P : HeightOneSpectrum (𝓞 K)) :
    (rationalPrimeBelow P).Prime := by
  let : NeZero P.asIdeal := ⟨P.ne_bot⟩
  exact Nat.absNorm_under_prime P.asIdeal

theorem primeIdeal_norm_eq_pow (P : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm P.asIdeal = rationalPrimeBelow P ^ P.asIdeal.inertiaDeg ℤ :=
  (Ideal.absNorm_pow_inertiaDeg (P.asIdeal.under ℤ) P.asIdeal).symm

/-- The fiber over a rational prime is the usual set of ideals lying over `(p)`. -/
noncomputable def rationalPrimeFiberEquiv (p : ℕ) [Fact p.Prime] :
    {P : HeightOneSpectrum (𝓞 K) // rationalPrimeBelow P = p} ≃
      Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K) where
  toFun P := ⟨P.val.asIdeal, P.val.isPrime, ⟨by
    exact (congrArg (fun n : ℕ ↦ Ideal.span {(n : ℤ)}) P.prop).symm.trans
      (Int.ideal_span_absNorm_eq_self _)⟩⟩
  invFun Q := ⟨⟨Q.val, Q.prop.1,
    Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(p : ℤ)})
      (by simp [NeZero.ne p]) Q.val⟩, by
        change Ideal.absNorm (Q.val.under ℤ) = p
        rw [← Q.prop.2.over]
        simp⟩
  left_inv P := by cases P; rfl
  right_inv Q := rfl

/-- Each prime ideal contributes a positive term to the fundamental identity
`sum e(P/p) f(P/p) = [K:ℚ]`. -/
theorem card_primesOver_le_degree (p : ℕ) [Fact p.Prime] :
    Nat.card (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) ≤ Module.finrank ℚ K := by
  classical
  let I : Ideal ℤ := Ideal.span {(p : ℤ)}
  calc
    Nat.card (I.primesOver (𝓞 K)) = ∑ _Q : I.primesOver (𝓞 K), 1 := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ ∑ Q : I.primesOver (𝓞 K), Q.val.ramificationIdx ℤ * Q.val.inertiaDeg ℤ := by
      apply Finset.sum_le_sum
      intro Q _
      exact Nat.mul_pos (Ideal.ramificationIdx_pos ℤ Q.val) (Ideal.inertiaDeg_pos Q.val ℤ)
    _ = Module.finrank ℤ (𝓞 K) := Ideal.sum_ramification_inertia_eq_finrank I (𝓞 K)
    _ = Module.finrank ℚ K := NumberField.RingOfIntegers.rank K

theorem card_rationalPrimeFiber_le_degree (p : ℕ) [Fact p.Prime] :
    Nat.card {P : HeightOneSpectrum (𝓞 K) // rationalPrimeBelow P = p} ≤
      Module.finrank ℚ K := by
  rw [Nat.card_congr (rationalPrimeFiberEquiv (K := K) p)]
  exact card_primesOver_le_degree p

instance rationalPrimeFiber_finite (p : ℕ) :
    Finite {P : HeightOneSpectrum (𝓞 K) // rationalPrimeBelow P = p} := by
  by_cases hp : p.Prime
  · let : Fact p.Prime := ⟨hp⟩
    exact Finite.of_equiv _ (rationalPrimeFiberEquiv (K := K) p).symm
  · have : IsEmpty {P : HeightOneSpectrum (𝓞 K) // rationalPrimeBelow P = p} :=
      ⟨fun P ↦ hp (P.prop ▸ rationalPrimeBelow_prime P.val)⟩
    infer_instance

theorem card_rationalPrimeFiber_le_degree_all (p : ℕ) :
    Nat.card {P : HeightOneSpectrum (𝓞 K) // rationalPrimeBelow P = p} ≤
      Module.finrank ℚ K := by
  by_cases hp : p.Prime
  · let : Fact p.Prime := ⟨hp⟩
    exact card_rationalPrimeFiber_le_degree p
  · have : IsEmpty {P : HeightOneSpectrum (𝓞 K) // rationalPrimeBelow P = p} :=
      ⟨fun P ↦ hp (P.prop ▸ rationalPrimeBelow_prime P.val)⟩
    simp

/-- A prime ideal of residue degree at least two has norm at least the square
of the rational prime below it. -/
theorem primeIdeal_norm_ge_sq (P : HeightOneSpectrum (𝓞 K))
    (hP : P.asIdeal.inertiaDeg ℤ ≠ 1) :
    rationalPrimeBelow P ^ 2 ≤ Ideal.absNorm P.asIdeal := by
  rw [primeIdeal_norm_eq_pow]
  have hpos := Ideal.inertiaDeg_pos P.asIdeal ℤ
  exact Nat.pow_le_pow_right (rationalPrimeBelow_prime P).pos (by omega)

/-- Norm equal to a rational prime is equivalent to lying above that prime
with residue degree one. -/
theorem primeIdeal_norm_eq_prime_iff (P : HeightOneSpectrum (𝓞 K))
    {p : ℕ} (hp : p.Prime) :
    Ideal.absNorm P.asIdeal = p ↔
      rationalPrimeBelow P = p ∧ P.asIdeal.inertiaDeg ℤ = 1 := by
  constructor
  · intro hnorm
    have hdvd : rationalPrimeBelow P ∣ p := by
      rw [← hnorm]
      exact Int.absNorm_under_dvd_absNorm P.asIdeal
    have hbase : rationalPrimeBelow P = p :=
      ((Nat.dvd_prime hp).mp hdvd).resolve_left (rationalPrimeBelow_prime P).ne_one
    refine ⟨hbase, ?_⟩
    apply Nat.pow_right_injective hp.two_le
    simpa [hbase] using (primeIdeal_norm_eq_pow P).symm.trans hnorm
  · rintro ⟨hbase, hdegree⟩
    rw [primeIdeal_norm_eq_pow, hbase, hdegree, pow_one]

/-- The degree-one ideals above `p` are exactly the prime ideals of norm `p`. -/
noncomputable def degreeOnePrimesEquivNormPrimes (p : ℕ) [Fact p.Prime] :
    {Q : Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K) //
      Ideal.inertiaDeg Q.val ℤ = 1} ≃
    {P : HeightOneSpectrum (𝓞 K) // Ideal.absNorm P.asIdeal = p} := by
  let e := rationalPrimeFiberEquiv (K := K) p
  refine
    { toFun := fun Q ↦ ⟨(e.symm Q.val).val, ?_⟩
      invFun := fun P ↦ ⟨e ⟨P.val, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact (primeIdeal_norm_eq_prime_iff _ (Fact.out : p.Prime)).mpr
      ⟨(e.symm Q.val).prop, Q.prop⟩
  · exact ((primeIdeal_norm_eq_prime_iff _ (Fact.out : p.Prime)).mp P.prop).1
  · exact ((primeIdeal_norm_eq_prime_iff _ (Fact.out : p.Prime)).mp P.prop).2
  · intro Q
    apply Subtype.ext
    exact e.apply_symm_apply Q.val
  · intro P
    rfl

end BretecheTenenbaumMean
