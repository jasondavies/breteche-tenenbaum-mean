module

public import BretecheTenenbaumMean.HigherDegreePrimeIdeals
public import BretecheTenenbaumMean.DedekindPrimeSum

@[expose] public section

/-! # Reindexing the degree-one prime-ideal sum by rational primes -/

namespace BretecheTenenbaumMean

open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The number of prime ideals of a prescribed absolute norm. -/
noncomputable def primeNormCount (n : ℕ) : ℕ :=
  Nat.card {P : HeightOneSpectrum (𝓞 K) // Ideal.absNorm P.asIdeal = n}

abbrev DegreeOnePrime :=
  {P : HeightOneSpectrum (𝓞 K) // P.asIdeal.inertiaDeg ℤ = 1}

noncomputable def degreeOnePrimeBelow (P : DegreeOnePrime K) : Nat.Primes :=
  ⟨rationalPrimeBelow P.val, rationalPrimeBelow_prime P.val⟩

noncomputable def degreeOneFiberEquivNorm (p : Nat.Primes) :
    {P : DegreeOnePrime K // degreeOnePrimeBelow K P = p} ≃
      {P : HeightOneSpectrum (𝓞 K) // Ideal.absNorm P.asIdeal = p.val} where
  toFun P := ⟨P.val.val, (primeIdeal_norm_eq_prime_iff _ p.prop).mpr
    ⟨congrArg Subtype.val P.prop, P.val.prop⟩⟩
  invFun P := ⟨⟨P.val, ((primeIdeal_norm_eq_prime_iff _ p.prop).mp P.prop).2⟩,
    Subtype.ext (((primeIdeal_norm_eq_prime_iff _ p.prop).mp P.prop).1)⟩
  left_inv _P := rfl
  right_inv _P := rfl

instance degreeOneFiber_finite (p : Nat.Primes) :
    Finite {P : DegreeOnePrime K // degreeOnePrimeBelow K P = p} := by
  have : Finite {P : HeightOneSpectrum (𝓞 K) // Ideal.absNorm P.asIdeal = p.val} :=
    ((Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le p.val).subset
      (fun _ h ↦ h.le)).to_subtype
  exact Finite.of_equiv _ (degreeOneFiberEquivNorm K p).symm

/-- Collecting the degree-one ideals above each prime produces the coefficient
`primeNormCount K p`; all series here converge absolutely. -/
theorem degreeOnePrime_sum_eq_primeNorm_sum {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes ↦ (primeNormCount K p.val : ℂ) / (p.val : ℂ) ^ s) ∧
    (∑' P : DegreeOnePrime K, primeIdealDirichletTerm K s P.val) =
      ∑' p : Nat.Primes, (primeNormCount K p.val : ℂ) / (p.val : ℂ) ^ s := by
  classical
  have h := ((summable_primeIdealDirichletTerm K hs).subtype
    (fun P ↦ P.asIdeal.inertiaDeg ℤ = 1)).hasSum.tsum_fiberwise (degreeOnePrimeBelow K)
  have hfiber (p : Nat.Primes) :
      (∑' P : {P : DegreeOnePrime K // degreeOnePrimeBelow K P = p},
        primeIdealDirichletTerm K s P.val.val) = (primeNormCount K p.val : ℂ) / (p.val : ℂ) ^ s := by
    have heval (P : {P : DegreeOnePrime K // degreeOnePrimeBelow K P = p}) :
        primeIdealDirichletTerm K s P.val.val = 1 / (p.val : ℂ) ^ s := by
      have hnorm := ((degreeOneFiberEquivNorm K p) P).prop
      change Ideal.absNorm P.val.val.asIdeal = p.val at hnorm
      unfold primeIdealDirichletTerm
      rw [hnorm]
    simp only [heval]
    rw [tsum_const, nsmul_eq_mul, mul_one_div]
    congr 2
    exact Nat.card_congr (degreeOneFiberEquivNorm K p)
  have h' : HasSum (fun p : Nat.Primes ↦ (primeNormCount K p.val : ℂ) / (p.val : ℂ) ^ s)
      (∑' P : DegreeOnePrime K, primeIdealDirichletTerm K s P.val) :=
    h.congr_fun (fun p ↦ (hfiber p).symm)
  exact ⟨h'.summable, h'.tsum_eq.symm⟩

/-- Removing the higher-degree primes from the full ideal sum costs a
constant independent of `s` in the right half-plane. -/
theorem primeNorm_sum_sub_primeIdeal_sum_bound {s : ℂ} (hs : 1 < s.re) :
    ‖(∑' p : Nat.Primes, (primeNormCount K p.val : ℂ) / (p.val : ℂ) ^ s) -
      ∑' P, primeIdealDirichletTerm K s P‖ ≤
        ∑' P : {P : HeightOneSpectrum (𝓞 K) // P.asIdeal.inertiaDeg ℤ ≠ 1},
          (Ideal.absNorm P.val.asIdeal : ℝ)⁻¹ := by
  have hsplit := (summable_primeIdealDirichletTerm K hs).tsum_subtype_add_tsum_subtype_compl
    {P | P.asIdeal.inertiaDeg ℤ = 1}
  change (∑' P : DegreeOnePrime K, primeIdealDirichletTerm K s P.val) +
      (∑' P : {P : HeightOneSpectrum (𝓞 K) // P.asIdeal.inertiaDeg ℤ ≠ 1},
        primeIdealDirichletTerm K s P.val) = _ at hsplit
  rw [(degreeOnePrime_sum_eq_primeNorm_sum K hs).2] at hsplit
  rw [← hsplit, sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg]
  exact (higherDegree_primeIdeal_sum_bound K hs.le).2

/-- The smoothed prime-norm coefficient sum has the same logarithmic profile
as the full prime-ideal sum. -/
theorem smoothed_primeNorm_sum_log_ratio :
    ∃ B ≥ (0 : ℝ), ∀ x θ : ℝ, Real.exp 1 ≤ x → |θ| ≤ 2 →
      |(∑' p : Nat.Primes, (primeNormCount K p.val : ℂ) /
          (p.val : ℂ) ^ ((1 + (Real.log x)⁻¹ : ℝ) + θ * Complex.I)).re -
        Real.log (Real.log x / (1 + |θ| * Real.log x))| ≤ B := by
  obtain ⟨B, hB, hb⟩ := smoothed_primeIdeal_sum_log_ratio K
  let E := ∑' P : {P : HeightOneSpectrum (𝓞 K) // P.asIdeal.inertiaDeg ℤ ≠ 1},
    (Ideal.absNorm P.val.asIdeal : ℝ)⁻¹
  have hE : 0 ≤ E := tsum_nonneg (fun _ ↦ by positivity)
  refine ⟨B + E, by positivity, fun x θ hx hθ ↦ ?_⟩
  have hl : 0 < Real.log x := Real.log_pos ((Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hx)
  have hs : 1 < (((1 + (Real.log x)⁻¹ : ℝ) : ℂ) + θ * Complex.I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    exact lt_add_of_pos_right _ (inv_pos.mpr hl)
  have hdiff := primeNorm_sum_sub_primeIdeal_sum_bound K hs
  have hre := (Complex.abs_re_le_norm _).trans hdiff
  have hmain := hb x θ hx hθ
  simp only [Complex.sub_re] at hre
  have htriangle := (abs_sub_le _ _ _).trans (add_le_add hre hmain)
  simpa only [add_comm] using htriangle

end BretecheTenenbaumMean
