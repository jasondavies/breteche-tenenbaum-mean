module

public import BretecheTenenbaumMean.PolynomialPrimeIdeals
public import BretecheTenenbaumMean.PrimeNormDirichlet
public import BretecheTenenbaumMean.FinitePrimeCorrections

@[expose] public section

/-! # The smoothed prime sum of polynomial root counts -/

namespace BretecheTenenbaumMean

/-- The polynomial root-count Dirichlet series has the logarithmic profile
required for the weighted mean theorem, with smoothing scale `1/log x`.
This holds for every irreducible nonconstant integer polynomial, including
nonmonic polynomials and those with fixed prime divisors. -/
theorem smoothed_polynomialRoot_sum_log_ratio (F : Polynomial ℤ)
    (hF : Irreducible F) (hdeg : 0 < F.natDegree) :
    ∃ B ≥ (0 : ℝ), ∀ x θ : ℝ, Real.exp 1 ≤ x → |θ| ≤ 2 →
      Summable (fun p : Nat.Primes ↦ (NairTenenbaum.rootCount F p.val : ℂ) /
        (p.val : ℂ) ^ ((1 + (Real.log x)⁻¹ : ℝ) + θ * Complex.I)) ∧
      |(∑' p : Nat.Primes, (NairTenenbaum.rootCount F p.val : ℂ) /
          (p.val : ℂ) ^ ((1 + (Real.log x)⁻¹ : ℝ) + θ * Complex.I)).re -
        Real.log (Real.log x / (1 + |θ| * Real.log x))| ≤ B := by
  classical
  obtain ⟨K, hK, hNF, N, hN, hgood⟩ := exists_numberField_rootCount_eq_normPrimes F hF hdeg
  have hfinite : Set.Finite {p : Nat.Primes | p.val ≤ N} :=
    Set.Finite.preimage Nat.Primes.coe_nat_injective.injOn (Set.finite_Iic N)
  let S := hfinite.toFinset
  let a : Nat.Primes → ℂ := fun p ↦ NairTenenbaum.rootCount F p.val
  let b : Nat.Primes → ℂ := fun p ↦ primeNormCount K p.val
  have hab : ∀ p, p ∉ S → a p = b p := by
    intro p hp
    have hpN : ¬ p.val ≤ N := by simpa [S] using hp
    have hndvd : ¬ p.val ∣ N := fun h ↦ hpN (Nat.le_of_dvd hN h)
    change (NairTenenbaum.rootCount F p.val : ℂ) =
      (Nat.card {P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
        Ideal.absNorm P.asIdeal = p.val} : ℂ)
    exact_mod_cast hgood p.val p.prop hndvd
  obtain ⟨C, hC, hcorr⟩ := finite_primeDirichlet_correction a b S hab
  obtain ⟨B, hB, hbound⟩ := smoothed_primeNorm_sum_log_ratio K
  refine ⟨B + C, by positivity, fun x θ hx hθ ↦ ?_⟩
  have hl : 0 < Real.log x := Real.log_pos ((Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hx)
  let s : ℂ := ((1 + (Real.log x)⁻¹ : ℝ) : ℂ) + θ * Complex.I
  have hs : 1 < s.re := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    exact lt_add_of_pos_right _ (inv_pos.mpr hl)
  obtain ⟨ha, hdiff⟩ := hcorr s hs.le (degreeOnePrime_sum_eq_primeNorm_sum K hs).1
  refine ⟨ha, ?_⟩
  have hre := (Complex.abs_re_le_norm _).trans hdiff
  simp only [Complex.sub_re] at hre
  have hmain := hbound x θ hx hθ
  have htriangle := (abs_sub_le _ _ _).trans (add_le_add hre hmain)
  simpa only [a, s, add_comm] using htriangle

end BretecheTenenbaumMean
