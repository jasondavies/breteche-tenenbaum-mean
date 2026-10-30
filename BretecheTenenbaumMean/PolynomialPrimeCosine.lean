module

public import BretecheTenenbaumMean.BoundedPrimeUnsmoothing
public import BretecheTenenbaumMean.PolynomialPrimeMean

@[expose] public section

/-! # The uniform polynomial root-count cosine prime estimate -/

namespace BretecheTenenbaumMean

open Real Finset Polynomial

/-- Removal of smoothing yields the root-count cosine estimate for `x ≥ e`. -/
theorem polynomialRoot_cosine_bound_large (F : ℤ[X]) (hI : Irreducible F)
    (hF : NairTenenbaum.NoFixedPrimeDivisor F) :
    ∃ B ≥ (0 : ℝ), ∀ x θ : ℝ, exp 1 ≤ x → |θ| ≤ 2 →
      |WeightedModel.cosinePrimeSum (polynomialRootWeight F) x θ -
        log (log x / (1 + |θ| * log x))| ≤ B := by
  have hdeg : 0 < F.natDegree := by
    have h := (hF.irreducible_map hI).natDegree_pos
    simpa only [natDegree_map_eq_of_injective (f := Int.castRingHom ℚ) Int.cast_injective] using h
  obtain ⟨C, hC, hu⟩ := bounded_prime_unsmoothing
  obtain ⟨B, hB, hb⟩ := smoothed_polynomialRoot_sum_log_ratio F hI hdeg
  refine ⟨(F.natDegree : ℝ) * C + B, by positivity, fun x θ hx hθ ↦ ?_⟩
  let f : Nat.Primes → ℝ := fun p ↦ (NairTenenbaum.rootCount F p.val : ℝ) * cos (θ * log p.val)
  have hf (p : Nat.Primes) : |f p| ≤ (F.natDegree : ℝ) := by
    dsimp [f]
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    calc
      _ ≤ (NairTenenbaum.rootCount F p.val : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (abs_cos_le_one _) (Nat.cast_nonneg _)
      _ ≤ (F.natDegree : ℝ) := by
        rw [mul_one]
        exact_mod_cast NairTenenbaum.rootCount_le_degree hF p.prop
  obtain ⟨_hd, hdiff⟩ := hu x hx f F.natDegree (Nat.cast_nonneg _) hf
  have hfinite : (∑ p ∈ primeCutoff x, f p / p.val) =
      WeightedModel.cosinePrimeSum (polynomialRootWeight F) x θ := by
    exact sum_primeCutoff x (fun p ↦ (NairTenenbaum.rootCount F p : ℝ) * cos (θ * log p) / p)
  obtain ⟨hs, hmain⟩ := hb x θ hx hθ
  have hre : (∑' p : Nat.Primes, (NairTenenbaum.rootCount F p.val : ℂ) /
      (p.val : ℂ) ^ ((1 + (log x)⁻¹ : ℝ) + θ * Complex.I)).re =
        ∑' p : Nat.Primes, f p * primeDamping x p.val := by
    rw [Complex.re_tsum hs]
    apply tsum_congr
    intro p
    have hp : (0 : ℝ) < p.val := Nat.cast_pos.mpr p.prop.pos
    have h := real_primeDirichlet_term (NairTenenbaum.rootCount F p.val : ℝ) p.val (log x)⁻¹ θ hp
    simp only [Complex.ofReal_natCast] at h
    rw [h]
    dsimp [f, primeDamping]
    ring
  rw [hre] at hmain
  rw [hfinite] at hdiff
  exact (abs_sub_le _ _ _).trans (add_le_add hdiff hmain)

/-- The logarithmic profile is bounded on the initial range. -/
theorem cosine_log_profile_small_bound {x θ : ℝ} (hx : 2 ≤ x) (hxe : x ≤ exp 1)
    (hθ : |θ| ≤ 2) :
    |log (log x / (1 + |θ| * log x))| ≤ |log (log 2 / 3)| := by
  have hx0 : 0 < x := by linarith
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlx : log 2 ≤ log x := log_le_log (by norm_num) hx
  have hlx1 : log x ≤ 1 := (log_le_iff_le_exp hx0).mpr hxe
  have hlx0 : 0 < log x := hl2.trans_le hlx
  have hden : 0 < 1 + |θ| * log x := by positivity
  have hden1 : 1 ≤ 1 + |θ| * log x :=
    le_add_of_nonneg_right (mul_nonneg (abs_nonneg θ) hlx0.le)
  have hden3 : 1 + |θ| * log x ≤ 3 := by nlinarith [abs_nonneg θ]
  have hratio0 : 0 < log x / (1 + |θ| * log x) := div_pos (by linarith) hden
  have hratio1 : log x / (1 + |θ| * log x) ≤ 1 :=
    (div_le_one hden).mpr (hlx1.trans hden1)
  have hratiol : log 2 / 3 ≤ log x / (1 + |θ| * log x) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hden).mpr
    nlinarith
  have hlogl := log_le_log (by positivity : 0 < log 2 / 3) hratiol
  have hlogu : log (log x / (1 + |θ| * log x)) ≤ 0 := log_nonpos hratio0.le hratio1
  rw [abs_of_nonpos hlogu]
  exact (neg_le_neg hlogl).trans (neg_le_abs _)

/-- The finite cosine sum is uniformly bounded for `2 ≤ x ≤ e`. -/
theorem polynomialRoot_cosine_bound_small (F : ℤ[X]) :
    ∃ B ≥ (0 : ℝ), ∀ x θ : ℝ, 2 ≤ x → x ≤ exp 1 → |θ| ≤ 2 →
      |WeightedModel.cosinePrimeSum (polynomialRootWeight F) x θ -
        log (log x / (1 + |θ| * log x))| ≤ B := by
  let M := ∑ p ∈ primesLT (exp 1), (NairTenenbaum.rootCount F p : ℝ) / p
  have hM : 0 ≤ M := sum_nonneg (fun _ _ ↦ by positivity)
  refine ⟨M + |log (log 2 / 3)|, by positivity, fun x θ hx hxe hθ ↦ ?_⟩
  have hsum : |WeightedModel.cosinePrimeSum (polynomialRootWeight F) x θ| ≤ M := by
    unfold WeightedModel.cosinePrimeSum
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ p ∈ primesLT x, (NairTenenbaum.rootCount F p : ℝ) / p := by
        apply sum_le_sum
        intro p _
        have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
        rw [abs_div, abs_mul]
        simp only [abs_of_nonneg ((polynomialRootWeight F).nonneg p), abs_of_nonneg hp0]
        exact div_le_div_of_nonneg_right (by
          simpa using mul_le_mul_of_nonneg_left (abs_cos_le_one (θ * log p))
            ((polynomialRootWeight F).nonneg p)) (Nat.cast_nonneg p)
      _ ≤ M := sum_le_sum_of_subset_of_nonneg (PrimeSums.primesLT_mono hxe)
        (fun _ _ _ ↦ by positivity)
  exact (abs_sub _ _).trans (add_le_add hsum (cosine_log_profile_small_bound hx hxe hθ))

/-- The complete arithmetic prime estimate needed by the weighted proof. -/
theorem polynomialPrimeCosineEstimates : PolynomialPrimeCosineEstimates := by
  intro F hI hF
  obtain ⟨B, hB, hb⟩ := polynomialRoot_cosine_bound_large F hI hF
  obtain ⟨C, hC, hc⟩ := polynomialRoot_cosine_bound_small F
  refine ⟨B + C, by positivity, fun x θ hx hθ ↦ ?_⟩
  by_cases hxe : exp 1 ≤ x
  · exact (hb x θ hxe hθ).trans (le_add_of_nonneg_right hC)
  · exact (hc x θ hx (le_of_not_ge hxe) hθ).trans (le_add_of_nonneg_left hB)

/-- Equation (1.7), including all irreducible integer polynomials and fixed
prime divisors, with no prime-sum hypothesis remaining. -/
theorem polynomialMeanBound : PolynomialMeanBound :=
  polynomialMeanBound_of_prime_cosine_estimates polynomialPrimeCosineEstimates

end BretecheTenenbaumMean
