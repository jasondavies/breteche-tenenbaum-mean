module

public import BretecheTenenbaumMean.PrimeSums.CosineIntegral
public import BretecheTenenbaumMean.PolynomialExpectation

@[expose] public section

/-! # Prime sums on frequency-dependent intervals

The weak upper and strict lower cutoffs match (2.9)–(2.11).
-/

open Real Finset MeasureTheory intervalIntegral

namespace BretecheTenenbaumMean.PrimeSums

/-- `∑_{a < p ≤ b} w(p)/p`; the sum is empty when the endpoints are reversed. -/
noncomputable def primeInterval (a b : ℝ) (w : ℕ → ℝ) : ℝ :=
  ∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if p.Prime then w p / p else 0

/-- A common summation range, also valid when the interval is empty. -/
theorem primeInterval_eq_sum_range {a : ℝ} (ha : 0 ≤ a) (b : ℝ) (w : ℕ → ℝ) :
    primeInterval a b w = ∑ p ∈ range (⌊b⌋₊ + 1),
      if p.Prime ∧ a < (p : ℝ) then w p / p else 0 := by
  have he : Ioc ⌊a⌋₊ ⌊b⌋₊ = (range (⌊b⌋₊ + 1)).filter (fun p : ℕ ↦ a < (p : ℝ)) := by
    ext p
    simp only [mem_Ioc, mem_filter, mem_range, Nat.lt_succ_iff, Nat.floor_lt ha]
    exact and_comm
  rw [primeInterval, he, sum_filter]
  apply sum_congr rfl
  intro p _
  split_ifs <;> simp_all

theorem primeInterval_cos {a b : ℝ} (hab : a ≤ b) (ψ : ℝ) :
    primeInterval a b (fun p ↦ cos (ψ * log p)) = cosinePrimeSum b ψ - cosinePrimeSum a ψ := by
  rw [cosinePrimeSum, cosinePrimeSum, ← sum_Ico_eq_sub _ (by gcongr),
    Finset.Ico_add_one_add_one_eq_Ioc]
  rfl

theorem cosinePrimeSum_zero (x : ℝ) : cosinePrimeSum x 0 = S x := by
  rw [cosinePrimeSum, S_eq_sum]
  simp only [zero_mul, cos_zero, one_div]

/-- The absolute Mertens remainder for weak prime cutoffs. -/
theorem abs_S_sub_loglog_le : ∃ K ≥ 0, ∀ x ≥ 2, |S x - log (log x)| ≤ K := by
  obtain ⟨K, hK0, hK⟩ := cosinePrimeSum_log_ratio
  refine ⟨K, hK0, fun x hx ↦ ?_⟩
  simpa only [cosinePrimeSum_zero, zero_mul, add_zero, div_one] using hK x 0 hx le_rfl (by norm_num)

/-- Logarithmic substitution on an arbitrary interval above two. -/
theorem integral_cosineWeight_eq_interval {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (ψ : ℝ) :
    (∫ t in a..b, cosineWeight ψ t) = ∫ u in log a..log b, cos (ψ * u) / u := by
  have hpos : ∀ t ∈ Set.uIcc a b, 0 < t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    linarith [ht.1]
  have hlog : ContinuousOn log (Set.uIcc a b) :=
    continuousOn_log.mono (fun t ht ↦ by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact (hpos t ht).ne')
  have hsub := integral_comp_mul_deriv_of_deriv_nonneg
    (f := log) (f' := fun t ↦ t⁻¹) (g := fun u ↦ cos (ψ * u) / u) hlog
    (fun t ht ↦ hasDerivAt_log (hpos t (Set.Ioo_subset_Icc_self ht)).ne')
    (fun t ht ↦ inv_nonneg.2 (hpos t (Set.Ioo_subset_Icc_self ht)).le)
  convert hsub using 1
  congr 1
  ext t
  dsimp only [cosineWeight, Function.comp_apply]
  ring

/-- Once `ψ log a ≥ 1`, the cosine prime sum over `(a,b]` is uniformly bounded.
Frequencies up to two cover both the individual and summed frequencies in (2.11). -/
theorem primeInterval_cos_tail : ∃ K ≥ 0, ∀ a b ψ,
    2 ≤ a → a ≤ b → 0 < ψ → ψ ≤ 2 → 1 ≤ ψ * log a →
    |primeInterval a b (fun p ↦ cos (ψ * log p))| ≤ K := by
  obtain ⟨K, hK0, hK⟩ := cosinePrimeSum_interval_error
  refine ⟨K + 3, by positivity, fun a b ψ ha hab hψ hψ2 hosc ↦ ?_⟩
  have hla : 0 < log a := log_pos (by linarith)
  have he := hK a b ψ ha hab (by rwa [abs_of_pos hψ])
  have hi := cosineIntegral_tail hψ hla (log_le_log (by linarith) hab)
  have hi' : |∫ t in a..b, cosineWeight ψ t| ≤ 3 := by
    rw [integral_cosineWeight_eq_interval ha hab]
    refine hi.trans ?_
    rw [div_le_iff₀ (mul_pos hψ hla)]
    linarith
  rw [primeInterval_cos hab]
  calc |cosinePrimeSum b ψ - cosinePrimeSum a ψ|
      ≤ |cosinePrimeSum b ψ - cosinePrimeSum a ψ - (∫ t in a..b, cosineWeight ψ t)| +
        |∫ t in a..b, cosineWeight ψ t| := by
          convert abs_add_le
            (cosinePrimeSum b ψ - cosinePrimeSum a ψ - (∫ t in a..b, cosineWeight ψ t))
            (∫ t in a..b, cosineWeight ψ t) using 1
          congr 1
          ring
    _ ≤ K * pntE a + 3 := add_le_add he hi'
    _ ≤ K + 3 := by nlinarith [pntE_le_one a]

/-- The lower endpoints in §2.2 are always at least two. -/
theorem two_le_exp_inv {ψ : ℝ} (hψ : 0 < ψ) (hψ1 : ψ ≤ 1) : 2 ≤ exp ψ⁻¹ := by
  have h := exp_le_exp.2 ((one_le_inv₀ hψ).2 hψ1)
  have := exp_one_gt_d9
  linarith

end BretecheTenenbaumMean.PrimeSums
