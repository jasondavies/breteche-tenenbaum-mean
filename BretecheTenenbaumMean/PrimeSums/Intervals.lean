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

theorem primeInterval_add (a b : ℝ) (v w : ℕ → ℝ) :
    primeInterval a b (fun p ↦ v p + w p) = primeInterval a b v + primeInterval a b w := by
  unfold primeInterval
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  split_ifs <;> simp only [add_div, zero_add]

theorem primeInterval_const_mul (a b c : ℝ) (w : ℕ → ℝ) :
    primeInterval a b (fun p ↦ c * w p) = c * primeInterval a b w := by
  unfold primeInterval
  rw [mul_sum]
  apply sum_congr rfl
  intro p _
  split_ifs <;> ring

theorem primeInterval_cos {a b : ℝ} (hab : a ≤ b) (ψ : ℝ) :
    primeInterval a b (fun p ↦ cos (ψ * log p)) = cosinePrimeSum b ψ - cosinePrimeSum a ψ := by
  rw [cosinePrimeSum, cosinePrimeSum, ← sum_Ico_eq_sub _ (by gcongr),
    Finset.Ico_add_one_add_one_eq_Ioc]
  rfl

theorem cosinePrimeSum_zero (x : ℝ) : cosinePrimeSum x 0 = S x := by
  rw [cosinePrimeSum, S_eq_sum]
  simp only [zero_mul, cos_zero, one_div]

theorem primeInterval_one {a b : ℝ} (hab : a ≤ b) :
    primeInterval a b (fun _ ↦ 1) = S b - S a := by
  simpa only [zero_mul, cos_zero, cosinePrimeSum_zero] using primeInterval_cos hab 0

/-- The absolute Mertens remainder for weak prime cutoffs. -/
theorem abs_S_sub_loglog_le : ∃ K ≥ 0, ∀ x ≥ 2, |S x - log (log x)| ≤ K := by
  obtain ⟨K, hK0, hK⟩ := cosinePrimeSum_log_ratio
  refine ⟨K, hK0, fun x hx ↦ ?_⟩
  simpa only [cosinePrimeSum_zero, zero_mul, add_zero, div_one] using hK x 0 hx le_rfl (by norm_num)

/-- Mertens' estimate on any interval above two. -/
theorem primeInterval_one_error : ∃ K ≥ 0, ∀ a b,
    2 ≤ a → a ≤ b →
    |primeInterval a b (fun _ ↦ 1) - log (log b / log a)| ≤ K := by
  obtain ⟨K, hK0, hK⟩ := abs_S_sub_loglog_le
  refine ⟨2 * K, by positivity, fun a b ha hab ↦ ?_⟩
  have hb := ha.trans hab
  have h1 := abs_le.1 (hK a ha)
  have h2 := abs_le.1 (hK b hb)
  rw [primeInterval_one hab, log_div (log_pos (by linarith : 1 < b)).ne'
    (log_pos (by linarith : 1 < a)).ne', abs_le]
  constructor <;> linarith

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

/-- Estimate (2.9), with an absolute error constant. -/
theorem primeSum_U1 : ∃ K ≥ 0, ∀ φ,
    0 < φ → φ ≤ 1 → S (exp φ⁻¹) ≤ log φ⁻¹ + K := by
  obtain ⟨K, hK0, hK⟩ := abs_S_sub_loglog_le
  refine ⟨K, hK0, fun φ hφ hφ1 ↦ ?_⟩
  have h := (abs_le.1 (hK (exp φ⁻¹) (two_le_exp_inv hφ hφ1))).2
  rw [log_exp] at h
  linarith

/-- Estimate (2.10), uniformly for `0 < θ ≤ φ ≤ 1`. -/
theorem primeSum_U2 : ∃ K ≥ 0, ∀ θ φ,
    0 < θ → θ ≤ φ → φ ≤ 1 →
    primeInterval (exp φ⁻¹) (exp θ⁻¹) (fun p ↦ 1 + cos (φ * log p)) ≤
      log (φ / θ) + K := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := primeInterval_one_error
  obtain ⟨K₂, hK₂0, hK₂⟩ := primeInterval_cos_tail
  refine ⟨K₁ + K₂, by positivity, fun θ φ hθ hθφ hφ1 ↦ ?_⟩
  have hφ : 0 < φ := hθ.trans_le hθφ
  have ha := two_le_exp_inv hφ hφ1
  have hab : exp φ⁻¹ ≤ exp θ⁻¹ := exp_le_exp.2 (inv_anti₀ hθ hθφ)
  have h1 := (abs_le.1 (hK₁ _ _ ha hab)).2
  have h2 := (abs_le.1 (hK₂ _ _ φ ha hab hφ (by linarith) (by
    rw [log_exp, mul_inv_cancel₀ hφ.ne']))).2
  rw [log_exp, log_exp, inv_div_inv] at h1
  rw [primeInterval_add]
  linarith

/-- Interval version of the full cosine asymptotic, including zero frequency. -/
theorem primeInterval_cos_error : ∃ K ≥ 0, ∀ a b ψ,
    2 ≤ a → a ≤ b → 0 ≤ ψ → ψ ≤ 1 →
    |primeInterval a b (fun p ↦ cos (ψ * log p)) -
      (log (log b / (1 + ψ * log b)) - log (log a / (1 + ψ * log a)))| ≤ K := by
  obtain ⟨K, hK0, hK⟩ := cosinePrimeSum_log_ratio
  refine ⟨2 * K, by positivity, fun a b ψ ha hab hψ hψ1 ↦ ?_⟩
  have h1 := abs_le.1 (hK a ψ ha hψ hψ1)
  have h2 := abs_le.1 (hK b ψ (ha.trans hab) hψ hψ1)
  rw [primeInterval_cos hab, abs_le]
  constructor <;> linarith

/-- The difference-frequency contribution in (2.11), including `φ = θ`. -/
theorem primeInterval_difference_frequency : ∃ K ≥ 0, ∀ x θ φ,
    0 < θ → θ ≤ φ → φ ≤ 1 → exp θ⁻¹ ≤ x →
    |primeInterval (exp θ⁻¹) x (fun p ↦ cos ((φ - θ) * log p)) -
      log (φ * log x / (1 + (φ - θ) * log x))| ≤ K := by
  obtain ⟨K, hK0, hK⟩ := primeInterval_cos_error
  refine ⟨K, hK0, fun x θ φ hθ hθφ hφ1 hx ↦ ?_⟩
  have hφ : 0 < φ := hθ.trans_le hθφ
  have ha := two_le_exp_inv hθ (hθφ.trans hφ1)
  have hx2 : 2 ≤ x := ha.trans hx
  have hlx : 0 < log x := log_pos (by linarith)
  have hd : 0 ≤ φ - θ := sub_nonneg.2 hθφ
  have hp : 0 < 1 + (φ - θ) * log x := by positivity
  have h := hK (exp θ⁻¹) x (φ - θ) ha hx hd (by linarith)
  rw [log_exp] at h
  have he : θ⁻¹ / (1 + (φ - θ) * θ⁻¹) = φ⁻¹ := by
    field_simp
    ring
  rw [he] at h
  have he' : log (log x / (1 + (φ - θ) * log x)) - log φ⁻¹ =
      log (φ * log x / (1 + (φ - θ) * log x)) := by
    rw [← log_div (div_pos hlx hp).ne' (inv_ne_zero hφ.ne')]
    congr 1
    field_simp
  rwa [he'] at h

/-- The cosine product expansion summed over an interval of primes. -/
theorem primeInterval_cos_product (a b θ φ : ℝ) :
    primeInterval a b (fun p ↦ (1 + cos (θ * log p)) * (1 + cos (φ * log p))) =
      primeInterval a b (fun _ ↦ 1) +
      primeInterval a b (fun p ↦ cos (θ * log p)) +
      primeInterval a b (fun p ↦ cos (φ * log p)) +
      (1 / 2) * primeInterval a b (fun p ↦ cos ((φ - θ) * log p)) +
      (1 / 2) * primeInterval a b (fun p ↦ cos ((φ + θ) * log p)) := by
  simp_rw [cosine_product_identity, ← sub_mul, ← add_mul]
  simp only [primeInterval_add, primeInterval_const_mul]

/-- Estimate (2.11) in its range of application `exp(1/θ) ≤ x`.
The error constant is uniform, including along the diagonal `φ = θ`. -/
theorem primeSum_U3 : ∃ K ≥ 0, ∀ x θ φ,
    0 < θ → θ ≤ φ → φ ≤ 1 → exp θ⁻¹ ≤ x →
    primeInterval (exp θ⁻¹) x
      (fun p ↦ (1 + cos (θ * log p)) * (1 + cos (φ * log p))) ≤
      log (1 + θ * log x) + (1 / 2) * log (φ * log x / (1 + (φ - θ) * log x)) + K := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := primeInterval_one_error
  obtain ⟨K₂, hK₂0, hK₂⟩ := primeInterval_cos_tail
  obtain ⟨K₃, hK₃0, hK₃⟩ := primeInterval_difference_frequency
  refine ⟨K₁ + 3 * K₂ + K₃, by positivity, fun x θ φ hθ hθφ hφ1 hx ↦ ?_⟩
  have hφ : 0 < φ := hθ.trans_le hθφ
  have hθ1 : θ ≤ 1 := hθφ.trans hφ1
  have ha := two_le_exp_inv hθ hθ1
  have hx2 : 2 ≤ x := ha.trans hx
  have hlx : 0 < log x := log_pos (by linarith)
  have h1 := (abs_le.1 (hK₁ (exp θ⁻¹) x ha hx)).2
  rw [log_exp, div_inv_eq_mul, mul_comm (log x) θ] at h1
  have hmain : log (θ * log x) ≤ log (1 + θ * log x) :=
    log_le_log (mul_pos hθ hlx) (by linarith)
  have hosc : ∀ ψ, θ ≤ ψ → 1 ≤ ψ * log (exp θ⁻¹) := by
    intro ψ hθψ
    rw [log_exp]
    calc 1 = θ * θ⁻¹ := (mul_inv_cancel₀ hθ.ne').symm
         _ ≤ ψ * θ⁻¹ := mul_le_mul_of_nonneg_right hθψ (inv_nonneg.2 hθ.le)
  have h2 := (abs_le.1 (hK₂ (exp θ⁻¹) x θ ha hx hθ (by linarith) (hosc θ le_rfl))).2
  have h3 := (abs_le.1 (hK₂ (exp θ⁻¹) x φ ha hx hφ (by linarith) (hosc φ hθφ))).2
  have h4 := (abs_le.1 (hK₃ x θ φ hθ hθφ hφ1 hx)).2
  have h5 := (abs_le.1 (hK₂ (exp θ⁻¹) x (φ + θ) ha hx (by positivity)
    (by linarith) (hosc (φ + θ) (by linarith)))).2
  rw [primeInterval_cos_product]
  linarith

end BretecheTenenbaumMean.PrimeSums
