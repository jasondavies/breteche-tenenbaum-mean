module

public import BretecheTenenbaumMean.WeightedPrimeEstimates

@[expose] public section

/-! # Weighted prime intervals for the high-frequency argument

Every interval is half open, `[a,b)`, matching the squarefree probability
model. All arithmetic hypotheses are supplied through `PrimeEstimates`.
-/

namespace BretecheTenenbaumMean.WeightedModel

open Real Finset

noncomputable def halfOpenPrimeSum (w : MultiplicativeWeight) (a b : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑ p ∈ (primesLT b).filter (fun p : ℕ ↦ a ≤ (p : ℝ)), w p * f p / p

theorem halfOpenPrimeSum_add (w : MultiplicativeWeight) (a b : ℝ) (f g : ℕ → ℝ) :
    halfOpenPrimeSum w a b (fun p ↦ f p + g p) =
      halfOpenPrimeSum w a b f + halfOpenPrimeSum w a b g := by
  simp only [halfOpenPrimeSum, mul_add, add_div, sum_add_distrib]

theorem halfOpenPrimeSum_const_mul (w : MultiplicativeWeight) (a b c : ℝ) (f : ℕ → ℝ) :
    halfOpenPrimeSum w a b (fun p ↦ c * f p) = c * halfOpenPrimeSum w a b f := by
  unfold halfOpenPrimeSum
  rw [mul_sum]
  apply sum_congr rfl
  intro p _
  ring

theorem PrimeEstimates.interval_cos_error {w : MultiplicativeWeight} (h : PrimeEstimates w)
    {a b ψ : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (hψ : 0 ≤ ψ) (hψ2 : ψ ≤ 2) :
    |halfOpenPrimeSum w a b (fun p ↦ cos (ψ * log p)) -
      (log (log b / (1 + ψ * log b)) - log (log a / (1 + ψ * log a)))| ≤ 2 * h.errorBound := by
  have h1 := abs_le.1 (h.cosine_error a ψ ha (by rwa [abs_of_nonneg hψ]))
  have h2 := abs_le.1 (h.cosine_error b ψ (ha.trans hab) (by rwa [abs_of_nonneg hψ]))
  rw [abs_of_nonneg hψ] at h1 h2
  rw [halfOpenPrimeSum, cosine_tail_eq_sub w hab, abs_le]
  constructor <;> linarith

theorem PrimeEstimates.interval_one_error {w : MultiplicativeWeight} (h : PrimeEstimates w)
    {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    |halfOpenPrimeSum w a b (fun _ ↦ 1) - log (log b / log a)| ≤ 2 * h.errorBound := by
  have hLa : 0 < log a := log_pos (by linarith)
  have hLb : 0 < log b := log_pos (by linarith)
  have he := h.interval_cos_error ha hab (ψ := 0) le_rfl (by norm_num)
  simpa only [zero_mul, cos_zero, add_zero, div_one, log_div hLb.ne' hLa.ne'] using he

/-- After the oscillation scale, the logarithmic main term varies by at most
`log 2`; the two endpoint errors are retained explicitly. -/
theorem PrimeEstimates.interval_cos_tail_le {w : MultiplicativeWeight} (h : PrimeEstimates w)
    {a b ψ : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (hψ : 0 < ψ) (hψ2 : ψ ≤ 2)
    (hosc : 1 ≤ ψ * log a) :
    halfOpenPrimeSum w a b (fun p ↦ cos (ψ * log p)) ≤ 2 * h.errorBound + log 2 := by
  have hLa : 0 < log a := log_pos (by linarith)
  have hLb : 0 < log b := log_pos (by linarith)
  have hda : 0 < 1 + ψ * log a := by positivity
  have hdb : 0 < 1 + ψ * log b := by positivity
  have hr : log b / (1 + ψ * log b) ≤ 2 * (log a / (1 + ψ * log a)) := by
    rw [← mul_div_assoc, div_le_div_iff₀ hdb hda]
    nlinarith [mul_nonneg (sub_nonneg.2 hosc) hLb.le]
  have hh := log_le_log (div_pos hLb hdb) hr
  rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) (div_pos hLa hda).ne'] at hh
  have he := (abs_le.1 (h.interval_cos_error ha hab hψ.le hψ2)).2
  linarith

/-- The difference-frequency term, uniformly including the diagonal. -/
theorem PrimeEstimates.interval_difference_frequency {w : MultiplicativeWeight}
    (h : PrimeEstimates w) {x θ φ : ℝ}
    (hθ : 0 < θ) (hθφ : θ ≤ φ) (hφ1 : φ ≤ 1) (hx : exp θ⁻¹ ≤ x) :
    |halfOpenPrimeSum w (exp θ⁻¹) x (fun p ↦ cos ((φ - θ) * log p)) -
      log (φ * log x / (1 + (φ - θ) * log x))| ≤ 2 * h.errorBound := by
  have hφ : 0 < φ := hθ.trans_le hθφ
  have ha := PrimeSums.two_le_exp_inv hθ (hθφ.trans hφ1)
  have hx2 := ha.trans hx
  have hlx : 0 < log x := log_pos (by linarith)
  have hd : 0 ≤ φ - θ := sub_nonneg.2 hθφ
  have hp : 0 < 1 + (φ - θ) * log x := by positivity
  have he := h.interval_cos_error ha hx hd (by linarith)
  rw [log_exp] at he
  have hratio : θ⁻¹ / (1 + (φ - θ) * θ⁻¹) = φ⁻¹ := by field_simp; ring
  rw [hratio] at he
  have hlog : log (log x / (1 + (φ - θ) * log x)) - log φ⁻¹ =
      log (φ * log x / (1 + (φ - θ) * log x)) := by
    rw [← log_div (div_pos hlx hp).ne' (inv_ne_zero hφ.ne')]
    congr 1
    field_simp
  rwa [hlog] at he

theorem halfOpen_cos_product (w : MultiplicativeWeight) (a b θ φ : ℝ) :
    halfOpenPrimeSum w a b (fun p ↦ (1 + cos (θ * log p)) * (1 + cos (φ * log p))) =
      halfOpenPrimeSum w a b (fun _ ↦ 1) +
      halfOpenPrimeSum w a b (fun p ↦ cos (θ * log p)) +
      halfOpenPrimeSum w a b (fun p ↦ cos (φ * log p)) +
      (1 / 2) * halfOpenPrimeSum w a b (fun p ↦ cos ((φ - θ) * log p)) +
      (1 / 2) * halfOpenPrimeSum w a b (fun p ↦ cos ((φ + θ) * log p)) := by
  simp_rw [cosine_product_identity, ← sub_mul, ← add_mul]
  simp only [halfOpenPrimeSum_add, halfOpenPrimeSum_const_mul]

/-- The middle prime range in the high-frequency product. -/
theorem PrimeEstimates.halfOpen_U2 {w : MultiplicativeWeight} (h : PrimeEstimates w) :
    ∃ K ≥ 0, ∀ θ φ : ℝ, 0 < θ → θ ≤ φ → φ ≤ 1 →
      halfOpenPrimeSum w (exp φ⁻¹) (exp θ⁻¹) (fun p ↦ 1 + cos (φ * log p)) ≤
        log (φ / θ) + K := by
  refine ⟨4 * h.errorBound + log 2, by linarith [h.errorBound_nonneg, log_pos (by norm_num : (1 : ℝ) < 2)],
    fun θ φ hθ hθφ hφ1 ↦ ?_⟩
  have hφ := hθ.trans_le hθφ
  have ha := PrimeSums.two_le_exp_inv hφ hφ1
  have hab : exp φ⁻¹ ≤ exp θ⁻¹ := exp_le_exp.2 (inv_anti₀ hθ hθφ)
  have h1 := (abs_le.1 (h.interval_one_error ha hab)).2
  have h2 := h.interval_cos_tail_le ha hab hφ (by linarith) (by rw [log_exp, mul_inv_cancel₀ hφ.ne'])
  have he : log (log (exp θ⁻¹) / log (exp φ⁻¹)) = log (φ / θ) := by
    rw [log_exp, log_exp]
    congr 1
    field_simp
  rw [he] at h1
  rw [halfOpenPrimeSum_add]
  linarith

/-- The large prime range, with its difference-frequency singularity retained. -/
theorem PrimeEstimates.halfOpen_U3 {w : MultiplicativeWeight} (h : PrimeEstimates w) :
    ∃ K ≥ 0, ∀ x θ φ : ℝ, 0 < θ → θ ≤ φ → φ ≤ 1 → exp θ⁻¹ ≤ x →
      halfOpenPrimeSum w (exp θ⁻¹) x
        (fun p ↦ (1 + cos (θ * log p)) * (1 + cos (φ * log p))) ≤
      log (1 + θ * log x) + (1 / 2) * log (φ * log x / (1 + (φ - θ) * log x)) + K := by
  refine ⟨10 * h.errorBound + 3 * log 2, by linarith [h.errorBound_nonneg, log_pos (by norm_num : (1 : ℝ) < 2)],
    fun x θ φ hθ hθφ hφ1 hx ↦ ?_⟩
  have hφ := hθ.trans_le hθφ
  have ha := PrimeSums.two_le_exp_inv hθ (hθφ.trans hφ1)
  have hx2 := ha.trans hx
  have hlx : 0 < log x := log_pos (by linarith)
  have h1 := (abs_le.1 (h.interval_one_error ha hx)).2
  rw [log_exp, div_inv_eq_mul, mul_comm (log x) θ] at h1
  have hmain : log (θ * log x) ≤ log (1 + θ * log x) :=
    log_le_log (mul_pos hθ hlx) (by linarith)
  have hosc : ∀ ψ : ℝ, θ ≤ ψ → 1 ≤ ψ * log (exp θ⁻¹) := by
    intro ψ hθψ
    rw [log_exp]
    calc
      1 = θ * θ⁻¹ := (mul_inv_cancel₀ hθ.ne').symm
      _ ≤ ψ * θ⁻¹ := mul_le_mul_of_nonneg_right hθψ (inv_nonneg.2 hθ.le)
  have h2 := h.interval_cos_tail_le ha hx hθ (by linarith) (hosc θ le_rfl)
  have h3 := h.interval_cos_tail_le ha hx hφ (by linarith) (hosc φ hθφ)
  have h4 := (abs_le.1 (h.interval_difference_frequency hθ hθφ hφ1 hx)).2
  have h5 := h.interval_cos_tail_le ha hx (show 0 < φ + θ by positivity)
    (show φ + θ ≤ 2 by linarith) (hosc (φ + θ) (by linarith))
  rw [halfOpen_cos_product]
  linarith [h.errorBound_nonneg, log_pos (by norm_num : (1 : ℝ) < 2)]

end BretecheTenenbaumMean.WeightedModel
