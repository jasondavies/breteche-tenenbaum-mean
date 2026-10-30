module

public import BretecheTenenbaumMean.MomentRecurrence
public import BretecheTenenbaumMean.DeltaConvolution
public import BretecheTenenbaumMean.DivisorConvolutionBounds
public import BretecheTenenbaumMean.FrequencyEstimates

@[expose] public section

/-! # The quadratic mean in the finite squarefree model -/

namespace BretecheTenenbaumMean

open Finset Real

noncomputable def normalizedSecondMoment : ArithmeticFunction ℝ :=
  ⟨fun n ↦ moment 2 n / tau n, by simp [tau]⟩

@[simp] lemma normalizedSecondMoment_apply (n : ℕ) :
    normalizedSecondMoment n = moment 2 n / tau n := rfl

lemma normalizedSecondMoment_nonneg (n : ℕ) : 0 ≤ normalizedSecondMoment n :=
  div_nonneg (moment_nonneg 2 n) (Nat.cast_nonneg _)

/-- Average the product inequality over all factorizations of a squarefree integer.
The factor `4` from Cauchy–Schwarz is retained explicitly. -/
theorem squarefree_delta_sq_le_convolution {n : ℕ} (hn : Squarefree n) :
    (hooleyDelta n : ℝ) ^ 2 ≤ 4 * (normalizedSecondMoment * normalizedSecondMoment) n := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun a b ↦ normalizedSecondMoment a * normalizedSecondMoment b), mul_sum]
  have ht := tau_pos hn.ne_zero
  calc
    _ = ∑ _ ∈ n.divisors, (hooleyDelta n : ℝ) ^ 2 / tau n := by
      simp only [sum_const, nsmul_eq_mul]
      change _ = tau n * (_ / tau n)
      field_simp
    _ ≤ _ := by
      apply sum_le_sum
      intro d hd
      have hprod : d * (n / d) = n := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
      have hcop : d.Coprime (n / d) := Nat.coprime_of_squarefree_mul (hprod.symm ▸ hn)
      have he : tau d * tau (n / d) = tau n := by rw [← tau_mul_of_coprime hcop, hprod]
      have h := hooleyDelta_mul_sq_le_moments d (n / d)
      rw [hprod] at h
      calc
        _ ≤ (4 * moment 2 d * moment 2 (n / d)) / tau n := div_le_div_of_nonneg_right h ht.le
        _ = _ := by
          rw [← he]
          simp only [normalizedSecondMoment_apply, div_eq_mul_inv, mul_inv_rev]
          ring

/-- The finite model turns divisor convolution into a product of harmonic sums. -/
theorem expectation_delta_sq_le_normalized_second (x : ℝ) :
    expectation x (fun n ↦ (hooleyDelta n : ℝ) ^ 2) ≤
      4 * normalizer x * expectation x (fun n ↦ moment 2 n / tau n) ^ 2 := by
  have hnorm := normalizer_pos x
  have hsum := harmonic_convolution_smooth_le normalizedSecondMoment normalizedSecondMoment
    normalizedSecondMoment_nonneg normalizedSecondMoment_nonneg x
  calc
    _ ≤ (4 * ∑ n ∈ smoothSupport x, (normalizedSecondMoment * normalizedSecondMoment) n / n) /
        normalizer x := by
      unfold expectation
      apply div_le_div_of_nonneg_right _ hnorm.le
      rw [mul_sum]
      apply sum_le_sum
      intro n hn
      have h := div_le_div_of_nonneg_right (squarefree_delta_sq_le_convolution (mem_smoothSupport.1 hn).1)
        (Nat.cast_nonneg (α := ℝ) n)
      simpa only [mul_div_assoc] using h
    _ ≤ (4 * ((∑ n ∈ smoothSupport x, normalizedSecondMoment n / n) *
        ∑ n ∈ smoothSupport x, normalizedSecondMoment n / n)) / normalizer x := by gcongr
    _ = _ := by
      simp only [normalizedSecondMoment_apply, expectation]
      field_simp

/-- The upper estimate (4.1), with `log(1+log x)` retaining the small endpoint. -/
theorem expectation_delta_sq_bound : ∃ C > 0, ∀ x : ℝ, 2 ≤ x →
    expectation x (fun n ↦ (hooleyDelta n : ℝ) ^ 2) ≤
      C * log x * log (1 + log x) ^ 2 := by
  obtain ⟨A, hA, hmoment⟩ := expectation_moment_two_log_bound
  obtain ⟨_, B, _, hB, hnormalizer⟩ := PrimeSums.normalizer_bounds
  refine ⟨4 * B * A ^ 2, by positivity, fun x hx ↦ ?_⟩
  have he0 : 0 ≤ expectation x (fun n ↦ moment 2 n / tau n) :=
    expectation_nonneg _ (fun n _ ↦ normalizedSecondMoment_nonneg n)
  have hsq := mul_self_le_mul_self he0 (hmoment x hx)
  calc
    _ ≤ 4 * normalizer x * expectation x (fun n ↦ moment 2 n / tau n) ^ 2 :=
      expectation_delta_sq_le_normalized_second x
    _ ≤ 4 * (B * log x) * (A * log (1 + log x)) ^ 2 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hnormalizer x hx).2 (by norm_num)
      · simpa only [← pow_two] using hsq
      · positivity
      · have := log_nonneg (show 1 ≤ x by linarith)
        positivity
    _ = _ := by ring

end BretecheTenenbaumMean
