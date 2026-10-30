module

public import BretecheTenenbaumMean.Probability

@[expose] public section

/-! # Finite bounds for divisor convolutions and harmonic weights -/

namespace BretecheTenenbaumMean

open Finset

/-- Summing a nonnegative convolution over divisors is bounded by the product
of the two divisor sums. Pairs whose product does not divide `N` are discarded. -/
theorem sum_divisors_convolution_le (f g : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (N : ℕ) :
    (∑ n ∈ N.divisors, (f * g) n) ≤
      (∑ n ∈ N.divisors, f n) * ∑ n ∈ N.divisors, g n := by
  classical
  simp only [ArithmeticFunction.mul_apply]
  rw [sum_sigma', sum_mul_sum, ← sum_product']
  apply sum_le_sum_of_injOn (fun d : (Σ _ : ℕ, ℕ × ℕ) ↦ d.2)
  · intro d hd e he h
    change d.2 = e.2 at h
    have hd' := Nat.mem_divisorsAntidiagonal.1 (mem_sigma.1 hd).2
    have he' := Nat.mem_divisorsAntidiagonal.1 (mem_sigma.1 he).2
    have hn : d.1 = e.1 := by rw [← hd'.1, ← he'.1, h]
    cases d
    cases e
    simp_all
  · intro d hd
    obtain ⟨e, he, rfl⟩ := mem_image.1 hd
    have he' := mem_sigma.1 he
    have hn := Nat.mem_divisors.1 he'.1
    have hp := (Nat.mem_divisorsAntidiagonal.1 he'.2).1
    apply mem_product.2
    constructor
    · exact Nat.mem_divisors.2 ⟨(show e.2.1 ∣ e.1 by rw [← hp]; exact dvd_mul_right _ _).trans hn.1, hn.2⟩
    · exact Nat.mem_divisors.2 ⟨(show e.2.2 ∣ e.1 by rw [← hp]; exact dvd_mul_left _ _).trans hn.1, hn.2⟩
  · intro _ _
    exact le_rfl
  · intro d _ _
    exact mul_nonneg (hf d.1) (hg d.2)

noncomputable def divideArgument (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ f n / n, by simp⟩

@[simp] lemma divideArgument_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    divideArgument f n = f n / n := rfl

lemma divideArgument_mul (f g : ArithmeticFunction ℝ) :
    divideArgument (f * g) = divideArgument f * divideArgument g := by
  ext n
  simp only [divideArgument_apply, ArithmeticFunction.mul_apply, sum_div]
  apply sum_congr rfl
  intro d hd
  rw [← (Nat.mem_divisorsAntidiagonal.1 hd).1, Nat.cast_mul, div_mul_div_comm]

/-- Harmonic weights preserve convolution, and the support is divisor closed. -/
theorem harmonic_convolution_smooth_le (f g : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (x : ℝ) :
    (∑ n ∈ smoothSupport x, (f * g) n / n) ≤
      (∑ n ∈ smoothSupport x, f n / n) * ∑ n ∈ smoothSupport x, g n / n := by
  change (∑ n ∈ (primeProduct x).divisors, divideArgument (f * g) n) ≤ _
  rw [divideArgument_mul]
  exact sum_divisors_convolution_le _ _ (fun n ↦ div_nonneg (hf n) (Nat.cast_nonneg _))
    (fun n ↦ div_nonneg (hg n) (Nat.cast_nonneg _)) _

end BretecheTenenbaumMean
