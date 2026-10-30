module

public import BretecheTenenbaumMean.Moments

@[expose] public section

/-! # The divisor Dirichlet polynomial in §2.2

Writing its summands as complex exponentials fixes the branch convention for
`d^(iθ)`; every divisor in the sum is positive.
-/

namespace BretecheTenenbaumMean

open Finset Real

@[simp] theorem divisorPolynomial_one (θ : ℝ) : divisorPolynomial 1 θ = 1 := by
  simp [divisorPolynomial]

@[simp] theorem divisorPolynomial_zero (θ : ℝ) : divisorPolynomial 0 θ = 0 := by
  simp [divisorPolynomial]

theorem norm_divisorPolynomial_le (n : ℕ) (θ : ℝ) : ‖divisorPolynomial n θ‖ ≤ tau n := by
  calc
    ‖divisorPolynomial n θ‖ ≤ ∑ d ∈ n.divisors,
        ‖Complex.exp ((θ * log d : ℝ) * Complex.I)‖ := norm_sum_le _ _
    _ = tau n := by simp only [Complex.norm_exp_ofReal_mul_I, Finset.sum_const, nsmul_eq_mul, mul_one, tau]

theorem divisorPolynomial_mul {m n : ℕ} (hmn : m.Coprime n) (θ : ℝ) :
    divisorPolynomial (m * n) θ = divisorPolynomial m θ * divisorPolynomial n θ := by
  classical
  unfold divisorPolynomial
  rw [hmn.divisors_mul, Finset.sum_map]
  change (∑ d ∈ (m.divisors ×ˢ n.divisors).attach,
    Complex.exp ((θ * log ((d.val.1 * d.val.2 : ℕ) : ℝ) : ℝ) * Complex.I)) = _
  rw [Finset.sum_attach _ (fun d : ℕ × ℕ =>
    Complex.exp ((θ * log ((d.1 * d.2 : ℕ) : ℝ) : ℝ) * Complex.I)), Finset.sum_product,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors ha).ne'
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hb).ne'
  rw [Nat.cast_mul, Real.log_mul ha0 hb0, mul_add, Complex.ofReal_add, add_mul,
    Complex.exp_add]

theorem divisorPolynomial_prime {p : ℕ} (hp : p.Prime) (θ : ℝ) :
    divisorPolynomial p θ = 1 + Complex.exp ((θ * log p : ℝ) * Complex.I) := by
  simp [divisorPolynomial, hp.divisors, hp.ne_one.symm]

/-- The local factor whose products give the cosine expressions in (2.9)--(2.12). -/
theorem normSq_divisorPolynomial_prime {p : ℕ} (hp : p.Prime) (θ : ℝ) :
    Complex.normSq (divisorPolynomial p θ) = 2 * (1 + cos (θ * log p)) := by
  rw [divisorPolynomial_prime hp]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re,
    Complex.exp_ofReal_mul_I_re, Complex.add_im, Complex.one_im,
    Complex.exp_ofReal_mul_I_im, zero_add]
  nlinarith [Real.cos_sq_add_sin_sq (θ * log p)]

theorem continuous_divisorPolynomial (n : ℕ) : Continuous (divisorPolynomial n) := by
  unfold divisorPolynomial
  fun_prop

/-- Expanding the squared norm pairs divisors through their logarithmic differences. -/
theorem norm_sq_divisorPolynomial_eq_sum (n : ℕ) (θ : ℝ) :
    ‖divisorPolynomial n θ‖ ^ 2 =
      ∑ d ∈ n.divisors, ∑ e ∈ n.divisors, cos (θ * (log d - log e)) := by
  have hre : (divisorPolynomial n θ).re = ∑ d ∈ n.divisors, cos (θ * log d) := by
    simp only [divisorPolynomial, Complex.re_sum, Complex.exp_ofReal_mul_I_re]
  have him : (divisorPolynomial n θ).im = ∑ d ∈ n.divisors, sin (θ * log d) := by
    simp only [divisorPolynomial, Complex.im_sum, Complex.exp_ofReal_mul_I_im]
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  simp_rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  rw [mul_sub, Real.cos_sub]

end BretecheTenenbaumMean
