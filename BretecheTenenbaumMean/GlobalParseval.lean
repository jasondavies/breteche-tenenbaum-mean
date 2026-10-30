module

public import BretecheTenenbaumMean.FejerInversion
public import BretecheTenenbaumMean.DivisorPolynomial
public import BretecheTenenbaumMean.SecondMoment

@[expose] public section

/-! # The global Parseval identity (2.6)

Fourier inversion of the triangular overlap kernel gives the exact identity
term by term in the finite divisor-pair sum. Both the continuous sinc version
and the paper's literal sine quotient are included.
-/

namespace BretecheTenenbaumMean

open Real MeasureTheory

/-- Each cosine term is absolutely integrable against the sinc-squared kernel. -/
theorem integrable_sinc_sq_cos (a : ℝ) :
    Integrable (fun θ : ℝ ↦ sinc (θ / 2) ^ 2 * cos (θ * a)) := by
  have he : (fun θ : ℝ ↦ sinc (θ / 2) ^ 2 * cos (θ * a)) =
      fun θ ↦ 2 * (fejerKernel θ * cos (θ * a)) := by
    funext θ
    rw [fejerKernel_eq_sinc]
    ring
  rw [he]
  exact (integrable_fejerKernel_cos a).const_mul 2

/-- The global frequency integral of the divisor polynomial converges. -/
theorem integrable_sinc_sq_divisorPolynomial (n : ℕ) :
    Integrable (fun θ : ℝ ↦ sinc (θ / 2) ^ 2 * ‖divisorPolynomial n θ‖ ^ 2) := by
  simp_rw [norm_sq_divisorPolynomial_eq_sum, Finset.mul_sum]
  exact integrable_finsetSum _ (fun (d : ℕ) _ ↦ integrable_finsetSum _
    (fun (e : ℕ) _ ↦ integrable_sinc_sq_cos (log d - log e)))

/-- Expanding the norm square and applying the global kernel identity to every
pair of divisors gives exactly `2π M₂(n)`. -/
theorem integral_sinc_sq_divisorPolynomial (n : ℕ) :
    (∫ θ : ℝ, sinc (θ / 2) ^ 2 * ‖divisorPolynomial n θ‖ ^ 2) = 2 * π * moment 2 n := by
  simp_rw [norm_sq_divisorPolynomial_eq_sum, Finset.mul_sum]
  rw [integral_finsetSum _ (fun (d : ℕ) _ ↦ integrable_finsetSum _
    (fun (e : ℕ) _ ↦ integrable_sinc_sq_cos (log d - log e)))]
  rw [moment_two_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [integral_finsetSum _ (fun (e : ℕ) _ ↦ integrable_sinc_sq_cos (log d - log e)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  exact integral_sinc_sq_cos (log d - log e)

/-- Equation (2.6), with the continuous value at the removable singularity. -/
theorem moment_two_parseval (n : ℕ) :
    moment 2 n = (1 / (2 * π)) *
      ∫ θ : ℝ, sinc (θ / 2) ^ 2 * ‖divisorPolynomial n θ‖ ^ 2 := by
  rw [integral_sinc_sq_divisorPolynomial]
  field_simp

/-- Replacing sinc by the literal sine quotient changes only the point `θ=0`. -/
theorem sinc_sq_divisorPolynomial_ae (n : ℕ) :
    (fun θ : ℝ ↦ sinc (θ / 2) ^ 2 * ‖divisorPolynomial n θ‖ ^ 2) =ᵐ[volume]
      fun θ ↦ (sin (θ / 2) / (θ / 2)) ^ 2 * ‖divisorPolynomial n θ‖ ^ 2 := by
  filter_upwards [volume.ae_ne (0 : ℝ)] with θ hθ
  rw [sinc_of_ne_zero (div_ne_zero hθ (by norm_num))]

/-- Absolute integrability also holds for the paper's literal integrand. -/
theorem integrable_parseval_integrand (n : ℕ) :
    Integrable (fun θ : ℝ ↦ (sin (θ / 2) / (θ / 2)) ^ 2 * ‖divisorPolynomial n θ‖ ^ 2) :=
  (integrable_sinc_sq_divisorPolynomial n).congr (sinc_sq_divisorPolynomial_ae n)

/-- The exact printed Parseval formula (2.6). It also holds at `n=0` under
the project's zero extension. -/
theorem moment_two_parseval_sine (n : ℕ) :
    moment 2 n = (1 / (2 * π)) *
      ∫ θ : ℝ, (sin (θ / 2) / (θ / 2)) ^ 2 * ‖divisorPolynomial n θ‖ ^ 2 := by
  rw [moment_two_parseval n, integral_congr_ae (sinc_sq_divisorPolynomial_ae n)]

end BretecheTenenbaumMean
