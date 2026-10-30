module

public import BretecheTenenbaumMean.DivisorPolynomial
public import BretecheTenenbaumMean.Probability

@[expose] public section

/-! # Exact Euler products for the frequency averages of §2.2 -/

namespace BretecheTenenbaumMean

open Real Finset

noncomputable def normalizedPolynomial (n : ℕ) (θ : ℝ) : ℝ :=
  ‖divisorPolynomial n θ‖ ^ 2 / tau n

theorem normalizedPolynomial_nonneg (n : ℕ) (θ : ℝ) : 0 ≤ normalizedPolynomial n θ :=
  div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

@[simp] theorem normalizedPolynomial_one (θ : ℝ) : normalizedPolynomial 1 θ = 1 := by
  simp [normalizedPolynomial]

theorem normalizedPolynomial_mul {m n : ℕ} (hmn : m.Coprime n) (θ : ℝ) :
    normalizedPolynomial (m * n) θ = normalizedPolynomial m θ * normalizedPolynomial n θ := by
  rw [normalizedPolynomial, divisorPolynomial_mul hmn, norm_mul, mul_pow, tau_mul_of_coprime hmn]
  exact mul_div_mul_comm _ _ _ _

theorem normalizedPolynomial_prime {p : ℕ} (hp : p.Prime) (θ : ℝ) :
    normalizedPolynomial p θ = 1 + cos (θ * log p) := by
  rw [normalizedPolynomial, ← Complex.normSq_eq_norm_sq,
    normSq_divisorPolynomial_prime hp, tau_prime hp]
  ring

theorem expectation_normalizedPolynomial (x θ : ℝ) :
    expectation x (fun n => normalizedPolynomial n θ) =
      (∏ p ∈ primesLT x, (1 + (1 + cos (θ * log p)) / p)) / normalizer x := by
  rw [expectation_multiplicative x _ (normalizedPolynomial_one θ)
    (fun _ _ h => normalizedPolynomial_mul h θ)]
  congr 1
  exact Finset.prod_congr rfl (fun p hp => by rw [normalizedPolynomial_prime (mem_primesLT.mp hp).1])

/-- The elementary trigonometric identity in (2.12). -/
theorem cosine_product_identity (a b : ℝ) :
    (1 + cos a) * (1 + cos b) =
      1 + cos a + cos b + (1 / 2) * cos (b - a) + (1 / 2) * cos (b + a) := by
  rw [Real.cos_sub, Real.cos_add]
  ring

end BretecheTenenbaumMean
