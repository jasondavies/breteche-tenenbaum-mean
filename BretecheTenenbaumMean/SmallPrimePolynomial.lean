module

public import BretecheTenenbaumMean.GoodSets
public import BretecheTenenbaumMean.PolynomialExpectation

@[expose] public section

/-! # Dividing the frequency polynomial by its small-prime divisor count

This is the multiplicative weight used for the small-frequency part of §2.2.
-/

namespace BretecheTenenbaumMean

open Real Finset

@[simp] theorem smallPrimePart_one (y : ℝ) : smallPrimePart 1 y = 1 := by
  simp [smallPrimePart]

theorem smallPrimePart_prime {p : ℕ} (hp : p.Prime) (y : ℝ) :
    smallPrimePart p y = if (p : ℝ) < y then p else 1 := by
  classical
  simp only [smallPrimePart, hp.primeFactors, filter_singleton]
  split_ifs <;> simp

theorem smallPrimePart_mul {m n : ℕ} (hmn : m.Coprime n) (y : ℝ) :
    smallPrimePart (m * n) y = smallPrimePart m y * smallPrimePart n y := by
  unfold smallPrimePart
  rw [hmn.primeFactors_mul, filter_union,
    prod_union (disjoint_filter_filter hmn.disjoint_primeFactors)]

theorem smallPrimePart_coprime {m n : ℕ} (hmn : m.Coprime n) (y : ℝ) :
    (smallPrimePart m y).Coprime (smallPrimePart n y) :=
  Nat.Coprime.of_dvd (smallPrimePart_dvd m y) (smallPrimePart_dvd n y) hmn

noncomputable def smallPrimePolynomial (n : ℕ) (y θ : ℝ) : ℝ :=
  normalizedPolynomial n θ / tau (smallPrimePart n y)

theorem smallPrimePolynomial_nonneg (n : ℕ) (y θ : ℝ) : 0 ≤ smallPrimePolynomial n y θ :=
  div_nonneg (normalizedPolynomial_nonneg n θ) (Nat.cast_nonneg _)

@[simp] theorem smallPrimePolynomial_one (y θ : ℝ) : smallPrimePolynomial 1 y θ = 1 := by
  simp [smallPrimePolynomial]

theorem smallPrimePolynomial_mul {m n : ℕ} (hmn : m.Coprime n) (y θ : ℝ) :
    smallPrimePolynomial (m * n) y θ = smallPrimePolynomial m y θ * smallPrimePolynomial n y θ := by
  rw [smallPrimePolynomial, normalizedPolynomial_mul hmn, smallPrimePart_mul hmn,
    tau_mul_of_coprime (smallPrimePart_coprime hmn y)]
  exact mul_div_mul_comm _ _ _ _

theorem smallPrimePolynomial_prime {p : ℕ} (hp : p.Prime) (y θ : ℝ) :
    smallPrimePolynomial p y θ =
      if (p : ℝ) < y then (1 + cos (θ * log p)) / 2 else 1 + cos (θ * log p) := by
  rw [smallPrimePolynomial, normalizedPolynomial_prime hp, smallPrimePart_prime hp]
  split_ifs <;> simp only [tau_prime hp, tau_one, div_one]

/-- Exact Euler product for the small-prime-weighted frequency average. -/
theorem expectation_smallPrimePolynomial (x y θ : ℝ) :
    expectation x (fun n ↦ smallPrimePolynomial n y θ) =
      (∏ p ∈ primesLT x,
        (1 + (if (p : ℝ) < y then (1 + cos (θ * log p)) / 2 else 1 + cos (θ * log p)) / p)) /
          normalizer x := by
  rw [expectation_multiplicative x _ (smallPrimePolynomial_one y θ)
    (fun _ _ h ↦ smallPrimePolynomial_mul h y θ)]
  congr 1
  exact prod_congr rfl (fun p hp ↦ by rw [smallPrimePolynomial_prime (mem_primesLT.1 hp).1])

end BretecheTenenbaumMean
