module

public import Mathlib

@[expose] public section

/-!
# Statement of record: the mean value of the Erdős–Hooley Delta-function

R. de la Bretèche and G. Tenenbaum, arXiv:2309.03958v14.
This independent statement surface imports only Mathlib. Every definition has
its full mathematical value; only theorem proofs have deliberate `sorry` holes.
`Solution` imports the substantive development, where the same declarations are proved.

Compared results: Theorems 1.1 and 1.2; polynomial consequence (1.7);
Proposition 2.1 (both directions), Proposition 2.2, both forms of Lemma 3.1,
and the exact Parseval formula (2.6), including absolute integrability.
For the lower tail (2.5), x must be sufficiently large depending on T:
the unrestricted uniform reading is false. The library proves the explicit
sufficient range x ≥ exp((B*T)^4). We use integer count k in Lemma 3.1;
the paper’s real offset is t=k-h. Zero polynomial values use Δ(0)=0.
The literal Parseval quotient has value zero at θ=0 in Lean; this changes
only a Lebesgue-null singleton. See BLUEPRINT.md for all source corrections.
-/

namespace BretecheTenenbaumMean

open Finset Real MeasureTheory

/-- Number of positive divisors with logarithm in the half-open window `(u,u+1]`. -/
noncomputable def divisorWindow (n : ℕ) (u : ℝ) : ℕ :=
  (n.divisors.filter fun d : ℕ => u < log d ∧ log d ≤ u + 1).card

/-- Hooley’s divisor concentration: the maximum window count, with `Δ(0)=0`. -/
noncomputable def hooleyDelta (n : ℕ) : ℕ := sSup (Set.range (divisorWindow n))

/-- The number of positive divisors, as a real number. -/
noncomputable def tau (n : ℕ) : ℝ := n.divisors.card

/-- The real-valued divisor-window count. -/
noncomputable def delta (n : ℕ) (u : ℝ) : ℝ := divisorWindow n u

/-- The moment `M_q(n)`, integrated over the real line with Lebesgue measure. -/
noncomputable def moment (q n : ℕ) : ℝ := ∫ u : ℝ, delta n u ^ q

/-- The finite set of rational primes strictly below the real cutoff. -/
noncomputable def primesLT (x : ℝ) : Finset ℕ :=
  (range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ (p : ℝ) < x)

/-- The product of the primes strictly below the cutoff. -/
noncomputable def primeProduct (x : ℝ) : ℕ := ∏ p ∈ primesLT x, p

/-- All squarefree integers with prime factors below the cutoff; they need not be below it. -/
noncomputable def smoothSupport (x : ℝ) : Finset ℕ := (primeProduct x).divisors

/-- The Euler product normalizing the squarefree reciprocal weights. -/
noncomputable def normalizer (x : ℝ) : ℝ := ∏ p ∈ primesLT x, (1 + (p : ℝ)⁻¹)

/-- Expectation with mass `1 / (n * normalizer x)` on the finite smooth support. -/
noncomputable def expectation (x : ℝ) (f : ℕ → ℝ) : ℝ :=
  (∑ n ∈ smoothSupport x, f n / n) / normalizer x

/-- Probability of a set in the finite squarefree model. -/
noncomputable def probability (x : ℝ) (E : Set ℕ) : ℝ :=
  expectation x (E.indicator (fun _ => 1))

/-- The product of the distinct prime factors of `n` below `y`. -/
noncomputable def smallPrimePart (n : ℕ) (y : ℝ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) < y), p

/-- The constant `1 / (log 4 - 1)` in the good-set envelope and central window. -/
noncomputable def criticalSlope : ℝ := 1 / (log 4 - 1)

/-- The paper’s logarithmic penalty, with parameter `δ` explicit. -/
noncomputable def penalty (δ T y : ℝ) : ℝ :=
  δ * min (log (T * log (3 * y)))
    ((log (log (3 * y)) - criticalSlope * log T) ^ 2 / log T)

/-- The squarefree good set `E_T` defined by all small-prime divisor-count bounds. -/
def goodSet (δ T : ℝ) : Set ℕ :=
  {n | Squarefree n ∧ ∀ y : ℝ, 1 ≤ y →
    tau (smallPrimePart n y) ≤ T * log (3 * y) * exp (-penalty δ T y)}

/-- The subset `E_T*` additionally satisfying `M₂(n)/τ(n) ≤ T`. -/
def goodSetStar (δ T : ℝ) : Set ℕ :=
  {n | n ∈ goodSet δ T ∧ moment 2 n / tau n ≤ T}

/-- The subset satisfying all normalized moment thresholds through order `q`. -/
def momentGoodSet (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ) : Set ℕ :=
  {n | n ∈ goodSetStar δ T ∧ ∀ j : ℕ, 1 ≤ j → j ≤ q → moment j n ≤ tau n * θ j}

/-- The truncated expectation `S_q(x)` of §2.3, cut off through order `q-1`. -/
noncomputable def truncatedMoment (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  expectation x ((momentGoodSet δ T θ (q - 1)).indicator (fun n => moment q n / tau n))

/-- The divisor Dirichlet polynomial `Σ_{d∣n} exp(i θ log d)`; all summed divisors are positive. -/
noncomputable def divisorPolynomial (n : ℕ) (θ : ℝ) : ℂ :=
  ∑ d ∈ n.divisors, Complex.exp ((θ * log d : ℝ) * Complex.I)

/-- The ordinary first-moment sum. -/
noncomputable def meanSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (hooleyDelta n : ℝ)

/-- The ordinary second-moment sum. -/
noncomputable def quadraticSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (hooleyDelta n : ℝ) ^ 2

/-- Theorem 1.1. The implied constant and cutoff are absolute. -/
def TheoremOne : Prop :=
  ∃ C > (0 : ℝ), ∃ x₀ ≥ (3 : ℝ), ∀ x ≥ x₀,
    meanSum x ≤ C * x * (log (log x)) ^ (5 / 2 : ℝ)

/-- Both inequalities in Theorem 1.2, on the printed range `x ≥ 3`. -/
def TheoremTwo : Prop :=
  ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ x : ℝ, 3 ≤ x →
    c * x * log x ≤ quadraticSum x ∧
    quadraticSum x ≤ C * x * log x * (log (log x)) ^ 2

/-- The polynomial-argument consequence (1.7). Integer roots contribute zero,
using the explicit extension `hooleyDelta 0 = 0`. -/
def PolynomialMeanBound : Prop :=
  ∀ F : Polynomial ℤ, Irreducible F → ∃ C > (0 : ℝ), ∀ x : ℝ, 3 ≤ x →
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (hooleyDelta (F.eval (n : ℤ)).natAbs : ℝ)) ≤
      C * x * (log (log x)) ^ (5 / 2 : ℝ)

/-- Proposition 2.1's upper exceptional-set estimate (2.4). -/
def PropositionTwoOneUpper : Prop :=
  ∃ δ > (0 : ℝ), ∃ C > (0 : ℝ), ∀ x T : ℝ, 2 ≤ x → 3 ≤ T →
    probability x (goodSetStar δ T)ᶜ ≤ C / T

/-- A quantified lower-tail target for (2.5). The cutoff can depend on `T`;
uniformity in both variables over the whole printed upper-bound range is false.
A proved quantitative version uses `x ≥ exp((B*T)^4)` for an absolute `B>0`. -/
def PropositionTwoOneLower : Prop :=
  ∃ c > (0 : ℝ), ∀ T : ℝ, 3 ≤ T → ∃ x₀ ≥ (2 : ℝ), ∀ x ≥ x₀,
    c / T ≤ probability x {n | T < moment 2 n / tau n}

/-- The admissibility conditions preceding (2.14). -/
def AdmissibleThresholds (C₀ T : ℝ) (θ : ℕ → ℝ) : Prop :=
  (∀ j, 0 < θ j) ∧ 1 ≤ θ 1 ∧ C₀ * T ≤ θ 2 ∧
    2 * C₀ ^ 2 * T ^ 2 * log T ≤ θ 3 ∧
    (∀ j : ℕ, 2 ≤ j → (j.factorial : ℝ) * (C₀ * T) ^ (j - 1) ≤ θ j) ∧
    ∀ q : ℕ, 3 ≤ q →
      (∑ j ∈ Finset.Icc 1 (q / 2), (q.choose j : ℝ) * θ j * θ (q - j)) ≤
        θ q / (C₀ * T * sqrt (log T))

/-- Proposition 2.2, with constants chosen before all varying parameters. -/
def PropositionTwoTwo : Prop :=
  ∃ δ > (0 : ℝ), ∃ C₀ ≥ (1 : ℝ), ∀ T : ℝ, 3 ≤ T → ∀ θ : ℕ → ℝ,
    AdmissibleThresholds C₀ T θ → ∀ q : ℕ, 3 ≤ q → ∀ x : ℝ, 2 ≤ x →
      truncatedMoment δ T θ q x ≤ C₀ * θ q / ((q : ℝ) ^ 2 * T)

/-- The uniform estimate (3.1), at sufficiently large `x` for each fixed `ε`.
The relevant integer indices are nonnegative once the cutoff is large. -/
def LemmaThreeOne : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∃ x₀ ≥ (3 : ℝ), ∀ x ≥ x₀,
      ∀ h k : ℕ, (log x) ^ ε ≤ (2 : ℝ) ^ h →
        (2 : ℝ) ^ h ≤ (log x) ^ (1 - ε) →
        ε * log (log x) ≤ k → (k : ℝ) ≤ log (log x) / ε →
        let P := probability (exp ((2 : ℝ) ^ h)) {n | n.primeFactors.card = k}
        let A := ((h : ℝ) * log 2) ^ k / ((2 : ℝ) ^ h * (k.factorial : ℝ))
        c * A ≤ P ∧ P ≤ C * A

/-- The central-window consequence (3.2). Writing the count as `k` makes the
integrality of the paper's `h+t` explicit; the offset is `t = k-h`. -/
def LemmaThreeOneCentral : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∃ x₀ ≥ (3 : ℝ), ∀ x ≥ x₀,
      ∀ h k : ℕ, (log x) ^ ε ≤ (2 : ℝ) ^ h →
        (2 : ℝ) ^ h ≤ (log x) ^ (1 - ε) →
        |(k : ℝ) - h - (h : ℝ) / criticalSlope| ≤ sqrt (log (log x)) →
        let P := probability (exp ((2 : ℝ) ^ h)) {n | n.primeFactors.card = k}
        let A := 1 / ((2 : ℝ) ^ ((k : ℝ) - h) * sqrt (log (log x)))
        c * A ≤ P ∧ P ≤ C * A

/-- Theorem 1.1: ordinary mean bounded by `x (log log x)^(5/2)`. -/
theorem theoremOne : TheoremOne := by sorry

/-- Theorem 1.2: both quadratic mean bounds, for every `x ≥ 3`. -/
theorem theoremTwo : TheoremTwo := by sorry

/-- Equation (1.7): the mean bound at all irreducible integer polynomial arguments. -/
theorem polynomialMeanBound : PolynomialMeanBound := by sorry

/-- Proposition 2.1 upper bound: exceptional probability is `O(1/T)`. -/
theorem propositionTwoOneUpper : PropositionTwoOneUpper := by sorry

/-- Proposition 2.1 lower bound, with the necessary T-dependent cutoff. -/
theorem propositionTwoOneLower : PropositionTwoOneLower := by sorry

/-- Proposition 2.2: uniform truncated moment estimate for all admissible thresholds. -/
theorem propositionTwoTwo : PropositionTwoTwo := by sorry

/-- Lemma 3.1, (3.1): two-sided prime-factor layer probabilities. -/
theorem lemmaThreeOne : LemmaThreeOne := by sorry

/-- Lemma 3.1, (3.2): the central-window estimate, with integer counts. -/
theorem lemmaThreeOneCentral : LemmaThreeOneCentral := by sorry

/-- Absolute integrability of the global Parseval integrand. -/
theorem integrable_parseval_integrand (n : ℕ) :
    Integrable (fun θ : ℝ ↦ (sin (θ / 2) / (θ / 2)) ^ 2 * ‖divisorPolynomial n θ‖ ^ 2) := by sorry

/-- Equation (2.6), with the exact factor `1/(2π)`. -/
theorem moment_two_parseval_sine (n : ℕ) :
    moment 2 n = (1 / (2 * π)) *
      ∫ θ : ℝ, (sin (θ / 2) / (θ / 2)) ^ 2 * ‖divisorPolynomial n θ‖ ^ 2 := by sorry

end BretecheTenenbaumMean
