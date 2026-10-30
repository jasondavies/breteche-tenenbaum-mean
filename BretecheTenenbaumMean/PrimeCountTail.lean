module

public import BretecheTenenbaumMean.PoissonRate
public import BretecheTenenbaumMean.PrimeLayers
public import BretecheTenenbaumMean.EventBounds

@[expose] public section

/-! # Upper tails for the number of prime factors and the divisor function -/

namespace BretecheTenenbaumMean

open Real Finset

/-- Summing the fixed prime-count layers gives a geometric factorial-tail bound. -/
theorem probability_prime_ge_le (x : ℝ) {ρ : ℝ} {k : ℕ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hk : (∑ p ∈ primesLT x, (p : ℝ)⁻¹) ≤ ρ * (k + 1)) :
    probability x {n | k ≤ n.primeFactors.card} ≤
      poissonTerm (∑ p ∈ primesLT x, (p : ℝ)⁻¹) k / ((1 - ρ) * normalizer x) := by
  classical
  let u := ∑ p ∈ primesLT x, (p : ℝ)⁻¹
  have hu : 0 ≤ u := sum_nonneg (fun _ _ ↦ by positivity)
  let s := ((smoothSupport x).image (fun n ↦ n.primeFactors.card)).filter (fun r ↦ k ≤ r)
  rw [probability_ge_eq_sum_fibers x (fun n ↦ n.primeFactors.card) k]
  calc (∑ r ∈ s, probability x {n | n.primeFactors.card = r})
      ≤ ∑ r ∈ s, poissonTerm u r / normalizer x := by
        apply sum_le_sum
        intro r _
        rw [probability_prime_layer_eq]
        apply div_le_div_of_nonneg_right _ (normalizer_pos x).le
        exact distinctProductSum_le _ _ _ (fun _ _ ↦ by positivity)
    _ = (∑ r ∈ s, poissonTerm u r) / normalizer x := (sum_div _ _ _).symm
    _ ≤ (poissonTerm u k / (1 - ρ)) / normalizer x :=
      div_le_div_of_nonneg_right (sum_poissonTerm_tail_le hu hρ hρ1 hk s
        (fun r hr ↦ (mem_filter.1 hr).2)) (normalizer_pos x).le
    _ = _ := by rw [div_div]

/-- The prime-count upper tail with its large-deviation exponential and
square-root saving. No approximation or rounding of the threshold is used. -/
theorem probability_prime_ge_le_rate (x : ℝ) {ρ : ℝ} {k : ℕ}
    (hu : 0 < ∑ p ∈ primesLT x, (p : ℝ)⁻¹) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hk0 : k ≠ 0)
    (hk : (∑ p ∈ primesLT x, (p : ℝ)⁻¹) ≤ ρ * (k + 1)) :
    probability x {n | k ≤ n.primeFactors.card} ≤
      exp ((∑ p ∈ primesLT x, (p : ℝ)⁻¹) *
        (1 - poissonRate (k / (∑ p ∈ primesLT x, (p : ℝ)⁻¹)))) /
        ((1 - ρ) * sqrt (2 * π * k) * normalizer x) := by
  refine (probability_prime_ge_le x hρ hρ1 hk).trans ?_
  have hd : 0 ≤ (1 - ρ) * normalizer x := mul_nonneg (by linarith) (normalizer_pos x).le
  have h := div_le_div_of_nonneg_right (poissonTerm_le_rate hu hk0) hd
  convert h using 1
  rw [div_div]
  congr 1
  ring

/-- A non-strict divisor threshold corresponds to a ceiling, including powers
of two exactly. This corrects the floor convention in the cited tail argument. -/
theorem tau_ge_iff_prime_count_ge_ceil {n : ℕ} (hn : Squarefree n) {R : ℝ} (hR : 0 < R) :
    R ≤ tau n ↔ ⌈log R / log 2⌉₊ ≤ n.primeFactors.card := by
  rw [tau_squarefree hn, ← log_le_log_iff hR (by positivity : (0 : ℝ) < 2 ^ n.primeFactors.card),
    log_pow, Nat.ceil_le, div_le_iff₀ (log_pos (by norm_num : (1 : ℝ) < 2))]

/-- The exact equality of divisor and prime-count tail events on the support. -/
theorem probability_tau_ge_eq (x : ℝ) {R : ℝ} (hR : 0 < R) :
    probability x {n | R ≤ tau n} = probability x {n | ⌈log R / log 2⌉₊ ≤ n.primeFactors.card} := by
  apply probability_congr_on_support
  intro n hn
  exact tau_ge_iff_prime_count_ge_ceil (mem_smoothSupport.1 hn).1 hR

/-- Explicit factorial-tail bound for a real divisor threshold. -/
theorem probability_tau_ge_le (x : ℝ) {R ρ : ℝ} (hR : 0 < R)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hk : (∑ p ∈ primesLT x, (p : ℝ)⁻¹) ≤ ρ * (⌈log R / log 2⌉₊ + 1)) :
    probability x {n | R ≤ tau n} ≤
      poissonTerm (∑ p ∈ primesLT x, (p : ℝ)⁻¹) ⌈log R / log 2⌉₊ /
        ((1 - ρ) * normalizer x) := by
  rw [probability_tau_ge_eq x hR]
  exact probability_prime_ge_le x hρ hρ1 hk

end BretecheTenenbaumMean
