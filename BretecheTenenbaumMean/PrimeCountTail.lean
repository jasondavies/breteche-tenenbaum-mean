module

public import BretecheTenenbaumMean.PoissonRate
public import BretecheTenenbaumMean.PrimeLayers
public import BretecheTenenbaumMean.EventBounds

@[expose] public section

/-! # Upper tails for the number of prime factors and the divisor function -/

namespace BretecheTenenbaumMean

open Real Finset

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

end BretecheTenenbaumMean
