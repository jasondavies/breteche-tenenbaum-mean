module

public import BretecheTenenbaumMean.CentralDyadicWindow

@[expose] public section

/-! # Counting the separated scales in the central window -/

namespace BretecheTenenbaumMean

open Finset Real

/-- Every real interval of length at least two contains at least half its
length in natural numbers, provided its lower endpoint is nonnegative. -/
theorem nat_interval_card_lower {a b : ℝ} (ha : 0 ≤ a) (hab : 2 ≤ b - a) :
    (b - a) / 2 ≤ ((Icc ⌈a⌉₊ ⌊b⌋₊).card : ℝ) := by
  have hb : 0 ≤ b := by linarith
  have hceil := Nat.ceil_lt_add_one ha
  have hfloor := Nat.lt_floor_add_one b
  have hmnR : (⌈a⌉₊ : ℝ) ≤ ⌊b⌋₊ := by linarith
  have hmn : ⌈a⌉₊ ≤ ⌊b⌋₊ := by exact_mod_cast hmnR
  rw [Nat.card_Icc, Nat.cast_sub (by omega : ⌈a⌉₊ ≤ ⌊b⌋₊ + 1), Nat.cast_add, Nat.cast_one]
  linarith

/-- Indices whose multiples by `m` fall in the central scale window. -/
noncomputable def scaleWindow (m t : ℕ) : Finset ℕ :=
  Icc ⌈criticalSlope * (t : ℝ) / m⌉₊ ⌊(criticalSlope * t + sqrt t) / m⌋₊

theorem scaleWindow_bounds {m t i : ℕ} (hm : 0 < m) (hi : i ∈ scaleWindow m t) :
    criticalSlope * t ≤ (m * i : ℕ) ∧
    (m * i : ℕ) ≤ criticalSlope * t + sqrt t := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hγ := criticalSlope_pos
  have hlow : criticalSlope * (t : ℝ) / m ≤ i :=
    (Nat.le_ceil _).trans (by exact_mod_cast (mem_Icc.1 hi).1)
  have hupp : (i : ℝ) ≤ (criticalSlope * t + sqrt t) / m :=
    (show (i : ℝ) ≤ ⌊(criticalSlope * t + sqrt t) / m⌋₊ by
      exact_mod_cast (mem_Icc.1 hi).2).trans (Nat.floor_le (by positivity))
  constructor
  · have := (div_le_iff₀ hmR).1 hlow
    push_cast
    nlinarith
  · have := (le_div_iff₀ hmR).1 hupp
    push_cast
    nlinarith

/-- A sufficiently long central window contains order `sqrt t/m` scales. -/
theorem scaleWindow_card_lower {m t : ℕ} (hm : 0 < m) (ht : 4 * (m : ℝ) ^ 2 ≤ t) :
    sqrt (t : ℝ) / (2 * m) ≤ ((scaleWindow m t).card : ℝ) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hroot : 2 * (m : ℝ) ≤ sqrt (t : ℝ) := by
    have := sq_sqrt (show (0 : ℝ) ≤ t by positivity)
    nlinarith [sqrt_nonneg (t : ℝ)]
  have hγ := criticalSlope_pos
  have hlen : 2 ≤ (criticalSlope * t + sqrt t) / m - criticalSlope * t / m := by
    rw [← sub_div]
    apply (le_div_iff₀ hmR).2
    linarith
  have he := nat_interval_card_lower (show 0 ≤ criticalSlope * (t : ℝ) / m by positivity) hlen
  change sqrt (t : ℝ) / (2 * m) ≤
    ((Icc ⌈criticalSlope * (t : ℝ) / m⌉₊ ⌊(criticalSlope * t + sqrt t) / m⌋₊).card : ℝ)
  convert he using 1
  ring

end BretecheTenenbaumMean
