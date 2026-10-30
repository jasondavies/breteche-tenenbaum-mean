module

public import BretecheTenenbaumMean.HalfIntervalSummation
public import BretecheTenenbaumMean.PolynomialFixedPrimeReduction

@[expose] public section

/-! # From the weighted model to the full polynomial mean

The only unproved input in this reduction is stated explicitly as
`PolynomialWeightedExpectationBound`. Short intervals, square factors,
fixed prime divisors, and the bounded initial range are handled by proofs.
-/

namespace BretecheTenenbaumMean

open Polynomial NairTenenbaum Finset Real

/-- The remaining weighted-mean target. Constants and the initial cutoff may
depend on the fixed polynomial, as allowed in (1.7). -/
def PolynomialWeightedExpectationBound : Prop :=
  ∀ F : ℤ[X], Irreducible F → NoFixedPrimeDivisor F →
    ∃ A > (0 : ℝ), ∃ z₀ ≥ (3 : ℝ), ∀ z ≥ z₀,
      WeightedModel.expectation (polynomialRootWeight F) z (fun n ↦ (hooleyDelta n : ℝ)) ≤
        A * (log (log z)) ^ (5 / 2 : ℝ)

theorem loglog_rpow_five_halves_mono {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    (log (log x)) ^ (5 / 2 : ℝ) ≤ (log (log y)) ^ (5 / 2 : ℝ) := by
  have h3 : 1 < log (3 : ℝ) := by linarith [log_three_gt_d9]
  have hxlog : 1 < log x := h3.trans_le (log_le_log (by norm_num) hx)
  apply rpow_le_rpow (log_pos hxlog).le _ (by norm_num)
  exact log_le_log (by linarith) (log_le_log (by linarith) hxy)

/-- For a polynomial with no fixed prime divisor, the eventual weighted mean
suffices for the printed mean bound on the entire range `x≥3`. -/
theorem polynomial_mean_of_weighted_expectation (F : ℤ[X])
    (hI : Irreducible F) (hF : NoFixedPrimeDivisor F)
    (hweighted : ∃ A > (0 : ℝ), ∃ z₀ ≥ (3 : ℝ), ∀ z ≥ z₀,
      WeightedModel.expectation (polynomialRootWeight F) z (fun n ↦ (hooleyDelta n : ℝ)) ≤
        A * (log (log z)) ^ (5 / 2 : ℝ)) :
    ∃ C > (0 : ℝ), ∀ x : ℝ, 3 ≤ x →
      (∑ n ∈ Icc 1 ⌊x⌋₊, (hooleyDelta (F.eval (n : ℤ)).natAbs : ℝ)) ≤
        C * x * (log (log x)) ^ (5 / 2 : ℝ) := by
  obtain ⟨A, hA, z₀, hz₀, hE⟩ := hweighted
  obtain ⟨s₀, hs₀, D, hD, hshort⟩ := polynomial_short_sum_weighted_bound F hF hI
    (α := 1) zero_lt_one
  let N₀ : ℕ := ⌈2 * (max s₀ z₀ + 3)⌉₊
  let f : ℕ → ℝ := fun n ↦ (hooleyDelta (F.eval (n : ℤ)).natAbs : ℝ)
  let B := ∑ n ∈ Icc 1 N₀, f n
  have hB : 0 ≤ B := sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)
  let b := (log (log (3 : ℝ))) ^ (5 / 2 : ℝ)
  have hb : 0 < b := (loglog_rpow_five_halves_lower (x := 3) le_rfl).1
  refine ⟨B / b + 2 * (D * A) + 1, by positivity, fun x hx ↦ ?_⟩
  let L := (log (log x)) ^ (5 / 2 : ℝ)
  have hL : b ≤ L := (loglog_rpow_five_halves_lower hx).2
  have hL0 : 0 ≤ L := hb.le.trans hL
  have hx0 : 0 ≤ x := by linarith
  have hhalf (n : ℕ) (hn₀ : N₀ ≤ n) (hnx : n ≤ ⌊x⌋₊) :
      (∑ i ∈ Ioc (n / 2) n, f i) ≤ (D * A) * n * L := by
    have hnreal : 2 * (max s₀ z₀ + 3) ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hn₀)
    have hnlarge : (6 : ℝ) ≤ n := by linarith [le_max_right s₀ z₀]
    have hnxreal : (n : ℝ) ≤ x := (by exact_mod_cast hnx : (n : ℝ) ≤ ⌊x⌋₊).trans
      (Nat.floor_le hx0)
    let s := (n : ℝ) / 2
    let z := (⌊s⌋₊ : ℝ) + 1
    have hs : s₀ < s := by dsimp [s]; linarith [le_max_left s₀ z₀]
    have hsz₀ : z₀ ≤ s := by dsimp [s]; linarith [le_max_right s₀ z₀]
    have hs0 : 0 ≤ s := by dsimp [s]; positivity
    have hsz : s < z := Nat.lt_floor_add_one s
    have hz : z₀ ≤ z := hsz₀.trans hsz.le
    have hzx : z ≤ x := by
      have hfl := Nat.floor_le hs0
      dsimp [z, s] at *
      linarith
    have hzl : (log (log z)) ^ (5 / 2 : ℝ) ≤ L :=
      loglog_rpow_five_halves_mono (hz₀.trans hz) hzx
    have he : WeightedModel.expectation (polynomialRootWeight F) z
        (fun n ↦ (hooleyDelta n : ℝ)) ≤ A * L :=
      (hE z hz).trans (mul_le_mul_of_nonneg_left hzl hA.le)
    have hss := hshort s s hs (by rw [rpow_one]) le_rfl
    have hfloor : ⌊s⌋₊ = n / 2 := by
      simpa only [s, Nat.floor_natCast, Nat.cast_ofNat] using Nat.floor_div_natCast (n : ℝ) 2
    have hadd : s + s = (n : ℝ) := by dsimp [s]; ring
    have hsum : (∑ i ∈ Ioc (n / 2) n, f i) = polynomialDeltaShortSum F s s := by
      simp only [polynomialDeltaShortSum, hfloor, hadd, Nat.floor_natCast, f]
    rw [hsum]
    calc
      _ ≤ D * s * WeightedModel.expectation (polynomialRootWeight F) z
          (fun n ↦ (hooleyDelta n : ℝ)) := hss
      _ ≤ D * s * (A * L) := mul_le_mul_of_nonneg_left he (mul_nonneg hD.le hs0)
      _ ≤ (D * A) * n * L := by
        have hsn : s ≤ (n : ℝ) := by dsimp [s]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
        have hh := mul_le_mul_of_nonneg_left hsn (mul_nonneg (mul_nonneg hD.le hA.le) hL0)
        nlinarith
  have hsum := sum_le_of_half_interval_bound f (fun _ ↦ Nat.cast_nonneg _) N₀ ⌊x⌋₊
    (mul_nonneg hD.le hA.le) hL0 hhalf
  have hscale : b ≤ x * L := hL.trans (le_mul_of_one_le_left hL0 (by linarith))
  have hinit : B ≤ (B / b) * (x * L) := by
    calc
      _ = (B / b) * b := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hscale (div_nonneg hB hb.le)
  calc
    _ ≤ B + 2 * (D * A) * (⌊x⌋₊ : ℝ) * L := hsum
    _ ≤ B + 2 * (D * A) * x * L := by
      gcongr
      exact Nat.floor_le hx0
    _ ≤ (B / b + 2 * (D * A)) * x * L := by nlinarith
    _ ≤ _ := by nlinarith [mul_nonneg hx0 hL0]

/-- The polynomial consequence follows from the weighted finite-model mean.
This theorem is a reduction; the weighted target has not been assumed as an axiom. -/
theorem polynomialMeanBound_of_weighted_expectation
    (h : PolynomialWeightedExpectationBound) : PolynomialMeanBound := by
  apply polynomialMeanBound_of_noFixedPrime
  intro F hI hF
  exact polynomial_mean_of_weighted_expectation F hI hF (h F hI hF)

end BretecheTenenbaumMean
