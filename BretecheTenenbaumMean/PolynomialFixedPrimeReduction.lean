module

public import BretecheTenenbaumMean.PolynomialProgressions
public import BretecheTenenbaumMean.Targets

@[expose] public section

/-! # Reduction of (1.7) to polynomials without fixed prime divisors

The reduction is unconditional. Its hypothesis is precisely the still-open
mean estimate for irreducible polynomials without fixed prime divisors.
Constant irreducible polynomials and zero values are included explicitly.
-/

namespace BretecheTenenbaumMean

open Polynomial NairTenenbaum Finset Real

theorem loglog_rpow_five_halves_lower {x : ℝ} (hx : 3 ≤ x) :
    0 < (log (log (3 : ℝ))) ^ (5 / 2 : ℝ) ∧
      (log (log (3 : ℝ))) ^ (5 / 2 : ℝ) ≤ (log (log x)) ^ (5 / 2 : ℝ) := by
  have h3 : 1 < log (3 : ℝ) := by linarith [log_three_gt_d9]
  have hlog3 : 0 < log (log (3 : ℝ)) := log_pos h3
  refine ⟨rpow_pos_of_pos hlog3 _, rpow_le_rpow hlog3.le ?_ (by norm_num)⟩
  exact log_le_log (by linarith) (log_le_log (by norm_num) hx)

/-- Constant polynomials satisfy the printed bound, including the zero
polynomial under the convention `Δ(0)=0`. -/
theorem polynomial_mean_bound_constant (c : ℤ) : ∃ C > (0 : ℝ), ∀ x : ℝ, 3 ≤ x →
    (∑ n ∈ Icc 1 ⌊x⌋₊, (hooleyDelta ((Polynomial.C c).eval (n : ℤ)).natAbs : ℝ)) ≤
      C * x * (log (log x)) ^ (5 / 2 : ℝ) := by
  let b := (log (log (3 : ℝ))) ^ (5 / 2 : ℝ)
  have hb : 0 < b := (loglog_rpow_five_halves_lower (x := 3) le_rfl).1
  let d := (hooleyDelta c.natAbs : ℝ)
  have hd : 0 ≤ d := Nat.cast_nonneg _
  refine ⟨d / b + 1, by positivity, fun x hx ↦ ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hfac := (loglog_rpow_five_halves_lower hx).2
  have hD : d ≤ (d / b + 1) * (log (log x)) ^ (5 / 2 : ℝ) := by
    calc
      _ = (d / b) * b := by field_simp
      _ ≤ (d / b) * (log (log x)) ^ (5 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hfac (div_nonneg hd hb.le)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (hb.le.trans hfac)
  calc
    _ = (⌊x⌋₊ : ℝ) * d := by simp [d, sum_const, Nat.card_Icc, nsmul_eq_mul]
    _ ≤ x * d := mul_le_mul_of_nonneg_right (Nat.floor_le hx0) hd
    _ ≤ x * ((d / b + 1) * (log (log x)) ^ (5 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hD hx0
    _ = _ := by ring

/-- A full proof of the polynomial estimate with no fixed prime divisors
suffices for the unrestricted polynomial consequence (1.7). -/
theorem polynomialMeanBound_of_noFixedPrime
    (hmean : ∀ F : ℤ[X], Irreducible F → NoFixedPrimeDivisor F →
      ∃ C > (0 : ℝ), ∀ x : ℝ, 3 ≤ x →
        (∑ n ∈ Icc 1 ⌊x⌋₊, (hooleyDelta (F.eval (n : ℤ)).natAbs : ℝ)) ≤
          C * x * (log (log x)) ^ (5 / 2 : ℝ)) : PolynomialMeanBound := by
  intro F hI
  by_cases hdeg : F.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hdeg]
    exact polynomial_mean_bound_constant _
  obtain ⟨q, hq, hG⟩ := exists_irreducible_progressions hI (Nat.pos_of_ne_zero hdeg)
  let G : ℕ → ℤ[X] := fun a ↦ progressionPrimitive F q (a : ℤ)
  choose C hC hbound using (fun a : ℕ ↦ hmean (G a) (hG (a : ℤ)).1 (hG (a : ℤ)).2)
  let b := (log (log (3 : ℝ))) ^ (5 / 2 : ℝ)
  have hb : 0 < b := (loglog_rpow_five_halves_lower (x := 3) le_rfl).1
  let w : ℕ → ℝ := fun a ↦ tau (F.comp (affinePolynomial q (a : ℤ))).content.natAbs
  have hw (a : ℕ) : 0 ≤ w a := Nat.cast_nonneg _
  let k : ℕ → ℝ := fun a ↦ (hooleyDelta ((G a).eval 0).natAbs : ℝ) / b + C a
  have hk (a : ℕ) : 0 ≤ k a := add_nonneg (div_nonneg (Nat.cast_nonneg _) hb.le) (hC a).le
  let K := ∑ a ∈ range q, w a * k a
  have hK : 0 ≤ K := sum_nonneg (fun a _ ↦ mul_nonneg (hw a) (hk a))
  refine ⟨K + 1, by positivity, fun x hx ↦ ?_⟩
  let L := (log (log x)) ^ (5 / 2 : ℝ)
  have hL : b ≤ L := (loglog_rpow_five_halves_lower hx).2
  have hL0 : 0 ≤ L := hb.le.trans hL
  have hx1 : 1 ≤ x := by linarith
  have hscale : b ≤ x * L := hL.trans (le_mul_of_one_le_left hL0 hx1)
  have hsum (a : ℕ) :
      (∑ m ∈ range (⌊x⌋₊ + 1), (hooleyDelta ((G a).eval (m : ℤ)).natAbs : ℝ)) ≤
        k a * (x * L) := by
    have he : range (⌊x⌋₊ + 1) = insert 0 (Icc 1 ⌊x⌋₊) := by
      ext n
      simp only [mem_range, mem_insert, mem_Icc]
      omega
    rw [he, sum_insert (by simp : 0 ∉ Icc 1 ⌊x⌋₊)]
    have hz : (hooleyDelta ((G a).eval 0).natAbs : ℝ) ≤
        ((hooleyDelta ((G a).eval 0).natAbs : ℝ) / b) * (x * L) := by
      calc
        _ = ((hooleyDelta ((G a).eval 0).natAbs : ℝ) / b) * b := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hscale (div_nonneg (Nat.cast_nonneg _) hb.le)
    have hm := hbound a x hx
    simpa only [Nat.cast_zero, k, add_mul, mul_assoc] using add_le_add hz hm
  calc
    _ ≤ ∑ a ∈ range q, w a *
        ∑ m ∈ range (⌊x⌋₊ + 1), (hooleyDelta ((G a).eval (m : ℤ)).natAbs : ℝ) :=
      polynomial_sum_le_progressions F hq _
    _ ≤ ∑ a ∈ range q, w a * (k a * (x * L)) :=
      sum_le_sum (fun a _ ↦ mul_le_mul_of_nonneg_left (hsum a) (hw a))
    _ = K * (x * L) := by simp only [K, sum_mul, mul_assoc]
    _ ≤ (K + 1) * (x * L) := mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (by linarith) hL0)
    _ = _ := by ring

end BretecheTenenbaumMean
