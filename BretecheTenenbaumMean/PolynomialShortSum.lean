module

public import BretecheTenenbaumMean.Delta
public import NairTenenbaum.Hooley.HooleyShortSum

@[expose] public section

/-! # The Nair–Tenenbaum reduction for polynomial values

The pinned Nair–Tenenbaum theorem supplies the arithmetic short-sum estimate. The sharp
root-weighted mean is a separate outstanding input to (1.7).
-/

namespace BretecheTenenbaumMean

open Finset Polynomial Real

/-- The two projects use exactly the same logarithmic-window definition. -/
theorem hooleyDelta_eq_nair (n : ℕ) : hooleyDelta n = NairTenenbaum.hooleyDelta n := rfl

noncomputable def polynomialDeltaShortSum (F : ℤ[X]) (x y : ℝ) : ℝ :=
  ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + y⌋₊, (hooleyDelta (F.eval (n : ℤ)).natAbs : ℝ)

noncomputable def polynomialDeltaRootSum (F : ℤ[X]) (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, (hooleyDelta n : ℝ) * (NairTenenbaum.rootCount F n : ℝ) / n

theorem polynomialDeltaShortSum_eq_nair (F : ℤ[X]) (x y : ℝ) :
    polynomialDeltaShortSum F x y = NairTenenbaum.hooleyPolynomialSum F 1 x y := by
  simp only [polynomialDeltaShortSum, NairTenenbaum.hooleyPolynomialSum,
    NairTenenbaum.shortInterval, rpow_one, hooleyDelta_eq_nair]

theorem polynomialDeltaRootSum_eq_nair (F : ℤ[X]) {x : ℝ} (hx : 0 ≤ x) :
    polynomialDeltaRootSum F x = NairTenenbaum.hooleyRootSum F 1 x := by
  classical
  symm
  unfold polynomialDeltaRootSum NairTenenbaum.hooleyRootSum
  apply sum_bij (fun (n : ℕ+) _ ↦ (n : ℕ))
  · intro n hn
    exact mem_Icc.2 ⟨n.pos, Nat.le_floor ((NairTenenbaum.mem_positiveUpTo n x).1 hn)⟩
  · intro a _ b _ he
    exact Subtype.ext he
  · intro n hn
    refine ⟨⟨n, (mem_Icc.1 hn).1⟩, ?_, rfl⟩
    apply (NairTenenbaum.mem_positiveUpTo _ x).2
    exact (show (n : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast (mem_Icc.1 hn).2).trans (Nat.floor_le hx)
  · intro n _
    simp only [rpow_one, hooleyDelta_eq_nair, mul_div_assoc]

/-- The proved short-sum reduction, expressed using this project's Delta
function and natural-number summation convention. No mean bound is assumed. -/
theorem polynomial_short_sum_root_bound (F : ℤ[X])
    (hF : NairTenenbaum.NoFixedPrimeDivisor F) (hdeg : 0 < F.natDegree)
    {α : ℝ} (hα : 0 < α) :
    ∃ x₀ > 0, ∃ C > 0, ∀ x y : ℝ, x₀ < x → x ^ α ≤ y → y ≤ x →
      polynomialDeltaShortSum F x y ≤
        C * (y * NairTenenbaum.sieveProduct F x * polynomialDeltaRootSum F x) := by
  obtain ⟨x₀, C, hx₀, hC, hbound⟩ :=
    NairTenenbaum.exists_hooleyPolynomialSum_root_bound F hF hdeg hα (t := 1) zero_lt_one
  refine ⟨x₀, hx₀, C, hC, fun x y hx hy hyx ↦ ?_⟩
  rw [polynomialDeltaShortSum_eq_nair, polynomialDeltaRootSum_eq_nair F (hx₀.le.trans hx.le)]
  exact hbound x y hx hy hyx

end BretecheTenenbaumMean
