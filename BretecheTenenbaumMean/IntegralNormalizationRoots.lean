module

public import NairTenenbaum.Polynomials.RootCount
public import Mathlib.RingTheory.Polynomial.IntegralNormalization

@[expose] public section

/-! # Root counts are preserved by integral normalization at good primes -/

namespace BretecheTenenbaumMean

open Polynomial

/-- Multiplication by the leading coefficient bijects the roots of `F` with
those of its integral normalization whenever that coefficient is nonzero modulo `p`. -/
noncomputable def rootsEquivIntegralNormalization (F : ℤ[X]) (hdeg : 0 < F.natDegree)
    (p : ℕ) [Fact p.Prime] (hc : (F.leadingCoeff : ZMod p) ≠ 0) :
    NairTenenbaum.ResidueRoots F p ≃ NairTenenbaum.ResidueRoots F.integralNormalization p := by
  let c : ZMod p := F.leadingCoeff
  have heval (a : ZMod p) :
      F.integralNormalization.eval₂ (Int.castRingHom (ZMod p)) (c * a) =
        c ^ (F.natDegree - 1) * F.eval₂ (Int.castRingHom (ZMod p)) a :=
    integralNormalization_eval₂_leadingCoeff_mul hdeg (Int.castRingHom (ZMod p)) a
  refine
    { toFun := fun a ↦ ⟨c * a.val, ?_⟩
      invFun := fun b ↦ ⟨c⁻¹ * b.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [heval, a.prop, mul_zero]
  · have h := heval (c⁻¹ * b.val)
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul, b.prop] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ hc)
  · intro a
    apply Subtype.ext
    simp [hc, c]
  · intro b
    apply Subtype.ext
    simp [hc, c]

/-- Passing to the monic integral normalization leaves the prime root weight
unchanged away from divisors of the leading coefficient. -/
theorem rootCount_integralNormalization (F : ℤ[X]) (hdeg : 0 < F.natDegree)
    (p : ℕ) [Fact p.Prime] (hc : (F.leadingCoeff : ZMod p) ≠ 0) :
    NairTenenbaum.rootCount F.integralNormalization p = NairTenenbaum.rootCount F p :=
  (Nat.card_congr (rootsEquivIntegralNormalization F hdeg p hc)).symm

end BretecheTenenbaumMean
