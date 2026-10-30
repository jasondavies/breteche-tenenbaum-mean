module

public import NairTenenbaum.Progressions.AffinePolynomialSystem
public import NairTenenbaum.Polynomials.DiscriminantBezout
public import Mathlib.Algebra.Polynomial.Taylor

@[expose] public section

/-! # Content after substitution along an arithmetic progression

The discriminant controls the content uniformly in the residue class.
Together with Taylor coefficients this will remove fixed prime divisors.
-/

namespace BretecheTenenbaumMean

open Polynomial NairTenenbaum

/-- Taylor coefficients after scaling the variable. -/
theorem coeff_comp_affine (F : ℤ[X]) (q : ℕ) (a : ℤ) (i : ℕ) :
    (F.comp (affinePolynomial q a)).coeff i = (taylor a F).coeff i * (q : ℤ) ^ i := by
  have he : F.comp (affinePolynomial q a) = (taylor a F).comp (C (q : ℤ) * X) := by
    simp only [taylor_apply, comp_assoc, add_comp, X_comp, C_comp, affinePolynomial]
  rw [he, comp_C_mul_X_coeff]

/-- The content divides the slope times the discriminant, independently of
the progression's residue. -/
theorem content_comp_affine_dvd (F : ℤ[X]) (hdeg : 2 ≤ F.natDegree) (q : ℕ) (a : ℤ) :
    (F.comp (affinePolynomial q a)).content ∣ (q : ℤ) * F.discr := by
  let H := F.comp (affinePolynomial q a)
  have hzero : H.content ∣ F.eval a := by
    have h := content_dvd_coeff (p := H) 0
    simpa only [H, coeff_comp_affine, pow_zero, mul_one, taylor_coeff_zero] using h
  have hone : H.content ∣ (q : ℤ) * F.derivative.eval a := by
    have h := content_dvd_coeff (p := H) 1
    simpa only [H, coeff_comp_affine, pow_one, taylor_coeff_one, mul_comm] using h
  obtain ⟨U, V, huv⟩ := exists_mul_add_mul_eq_C_discr F hdeg
  have he := congrArg (fun P : ℤ[X] ↦ P.eval a) huv
  simp only [eval_add, eval_mul, eval_C] at he
  rw [← he, mul_add]
  exact dvd_add (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hzero _) _)
    (by rw [← mul_assoc]; exact dvd_mul_of_dvd_left hone _)

/-- Every coefficient of degree at least two has two factors of the slope. -/
theorem slope_sq_dvd_coeff_comp_affine (F : ℤ[X]) (q : ℕ) (a : ℤ)
    {i : ℕ} (hi : 2 ≤ i) :
    (q : ℤ) ^ 2 ∣ (F.comp (affinePolynomial q a)).coeff i := by
  rw [coeff_comp_affine]
  exact dvd_mul_of_dvd_right (pow_dvd_pow _ hi) _

/-- Primitivity means reduction modulo any prime is nonzero as a polynomial. -/
theorem primitive_map_ne_zero {G : ℤ[X]} (hG : G.IsPrimitive)
    {p : ℕ} (hp : p.Prime) : G.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  intro hz
  have hdiv : C (p : ℤ) ∣ G := by
    apply (C_dvd_iff_dvd_coeff _ _).2
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
    have h := congrArg (fun Q : (ZMod p)[X] ↦ Q.coeff i) hz
    simpa only [coeff_map, coeff_zero, Int.coe_castRingHom] using h
  have hu := hG (p : ℤ) hdiv
  have hp1 : p = 1 := by simpa using Int.isUnit_iff_natAbs_eq.1 hu
  exact hp.ne_one hp1

/-- A nonzero reduction bounds roots by its actual reduced degree. -/
theorem rootCount_le_reduced_degree {G : ℤ[X]} {p : ℕ} (hp : p.Prime)
    (hG : G.map (Int.castRingHom (ZMod p)) ≠ 0) :
    rootCount G p ≤ (G.map (Int.castRingHom (ZMod p))).natDegree := by
  let : Fact p.Prime := ⟨hp⟩
  rw [rootCount_eq_card_filter G p]
  apply Polynomial.card_le_degree_of_subset_roots
  intro a ha
  apply (mem_roots hG).2
  simpa only [IsRoot, eval_map] using (Finset.mem_filter.1 ha).2

end BretecheTenenbaumMean
