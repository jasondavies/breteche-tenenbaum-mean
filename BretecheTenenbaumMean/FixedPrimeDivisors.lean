module

public import BretecheTenenbaumMean.AffineContent

@[expose] public section

/-! # Removing fixed prime divisors by finitely many progressions

For a polynomial of degree at least two with nonzero discriminant, the
primitive part of `F(qX+a)`, with `q=(|disc F| degree(F)!)²`, has no fixed
prime divisor for every residue `a`. The same slope works for all residues.
-/

namespace BretecheTenenbaumMean

open Polynomial NairTenenbaum

noncomputable def fixedPrimeSlope (F : ℤ[X]) : ℕ :=
  (F.discr.natAbs * F.natDegree.factorial) ^ 2

noncomputable def progressionPrimitive (F : ℤ[X]) (q : ℕ) (a : ℤ) : ℤ[X] :=
  (F.comp (affinePolynomial q a)).primPart

theorem fixedPrimeSlope_pos {F : ℤ[X]} (hD : F.discr ≠ 0) : 0 < fixedPrimeSlope F := by
  unfold fixedPrimeSlope
  exact pow_pos (Nat.mul_pos (Int.natAbs_pos.2 hD) (Nat.factorial_pos _)) _

theorem progressionPrimitive_degree (F : ℤ[X]) {q : ℕ} (hq : q ≠ 0) (a : ℤ) :
    (progressionPrimitive F q a).natDegree = F.natDegree := by
  rw [progressionPrimitive, natDegree_primPart, natDegree_comp, natDegree_affinePolynomial hq, mul_one]

/-- The square in the chosen slope supplies an additional factor of every
prime dividing the slope, beyond the slope times the discriminant. -/
theorem prime_mul_slope_discr_dvd_sq {F : ℤ[X]} {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ fixedPrimeSlope F) :
    p * (fixedPrimeSlope F * F.discr.natAbs) ∣ fixedPrimeSlope F ^ 2 := by
  have hpL : p ∣ F.discr.natAbs * F.natDegree.factorial := hp.dvd_of_dvd_pow hpq
  have hpextra : p ∣ F.discr.natAbs * F.natDegree.factorial ^ 2 := by
    apply hpL.trans
    refine ⟨F.natDegree.factorial, ?_⟩
    ring
  have h := Nat.mul_dvd_mul_left (fixedPrimeSlope F * F.discr.natAbs) hpextra
  convert h using 1 <;> unfold fixedPrimeSlope <;> ring

/-- At primes dividing the slope, all higher coefficients of the primitive
part vanish. This includes residue classes in which `F(a)` is highly divisible. -/
theorem progressionPrimitive_coeff_dvd {F : ℤ[X]} (hdeg : 2 ≤ F.natDegree)
    (hD : F.discr ≠ 0) (a : ℤ) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ fixedPrimeSlope F) {i : ℕ} (hi : 2 ≤ i) :
    (p : ℤ) ∣ (progressionPrimitive F (fixedPrimeSlope F) a).coeff i := by
  let q := fixedPrimeSlope F
  let H := F.comp (affinePolynomial q a)
  have hq : q ≠ 0 := (fixedPrimeSlope_pos hD).ne'
  have hH0 : H ≠ 0 := by
    intro hz
    have he : H.natDegree = F.natDegree := by
      dsimp only [H]
      rw [natDegree_comp, natDegree_affinePolynomial hq, mul_one]
    rw [hz, natDegree_zero] at he
    omega
  have hd0 : H.content.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.2 (mt content_eq_zero_iff.1 hH0)
  have hd : H.content.natAbs ∣ q * F.discr.natAbs := by
    simpa only [H, Int.natAbs_mul, Int.natAbs_natCast] using
      Int.natAbs_dvd_natAbs.2 (content_comp_affine_dvd F hdeg q a)
  have hpd : p * H.content.natAbs ∣ q ^ 2 :=
    (Nat.mul_dvd_mul_left p hd).trans (prime_mul_slope_discr_dvd_sq hp hpq)
  have hcoeff : q ^ 2 ∣ (H.coeff i).natAbs := by
    simpa only [H, Int.natAbs_pow, Int.natAbs_natCast] using
      Int.natAbs_dvd_natAbs.2 (slope_sq_dvd_coeff_comp_affine F q a hi)
  have he : (H.coeff i).natAbs = H.content.natAbs * (H.primPart.coeff i).natAbs := by
    conv_lhs => rw [H.eq_C_content_mul_primPart]
    rw [coeff_C_mul, Int.natAbs_mul]
  have h := hpd.trans hcoeff
  rw [he, mul_comm p] at h
  have hn : p ∣ (H.primPart.coeff i).natAbs := (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hd0)).1 h
  exact Int.natCast_dvd.2 hn

/-- The chosen slope absorbs all primes that are too small for the degree
bound on roots. -/
theorem degree_lt_prime_of_not_dvd_slope {F : ℤ[X]} {p : ℕ} (hp : p.Prime)
    (hpq : ¬ p ∣ fixedPrimeSlope F) : F.natDegree < p := by
  by_contra! hle
  apply hpq
  exact (dvd_mul_of_dvd_right (Nat.dvd_factorial hp.pos hle) _).trans
    (dvd_pow_self _ (by norm_num : 2 ≠ 0))

/-- Every progression has a primitive polynomial with no fixed prime divisor. -/
theorem progressionPrimitive_noFixedPrime_of_two_le {F : ℤ[X]} (hdeg : 2 ≤ F.natDegree)
    (hD : F.discr ≠ 0) (a : ℤ) :
    NoFixedPrimeDivisor (progressionPrimitive F (fixedPrimeSlope F) a) := by
  intro p hp
  let G := progressionPrimitive F (fixedPrimeSlope F) a
  have hG : G.IsPrimitive := isPrimitive_primPart _
  have hroot := rootCount_le_reduced_degree hp (primitive_map_ne_zero hG hp)
  by_cases hpq : p ∣ fixedPrimeSlope F
  · have hdeg' : (G.map (Int.castRingHom (ZMod p))).natDegree ≤ 1 := by
      apply natDegree_le_iff_coeff_eq_zero.2
      intro i hi
      rw [coeff_map]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2
        (progressionPrimitive_coeff_dvd hdeg hD a hp hpq (by omega))
    exact hroot.trans_lt (hdeg'.trans_lt hp.one_lt)
  · have hdeg' : (G.map (Int.castRingHom (ZMod p))).natDegree ≤ F.natDegree :=
      natDegree_map_le.trans (progressionPrimitive_degree F (fixedPrimeSlope_pos hD).ne' a).le
    exact hroot.trans_lt (hdeg'.trans_lt (degree_lt_prime_of_not_dvd_slope hp hpq))

/-- The low-degree cases are covered by the root bound for a primitive
linear or constant polynomial. -/
theorem progressionPrimitive_noFixedPrime {F : ℤ[X]} (hD : F.discr ≠ 0) (a : ℤ) :
    NoFixedPrimeDivisor (progressionPrimitive F (fixedPrimeSlope F) a) := by
  by_cases hdeg : 2 ≤ F.natDegree
  · exact progressionPrimitive_noFixedPrime_of_two_le hdeg hD a
  · intro p hp
    have hG := isPrimitive_primPart (F.comp (affinePolynomial (fixedPrimeSlope F) a))
    have hr := rootCount_le_reduced_degree hp (primitive_map_ne_zero hG hp)
    have hd : ((progressionPrimitive F (fixedPrimeSlope F) a).map
        (Int.castRingHom (ZMod p))).natDegree ≤ 1 :=
      natDegree_map_le.trans ((progressionPrimitive_degree F (fixedPrimeSlope_pos hD).ne' a).le.trans
        (by omega))
    exact hr.trans_lt (hd.trans_lt hp.one_lt)

end BretecheTenenbaumMean
