module

public import BretecheTenenbaumMean.FixedPrimeDivisors
public import BretecheTenenbaumMean.PolynomialSquareFactor

@[expose] public section

/-! # Irreducible progression polynomials and their Delta sums -/

namespace BretecheTenenbaumMean

open Polynomial NairTenenbaum Finset Real

/-- Passing to the primitive part after an invertible rational affine
substitution preserves integral irreducibility. -/
theorem progressionPrimitive_irreducible {F : ℤ[X]} (hI : Irreducible F)
    (hdeg : 0 < F.natDegree) {q : ℕ} (hq : q ≠ 0) (a : ℤ) :
    Irreducible (progressionPrimitive F q a) := by
  let H := F.comp (affinePolynomial q a)
  have hF : Irreducible (F.map (Int.castRingHom ℚ)) :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast (hI.isPrimitive hdeg.ne')).1 hI
  have hH : Irreducible (H.map (Int.castRingHom ℚ)) := by
    dsimp only [H]
    rw [← rationalAffineEquiv_map q a hq]
    exact (MulEquiv.irreducible_iff (f := rationalAffineEquiv q a hq)).2 hF
  have hH0 : H ≠ 0 := by intro hz; simpa [hz] using hH.ne_zero
  have hd : H.content ≠ 0 := mt content_eq_zero_iff.1 hH0
  have hunit : IsUnit (C (H.content : ℚ)) := isUnit_C.2 (isUnit_iff_ne_zero.2 (by exact_mod_cast hd))
  have he : H.map (Int.castRingHom ℚ) =
      C (H.content : ℚ) * H.primPart.map (Int.castRingHom ℚ) := by
    conv_lhs => rw [H.eq_C_content_mul_primPart]
    rw [Polynomial.map_mul, map_C]
    rfl
  rw [he, irreducible_isUnit_mul hunit] at hH
  exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast H.isPrimitive_primPart).2 hH

/-- The original value is content times the normalized progression value. -/
theorem eval_eq_content_mul_progression (F : ℤ[X]) (q : ℕ) (a n : ℤ) :
    F.eval ((q : ℤ) * n + a) =
      (F.comp (affinePolynomial q a)).content * (progressionPrimitive F q a).eval n := by
  have he := congrArg (fun H : ℤ[X] ↦ H.eval n)
    (F.comp (affinePolynomial q a)).eq_C_content_mul_primPart
  simpa only [eval_comp, eval_affinePolynomial, eval_mul, eval_C, progressionPrimitive] using he

/-- Extracting the content costs a constant divisor-count factor. -/
theorem delta_eval_progression_le (F : ℤ[X]) (q : ℕ) (a n : ℤ) :
    (hooleyDelta (F.eval ((q : ℤ) * n + a)).natAbs : ℝ) ≤
      tau (F.comp (affinePolynomial q a)).content.natAbs *
        (hooleyDelta ((progressionPrimitive F q a).eval n).natAbs : ℝ) := by
  rw [eval_eq_content_mul_progression, Int.natAbs_mul]
  exact hooleyDelta_mul_le_tau _ _

/-- One finite collection of progression polynomials removes all fixed prime
divisors from a nonconstant irreducible polynomial. -/
theorem exists_irreducible_progressions {F : ℤ[X]} (hI : Irreducible F)
    (hdeg : 0 < F.natDegree) :
    ∃ q : ℕ, 0 < q ∧ ∀ a : ℤ,
      Irreducible (progressionPrimitive F q a) ∧
      NoFixedPrimeDivisor (progressionPrimitive F q a) := by
  have hF : Irreducible (F.map (Int.castRingHom ℚ)) :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast (hI.isPrimitive hdeg.ne')).1 hI
  have hD : F.discr ≠ 0 := discr_ne_zero_of_separable_map hF.separable
  exact ⟨fixedPrimeSlope F, fixedPrimeSlope_pos hD, fun a ↦
    ⟨progressionPrimitive_irreducible hI hdeg (fixedPrimeSlope_pos hD).ne' a,
      progressionPrimitive_noFixedPrime hD a⟩⟩

/-- A finite nonnegative sum is bounded by the full rectangular collection of
its quotient and residue coordinates. Enlarging the quotient range loses only
a constant depending on the fixed slope. -/
theorem sum_le_residue_rectangle (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    {q : ℕ} (hq : 0 < q) (N : ℕ) :
    (∑ n ∈ range (N + 1), f n) ≤
      ∑ a ∈ range q, ∑ m ∈ range (N + 1), f (q * m + a) := by
  classical
  let e : ℕ → ℕ × ℕ := fun n ↦ (n % q, n / q)
  have hinj : Set.InjOn e (↑(range (N + 1)) : Set ℕ) := by
    intro n _ m _ he
    have ha := congrArg Prod.fst he
    have hb := congrArg Prod.snd he
    have hn := Nat.mod_add_div n q
    have hm := Nat.mod_add_div m q
    dsimp only [e] at ha hb
    rw [ha, hb] at hn
    exact hn.symm.trans hm
  have hsub : (range (N + 1)).image e ⊆ range q ×ˢ range (N + 1) := by
    intro d hd
    obtain ⟨n, hn, rfl⟩ := mem_image.1 hd
    exact mem_product.2 ⟨mem_range.2 (Nat.mod_lt n hq),
      mem_range.2 ((Nat.div_le_self n q).trans_lt (mem_range.1 hn))⟩
  rw [← sum_product (f := fun d : ℕ × ℕ ↦ f (q * d.2 + d.1))]
  apply sum_le_sum_of_injOn e hinj hsub
  · intro n _
    dsimp only [e]
    rw [Nat.div_add_mod]
  · intro d _ _
    exact hf _

/-- The complete polynomial mean is bounded by finitely many normalized
progression means. The zero quotient is kept explicitly. -/
theorem polynomial_sum_le_progressions (F : ℤ[X]) {q : ℕ} (hq : 0 < q) (N : ℕ) :
    (∑ n ∈ Icc 1 N, (hooleyDelta (F.eval (n : ℤ)).natAbs : ℝ)) ≤
      ∑ a ∈ range q, tau (F.comp (affinePolynomial q (a : ℤ))).content.natAbs *
        ∑ m ∈ range (N + 1),
          (hooleyDelta ((progressionPrimitive F q (a : ℤ)).eval (m : ℤ)).natAbs : ℝ) := by
  calc
    _ ≤ ∑ n ∈ range (N + 1), (hooleyDelta (F.eval (n : ℤ)).natAbs : ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact mem_range.2 (by have := (mem_Icc.1 hn).2; omega)
      · intro n _ _
        exact Nat.cast_nonneg _
    _ ≤ ∑ a ∈ range q, ∑ m ∈ range (N + 1),
        (hooleyDelta (F.eval ((q * m + a : ℕ) : ℤ)).natAbs : ℝ) :=
      sum_le_residue_rectangle _ (fun _ ↦ Nat.cast_nonneg _) hq N
    _ ≤ _ := by
      apply sum_le_sum
      intro a _
      rw [mul_sum]
      apply sum_le_sum
      intro m _
      push_cast
      exact delta_eval_progression_le F q (a : ℤ) (m : ℤ)

end BretecheTenenbaumMean
