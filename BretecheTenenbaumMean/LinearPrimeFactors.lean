module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import NairTenenbaum.RootCount

@[expose] public section

/-! # Roots modulo primes and prime ideals of residue degree one -/

namespace BretecheTenenbaumMean

open Polynomial UniqueFactorizationMonoid NumberField
open scoped NumberField

/-- A root determines a distinct monic linear factor, without a separability
hypothesis. Multiplicity is deliberately discarded. -/
noncomputable def rootsEquivLinearFactors {k : Type*} [Field k] [DecidableEq k] (F : k[X]) (hF : F ≠ 0) :
    {a : k // F.eval a = 0} ≃
      {Q : {Q : k[X] // Q ∈ (normalizedFactors F).toFinset} //
        Q.val.natDegree = 1} := by
  classical
  refine
    { toFun := fun a ↦ ⟨⟨X - C a.val, ?_⟩, natDegree_X_sub_C _⟩
      invFun := fun Q ↦ ⟨-Q.val.val.coeff 0, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · simp only [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hF]
    exact ⟨irreducible_X_sub_C _, monic_X_sub_C _, dvd_iff_isRoot.mpr a.prop⟩
  · have hQ := (Polynomial.mem_normalizedFactors_iff hF).mp
      (Multiset.mem_toFinset.mp Q.val.prop)
    have heq := hQ.2.1.eq_X_add_C Q.prop
    obtain ⟨G, hG⟩ := hQ.2.2
    have hz : Q.val.val.eval (-Q.val.val.coeff 0) = 0 := by
      simpa only [eval_add, eval_X, eval_C, neg_add_cancel] using
        congrArg (eval (-Q.val.val.coeff 0)) heq
    calc
      _ = (Q.val.val * G).eval (-Q.val.val.coeff 0) := congrArg (eval _) hG
      _ = 0 := by rw [eval_mul, hz, zero_mul]
  · intro a
    apply Subtype.ext
    simp
  · intro Q
    apply Subtype.ext
    apply Subtype.ext
    have hQ := (Polynomial.mem_normalizedFactors_iff hF).mp
      (Multiset.mem_toFinset.mp Q.val.prop)
    simpa using (hQ.2.1.eq_X_add_C Q.prop).symm

/-- The degree-one part of Kummer–Dedekind, expressed directly as an
 equivalence with roots of the minimal polynomial modulo the rational prime. -/
noncomputable def minpolyRootsEquivDegreeOnePrimes {K : Type*} [Field K] [NumberField K]
    (θ : 𝓞 K) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ RingOfIntegers.exponent θ) :
    NairTenenbaum.ResidueRoots (minpoly ℤ θ) p ≃
      {P : Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K) //
        Ideal.inertiaDeg (P.val) ℤ = 1} := by
  classical
  let F := (minpoly ℤ θ).map (Int.castRingHom (ZMod p))
  have hF : F ≠ 0 := map_monic_ne_zero (minpoly.monic θ.isIntegral)
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp
  let r : NairTenenbaum.ResidueRoots (minpoly ℤ θ) p ≃ {a : ZMod p // F.eval a = 0} :=
    Equiv.subtypeEquivRight (fun a ↦ by simp [F, eval_map])
  refine r.trans ((rootsEquivLinearFactors F hF).trans ?_)
  refine
    { toFun := fun Q ↦ ⟨e.symm Q.val, ?_⟩
      invFun := fun P ↦ ⟨e P.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply']
    exact Q.prop
  · have h := NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
      hp (e P.val).prop
    change Ideal.inertiaDeg (e.symm (e P.val)).val ℤ = _ at h
    rw [e.symm_apply_apply] at h
    exact h.symm.trans P.prop
  · intro Q
    apply Subtype.ext
    exact e.apply_symm_apply Q.val
  · intro P
    apply Subtype.ext
    exact e.symm_apply_apply P.val

end BretecheTenenbaumMean
