module

public import BretecheTenenbaumMean.PrimeLayers
public import BretecheTenenbaumMean.SmallPrimePolynomial
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! # Splitting squarefree sums across disjoint prime ranges -/

namespace BretecheTenenbaumMean

open Finset Real

/-- An exact splitting of a sum over subsets of two disjoint sets. -/
theorem sum_powerset_disjoint_union {α : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B) (F : Finset α → ℝ) :
    (∑ s ∈ (A ∪ B).powerset, F s) =
      ∑ a ∈ A.powerset, ∑ b ∈ B.powerset, F (a ∪ b) := by
  induction B using Finset.induction_on generalizing F with
  | empty => simp
  | @insert p B hp ih =>
      have hpA : p ∉ A := fun h ↦ disjoint_left.1 hAB h (mem_insert_self _ _)
      have hAB' : Disjoint A B := hAB.mono_right (subset_insert _ _)
      have hpAB : p ∉ A ∪ B := by simp only [mem_union, not_or]; exact ⟨hpA, hp⟩
      rw [union_insert, sum_powerset_insert hpAB, ih hAB', ih hAB']
      simp_rw [sum_powerset_insert hp, sum_add_distrib, union_insert]

/-- Fixing the number of selected elements in the first range leaves an Euler
product over the second range. -/
theorem fixed_layer_product_split {α : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B) (w : α → ℝ) (r : ℕ) :
    (∑ s ∈ (A ∪ B).powerset, if (s ∩ A).card = r then ∏ p ∈ s, w p else 0) =
      distinctProductSum A w r * ∏ p ∈ B, (1 + w p) := by
  rw [sum_powerset_disjoint_union A B hAB]
  have he : ∀ a ∈ A.powerset, ∀ b ∈ B.powerset,
      (if ((a ∪ b) ∩ A).card = r then ∏ p ∈ a ∪ b, w p else 0) =
        (if a.card = r then ∏ p ∈ a, w p else 0) * ∏ p ∈ b, w p := by
    intro a ha b hb
    have haA := mem_powerset.1 ha
    have hbB := mem_powerset.1 hb
    have hd : Disjoint a b := hAB.mono haA hbB
    have hbA : Disjoint b A := hAB.symm.mono_left hbB
    rw [union_inter_distrib_right, inter_eq_left.2 haA, disjoint_iff_inter_eq_empty.1 hbA, union_empty, prod_union hd]
    split_ifs <;> simp only [zero_mul]
  calc (∑ a ∈ A.powerset, ∑ b ∈ B.powerset,
      if ((a ∪ b) ∩ A).card = r then ∏ p ∈ a ∪ b, w p else 0) =
      ∑ a ∈ A.powerset, ∑ b ∈ B.powerset,
        (if a.card = r then ∏ p ∈ a, w p else 0) * ∏ p ∈ b, w p :=
          sum_congr rfl (fun a ha ↦ sum_congr rfl (fun b hb ↦ he a ha b hb))
    _ = _ := by
      simp_rw [← mul_sum, ← prod_one_add]
      rw [← sum_mul]
      congr 1
      rw [distinctProductSum, powersetCard_eq_filter, sum_filter]

/-- The same factorization with the first range specified as a subset. -/
theorem fixed_layer_product_split_subset {α : Type*} [DecidableEq α]
    (P A : Finset α) (hA : A ⊆ P) (w : α → ℝ) (r : ℕ) :
    (∑ s ∈ P.powerset, if (s ∩ A).card = r then ∏ p ∈ s, w p else 0) =
      distinctProductSum A w r * ∏ p ∈ P \ A, (1 + w p) := by
  have hd : Disjoint A (P \ A) := by
    apply disjoint_left.2
    intro p hp hpd
    exact (mem_sdiff.1 hpd).2 hp
  have h := fixed_layer_product_split A (P \ A) hd w r
  rwa [union_sdiff_of_subset hA] at h

/-- Multiplicativity on coprime integers gives a product over a finite set of primes. -/
theorem map_prod_primes (f : ℕ → ℝ) (hf1 : f 1 = 1)
    (hfm : ∀ m n, m.Coprime n → f (m * n) = f m * f n)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    f (∏ p ∈ s, p) = ∏ p ∈ s, f p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hf1
  | @insert p s hp ih =>
      have hpp : p.Prime := hs p (mem_insert_self _ _)
      have hss : ∀ q ∈ s, q.Prime := fun q hq ↦ hs q (mem_insert_of_mem hq)
      have hc : p.Coprime (∏ q ∈ s, q) := Nat.Coprime.prod_right (fun q hq ↦
        (Nat.coprime_primes hpp (hss q hq)).2 (fun he ↦ hp (he ▸ hq)))
      rw [prod_insert hp, prod_insert hp, hfm _ _ hc, ih hss]

/-- The subset representing the small-prime part. -/
theorem smallPrimePart_prod {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (y : ℝ) :
    smallPrimePart (∏ p ∈ s, p) y = ∏ p ∈ s.filter (fun p : ℕ ↦ (p : ℝ) < y), p := by
  rw [smallPrimePart, Nat.primeFactors_prod hs]

/-- Its prime-factor count is the number of selected primes below the cutoff. -/
theorem primeFactors_smallPrimePart_prod {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (y : ℝ) :
    (smallPrimePart (∏ p ∈ s, p) y).primeFactors = s.filter (fun p : ℕ ↦ (p : ℝ) < y) := by
  rw [smallPrimePart_prod hs, Nat.primeFactors_prod (fun p hp ↦ hs p (mem_filter.1 hp).1)]

/-- A multiplicative weighted sum with prescribed small-prime count, expressed
entirely in terms of subsets of the allowed primes. -/
theorem sum_smallPrime_layer_eq_powerset (x y : ℝ) (r : ℕ) (f : ℕ → ℝ) (hf1 : f 1 = 1)
    (hfm : ∀ m n, m.Coprime n → f (m * n) = f m * f n) :
    (∑ n ∈ smoothSupport x, if (smallPrimePart n y).primeFactors.card = r then f n / n else 0) =
      ∑ s ∈ (primesLT x).powerset,
        if (s ∩ (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < y)).card = r
        then ∏ p ∈ s, f p / p else 0 := by
  classical
  rw [sum_smoothSupport_eq_powerset]
  apply sum_congr rfl
  intro s hs
  have hsub := mem_powerset.1 hs
  have hprime : ∀ p ∈ s, p.Prime := fun p hp ↦ (mem_primesLT.1 (hsub hp)).1
  have he : s.filter (fun p : ℕ ↦ (p : ℝ) < y) =
      s ∩ (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < y) := by
    ext p
    simp only [mem_filter, mem_inter]
    exact ⟨fun h ↦ ⟨h.1, hsub h.1, h.2⟩, fun h ↦ ⟨h.1, h.2.2⟩⟩
  rw [primeFactors_smallPrimePart_prod hprime, he]
  split_ifs
  · rw [map_prod_primes f hf1 hfm s hprime, Nat.cast_prod, prod_div_distrib]
  · rfl

/-- Exact factorization of a multiplicative sum restricted by its small-prime count. -/
theorem sum_smallPrime_layer_eq_product (x y : ℝ) (r : ℕ) (f : ℕ → ℝ) (hf1 : f 1 = 1)
    (hfm : ∀ m n, m.Coprime n → f (m * n) = f m * f n) :
    (∑ n ∈ smoothSupport x, if (smallPrimePart n y).primeFactors.card = r then f n / n else 0) =
      distinctProductSum ((primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < y)) (fun p ↦ f p / p) r *
      ∏ p ∈ primesLT x \ (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < y), (1 + f p / p) := by
  rw [sum_smallPrime_layer_eq_powerset x y r f hf1 hfm]
  exact fixed_layer_product_split_subset _ _ (filter_subset _ _) _ r

/-- A primewise nonnegative majorant may replace the multiplicative weight. -/
theorem sum_smallPrime_layer_le_product (x y : ℝ) (r : ℕ) (f v : ℕ → ℝ) (hf1 : f 1 = 1)
    (hfm : ∀ m n, m.Coprime n → f (m * n) = f m * f n)
    (hf : ∀ p ∈ primesLT x, 0 ≤ f p) (hv : ∀ p ∈ primesLT x, f p ≤ v p) :
    (∑ n ∈ smoothSupport x, if (smallPrimePart n y).primeFactors.card = r then f n / n else 0) ≤
      distinctProductSum ((primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < y)) (fun p ↦ v p / p) r *
      ∏ p ∈ primesLT x \ (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < y), (1 + v p / p) := by
  classical
  rw [sum_smallPrime_layer_eq_powerset x y r f hf1 hfm,
    ← fixed_layer_product_split_subset _ _ (filter_subset _ _) _ r]
  apply sum_le_sum
  intro s hs
  have hsub := mem_powerset.1 hs
  split_ifs
  · apply prod_le_prod₀
    · exact fun p hp ↦ div_nonneg (hf p (hsub hp)) (Nat.cast_nonneg p)
    · exact fun p hp ↦ div_le_div_of_nonneg_right (hv p (hsub hp)) (Nat.cast_nonneg p)
  · exact le_rfl

end BretecheTenenbaumMean
