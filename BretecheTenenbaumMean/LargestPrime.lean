module

public import BretecheTenenbaumMean.PrimeLayers
public import BretecheTenenbaumMean.GoodSets
public import BretecheTenenbaumMean.HalfRange

@[expose] public section

/-! # Decomposition by the largest prime factor -/

namespace BretecheTenenbaumMean

open Finset

/-- Partition subsets of an ordered finite set by their largest element. -/
theorem sum_powerset_by_max {α : Type*} [LinearOrder α] (s : Finset α)
    (f : Finset α → ℝ) :
    (∑ a ∈ s.powerset, f a) = f ∅ +
      ∑ p ∈ s, ∑ a ∈ (s.filter (fun r ↦ r < p)).powerset, f (insert p a) := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert p s hp ih =>
    have hps : p ∉ s := fun h ↦ (lt_irrefl p) (hp p h)
    have hfilter : (insert p s).filter (fun r ↦ r < p) = s := by
      ext r
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨hr | hr, hlt⟩
        · exact (lt_irrefl p (hr ▸ hlt)).elim
        · exact hr
      · intro hr
        exact ⟨Or.inr hr, hp r hr⟩
    have hfilters : ∀ q ∈ s,
        (insert p s).filter (fun r ↦ r < q) = s.filter (fun r ↦ r < q) := by
      intro q hq
      rw [filter_insert]
      simp only [not_lt.2 (hp q hq).le, ite_false]
    rw [sum_powerset_insert hps, ih, sum_insert hps, hfilter]
    simp_rw [sum_congr rfl (fun q hq ↦ congrArg (fun a : Finset α ↦
      ∑ b ∈ a.powerset, f (insert q b)) (hfilters q hq))]
    ring

/-- Every squarefree smooth integer other than one is uniquely `m*p`,
where `p` is its largest prime and all prime factors of `m` are strictly smaller. -/
theorem sum_smoothSupport_by_largest_prime (x : ℝ) (f : ℕ → ℝ) :
    (∑ n ∈ smoothSupport x, f n) = f 1 +
      ∑ p ∈ primesLT x, ∑ m ∈ smoothSupport p, f (m * p) := by
  classical
  rw [sum_smoothSupport_eq_powerset, sum_powerset_by_max]
  simp only [prod_empty]
  congr 1
  apply sum_congr rfl
  intro p hp
  have he : (primesLT x).filter (fun r ↦ r < p) = primesLT p := by
    ext r
    simp only [mem_filter, mem_primesLT]
    constructor
    · rintro ⟨⟨hr, _⟩, hrp⟩
      exact ⟨hr, by exact_mod_cast hrp⟩
    · rintro ⟨hr, hrp⟩
      exact ⟨⟨hr, hrp.trans (mem_primesLT.1 hp).2⟩, by exact_mod_cast hrp⟩
  rw [he, sum_smoothSupport_eq_powerset]
  apply sum_congr rfl
  intro s hs
  have hpnot : p ∉ s := by
    intro h
    have hlt := (mem_primesLT.1 ((mem_powerset.1 hs) h)).2
    exact (lt_irrefl (p : ℝ)) hlt
  rw [prod_insert hpnot, Nat.mul_comm]

/-- A prime at the cutoff cannot divide an integer in the strict smooth support. -/
theorem prime_not_dvd_of_mem_smoothSupport {p m : ℕ} (hp : p.Prime)
    (hm : m ∈ smoothSupport p) : ¬ p ∣ m := by
  intro hdiv
  have hs := mem_smoothSupport.1 hm
  have h := hs.2 p (Nat.mem_primeFactors.2 ⟨hp, hdiv, hs.1.ne_zero⟩)
  exact (lt_irrefl (p : ℝ)) h

/-- The normalized half-range recurrence at a new largest prime. -/
theorem normalized_moment_mul_prime_le {p m q : ℕ} (hp : p.Prime)
    (hm : m ∈ smoothSupport p) (hq : 1 ≤ q) :
    moment q (m * p) / tau (m * p) ≤
      moment q m / tau m + mixedRemainder q m p / tau m := by
  have hpn := prime_not_dvd_of_mem_smoothSupport hp hm
  have ht := tau_pos (mem_smoothSupport.1 hm).1.ne_zero
  rw [tau_mul_of_coprime (hp.coprime_iff_not_dvd.2 hpn).symm, tau_prime hp]
  have h := div_le_div_of_nonneg_right (moment_mul_prime_le hp hpn hq)
    (show 0 ≤ tau m * 2 by positivity)
  convert h using 1
  ring

/-- The unnormalized error term `V_q(x)` in §2.3. -/
noncomputable def recursionError (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  1 + ∑ p ∈ primesLT x, ∑ m ∈ smoothSupport p,
    (momentGoodSet δ T θ (q - 1)).indicator (fun m ↦ mixedRemainder q m p / tau m) m /
      ((m : ℝ) * p)

/-- The first largest-prime recursion for `L_x S_q(x)`. The divisor closure
of the moment good set justifies dropping its constraint on `m*p`. -/
theorem truncatedMoment_largest_prime_le (δ T : ℝ) (θ : ℕ → ℝ)
    {q : ℕ} (hq : 1 ≤ q) (x : ℝ) :
    normalizer x * truncatedMoment δ T θ q x ≤ recursionError δ T θ q x +
      ∑ p ∈ primesLT x, normalizer p * truncatedMoment δ T θ q p / p := by
  classical
  let E := momentGoodSet δ T θ (q - 1)
  let f := E.indicator (fun n ↦ moment q n / tau n)
  have hnorm : ∀ y : ℝ, normalizer y * truncatedMoment δ T θ q y =
      ∑ n ∈ smoothSupport y, f n / n := by
    intro y
    unfold truncatedMoment expectation
    dsimp only [f, E]
    field_simp [(normalizer_pos y).ne']
  rw [hnorm, sum_smoothSupport_by_largest_prime]
  have h1 : f 1 / (1 : ℕ) ≤ 1 := by
    dsimp only [f]
    by_cases h : 1 ∈ E
    · simp only [Set.indicator_of_mem h, tau_one, Nat.cast_one, div_one]
      simpa only [tau_one, one_pow] using moment_le_tau_pow 1 q hq
    · simp only [Set.indicator_of_notMem h, zero_div]; norm_num
  have hterm : ∀ p ∈ primesLT x, ∀ m ∈ smoothSupport p,
      f (m * p) / (m * p : ℕ) ≤
        (f m + E.indicator (fun m ↦ mixedRemainder q m p / tau m) m) / ((m : ℝ) * p) := by
    intro p hp m hm
    rw [Nat.cast_mul]
    apply div_le_div_of_nonneg_right _ (by positivity)
    by_cases hmp : m * p ∈ E
    · have hmE : m ∈ E := momentGoodSet_of_dvd hmp (Nat.dvd_mul_right m p)
      simp only [f, Set.indicator_of_mem hmp, Set.indicator_of_mem hmE]
      exact normalized_moment_mul_prime_le (mem_primesLT.1 hp).1 hm hq
    · simp only [f, Set.indicator_of_notMem hmp]
      apply add_nonneg
      · exact Set.indicator_nonneg (fun n _ ↦ div_nonneg (moment_nonneg _ _) (Nat.cast_nonneg _)) m
      · apply Set.indicator_nonneg _ m
        intro n _
        exact div_nonneg (sum_nonneg (fun j _ ↦ mul_nonneg (Nat.cast_nonneg _) (mixedMoment_nonneg _ _ _ _)))
          (Nat.cast_nonneg _)
  calc
    _ ≤ 1 + ∑ p ∈ primesLT x, ∑ m ∈ smoothSupport p,
        (f m + E.indicator (fun m ↦ mixedRemainder q m p / tau m) m) / ((m : ℝ) * p) :=
      add_le_add h1 (sum_le_sum (fun p hp ↦ sum_le_sum (hterm p hp)))
    _ = _ := by
      simp_rw [hnorm, add_div, div_mul_eq_div_div, sum_add_distrib, sum_div]
      unfold recursionError
      dsimp only [E]
      ring_nf

end BretecheTenenbaumMean
