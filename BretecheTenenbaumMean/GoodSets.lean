module

public import BretecheTenenbaumMean.Probability
public import BretecheTenenbaumMean.MomentRecurrence

@[expose] public section

/-! # The sets in §§2.1--2.3

`δ` is a parameter here. The existence of a sufficiently small positive choice
with the claimed probability estimates is a separate analytic proof obligation.
-/

namespace BretecheTenenbaumMean

open Real Finset

theorem smallPrimePart_dvd (n : ℕ) (y : ℝ) : smallPrimePart n y ∣ n := by
  apply dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _))
  exact Nat.prod_primeFactors_dvd n

theorem smallPrimePart_eq_self {n : ℕ} (hn : Squarefree n) {y : ℝ}
    (h : ∀ p ∈ n.primeFactors, (p : ℝ) < y) : smallPrimePart n y = n := by
  rw [smallPrimePart, Finset.filter_eq_self.mpr h, Nat.prod_primeFactors_of_squarefree hn]

theorem smallPrimePart_ne_zero (n : ℕ) (y : ℝ) : smallPrimePart n y ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero

theorem smallPrimePart_dvd_of_dvd {d n : ℕ} (hn : n ≠ 0) (hd : d ∣ n) (y : ℝ) :
    smallPrimePart d y ∣ smallPrimePart n y := by
  apply Finset.prod_dvd_prod_of_subset
  exact Finset.filter_subset_filter _ (Nat.primeFactors_mono hd hn)

theorem tau_le_of_dvd {d n : ℕ} (hn : n ≠ 0) (hd : d ∣ n) : tau d ≤ tau n := by
  unfold tau
  exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hn hd)

theorem goodSet_of_dvd {δ T : ℝ} {d n : ℕ} (hn : n ∈ goodSet δ T) (hd : d ∣ n) :
    d ∈ goodSet δ T := by
  refine ⟨hn.1.squarefree_of_dvd hd, fun y hy => ?_⟩
  exact (tau_le_of_dvd (smallPrimePart_ne_zero n y)
    (smallPrimePart_dvd_of_dvd hn.1.ne_zero hd y)).trans (hn.2 y hy)

theorem goodSetStar_of_dvd {δ T : ℝ} {d n : ℕ} (hn : n ∈ goodSetStar δ T) (hd : d ∣ n) :
    d ∈ goodSetStar δ T := by
  exact ⟨goodSet_of_dvd hn.1 hd,
    (normalized_moment_le_of_dvd hn.1.1 hd (by norm_num)).trans hn.2⟩

theorem momentGoodSet_of_dvd {δ T : ℝ} {θ : ℕ → ℝ} {q d n : ℕ}
    (hn : n ∈ momentGoodSet δ T θ q) (hd : d ∣ n) : d ∈ momentGoodSet δ T θ q := by
  refine ⟨goodSetStar_of_dvd hn.1 hd, fun j hj hjq => ?_⟩
  have hn0 := hn.1.1.1.ne_zero
  have hd0 := (hn.1.1.1.squarefree_of_dvd hd).ne_zero
  have hbound : moment j n / tau n ≤ θ j :=
    (div_le_iff₀ (tau_pos hn0)).mpr (by simpa [mul_comm] using hn.2 j hj hjq)
  have h := (normalized_moment_le_of_dvd hn.1.1.1 hd hj).trans hbound
  simpa [mul_comm] using (div_le_iff₀ (tau_pos hd0)).mp h

theorem momentGoodSet_antitone (δ T : ℝ) (θ : ℕ → ℝ) :
    Antitone (momentGoodSet δ T θ) := by
  intro p q hpq n hn
  exact ⟨hn.1, fun j hj hjp => hn.2 j hj (hjp.trans hpq)⟩

theorem momentGoodSet_zero (δ T : ℝ) (θ : ℕ → ℝ) :
    momentGoodSet δ T θ 0 = goodSetStar δ T := by
  ext n
  simp only [momentGoodSet, Set.mem_ofPred_eq]
  constructor
  · exact And.left
  · intro h
    exact ⟨h, fun j hj hj0 => by omega⟩

theorem momentGoodSet_one (δ T : ℝ) {θ : ℕ → ℝ} (hθ : 1 ≤ θ 1) :
    momentGoodSet δ T θ 1 = goodSetStar δ T := by
  ext n
  constructor
  · exact And.left
  · intro hn
    refine ⟨hn, fun j hj hj1 => ?_⟩
    have : j = 1 := by omega
    subst j
    rw [moment_one]
    simpa [tau] using mul_le_mul_of_nonneg_left hθ (Nat.cast_nonneg n.divisors.card)

theorem momentGoodSet_succ (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ) :
    momentGoodSet δ T θ (q + 1) =
      momentGoodSet δ T θ q ∩ {n | moment (q + 1) n ≤ tau n * θ (q + 1)} := by
  ext n
  constructor
  · intro h
    exact ⟨⟨h.1, fun j hj hjq => h.2 j hj (by omega)⟩, h.2 _ (by omega) le_rfl⟩
  · rintro ⟨h, hq⟩
    refine ⟨h.1, fun j hj hjq => ?_⟩
    rcases eq_or_lt_of_le hjq with rfl | hjq
    · exact hq
    · exact h.2 j hj (by omega)

/-- The Markov step of §2.4, with denominator `θ(q+1)`. -/
theorem probability_momentGoodSet_drop (δ T x : ℝ) (θ : ℕ → ℝ) (q : ℕ)
    (hθ : 0 < θ (q + 1)) :
    probability x (momentGoodSet δ T θ q \ momentGoodSet δ T θ (q + 1)) ≤
      truncatedMoment δ T θ (q + 1) x / θ (q + 1) := by
  classical
  let f : ℕ → ℝ := (momentGoodSet δ T θ q).indicator
    (fun n => moment (q + 1) n / tau n)
  have he : momentGoodSet δ T θ q \ momentGoodSet δ T θ (q + 1) =
      {n | θ (q + 1) < f n} := by
    rw [momentGoodSet_succ]
    ext n
    by_cases hn : n ∈ momentGoodSet δ T θ q
    · have hτ := tau_pos hn.1.1.1.ne_zero
      simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, hn, true_and,
        not_le, f, Set.indicator_of_mem hn]
      rw [lt_div_iff₀ hτ, mul_comm (θ (q + 1))]
    · simp [hn, f, not_lt.mpr hθ.le]
  rw [he]
  have hf : ∀ n ∈ smoothSupport x, 0 ≤ f n := by
    intro n _
    apply Set.indicator_nonneg _ n
    intro k _
    exact div_nonneg (moment_nonneg _ _) (Nat.cast_nonneg _)
  simpa [truncatedMoment, f] using probability_gt_le x hf hθ

end BretecheTenenbaumMean
