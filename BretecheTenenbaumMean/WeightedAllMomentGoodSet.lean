module

public import BretecheTenenbaumMean.AllMomentGoodSet
public import BretecheTenenbaumMean.WeightedPropositionTwoTwo
public import BretecheTenenbaumMean.WeightedSecondMomentTail

@[expose] public section

/-! # Simultaneous weighted moment control -/

namespace BretecheTenenbaumMean.WeightedModel

open Finset Real

theorem probability_momentGoodSet_drop (w : MultiplicativeWeight) (δ T x : ℝ) (θ : ℕ → ℝ) (q : ℕ)
    (hθ : 0 < θ (q + 1)) :
    probability w x (momentGoodSet δ T θ q \ momentGoodSet δ T θ (q + 1)) ≤
      truncatedMoment w δ T θ (q + 1) x / θ (q + 1) := by
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
  simpa [truncatedMoment, f] using probability_gt_le w x f hf hθ


theorem probability_allMomentGoodSet_compl_le (w : MultiplicativeWeight) {δ T x C₀ : ℝ} (hC : 0 ≤ C₀) (hT : 0 < T)
    (θ : ℕ → ℝ) (hθ : ∀ q, 0 < θ q) (hθ1 : 1 ≤ θ 1) (hθ2 : T ≤ θ 2)
    (hS : ∀ q : ℕ, 3 ≤ q → truncatedMoment w δ T θ q x ≤ C₀ * θ q / ((q : ℝ) ^ 2 * T)) :
    probability w x (allMomentGoodSet δ T θ)ᶜ ≤
      probability w x (goodSetStar δ T)ᶜ + (C₀ * π ^ 2 / 6) / T := by
  classical
  let E := fun j : ℕ ↦ momentGoodSet δ T θ (j + 2) \ momentGoodSet δ T θ (j + 3)
  have hdrop : ∀ j : ℕ, probability w x (E j) ≤ C₀ / (((j + 3 : ℕ) : ℝ) ^ 2 * T) := by
    intro j
    have hm := probability_momentGoodSet_drop w δ T x θ (j + 2) (hθ _)
    have hs := div_le_div_of_nonneg_right (hS (j + 3) (by omega)) (hθ (j + 3)).le
    norm_num only [Nat.add_assoc, Nat.reduceAdd] at hm
    calc
      _ ≤ truncatedMoment w δ T θ (j + 3) x / θ (j + 3) := hm
      _ ≤ (C₀ * θ (j + 3) / (((j + 3 : ℕ) : ℝ) ^ 2 * T)) / θ (j + 3) := hs
      _ = _ := by field_simp [(hθ (j + 3)).ne']
  obtain ⟨s, hs⟩ := probability_exists_le_finite_sum w x E
  have hsum : (∑ j ∈ s, 1 / (((j + 3 : ℕ) : ℝ) ^ 2)) ≤ π ^ 2 / 6 := by
    have he : (∑ j ∈ s, 1 / (((j + 3 : ℕ) : ℝ) ^ 2)) =
        ∑ k ∈ s.image (fun j : ℕ ↦ (j + 3 : ℕ)), 1 / (k : ℝ) ^ 2 := by
      rw [sum_image (fun a _ b _ hab ↦ Nat.add_right_cancel hab)]
    rw [he]
    exact sum_inv_sq_le_pi_sq_div_six _
  have hprob : probability w x {n | ∃ j : ℕ, n ∈ E j} ≤ (C₀ * π ^ 2 / 6) / T := by
    calc
      _ ≤ ∑ j ∈ s, probability w x (E j) := hs
      _ ≤ ∑ j ∈ s, C₀ / (((j + 3 : ℕ) : ℝ) ^ 2 * T) := sum_le_sum (fun j _ ↦ hdrop j)
      _ = (C₀ / T) * ∑ j ∈ s, 1 / (((j + 3 : ℕ) : ℝ) ^ 2) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        ring
      _ ≤ (C₀ / T) * (π ^ 2 / 6) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring
  calc
    _ ≤ probability w x ((goodSetStar δ T)ᶜ ∪ {n | ∃ j : ℕ, n ∈ E j}) :=
      probability_mono w x (allMomentGoodSet_failure_cover δ T hθ1 hθ2)
    _ ≤ probability w x (goodSetStar δ T)ᶜ + probability w x {n | ∃ j : ℕ, n ∈ E j} :=
      probability_union_le w x _ _
    _ ≤ _ := add_le_add le_rfl hprob


theorem allMomentGoodSet_probability_bound (w : MultiplicativeWeight) (hpw : PrimeEstimates w) {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 1000000) :
    ∃ C₀ ≥ (1 : ℝ), ∃ C > 0, ∀ x T : ℝ, 2 ≤ x → 3 ≤ T →
      probability w x (allMomentGoodSet δ T (explicitThreshold C₀ T))ᶜ ≤ C / T := by
  obtain ⟨C₀, hC₀, hS⟩ := propositionTwoTwo_for_delta w hpw hδ
  obtain ⟨A, hA, hgood⟩ := hpw.goodSet_exceptional_bound hδ hδsmall
  obtain ⟨B, hB, hstar⟩ := probability_goodSetStar_compl_le w hpw hδ
  refine ⟨C₀, hC₀, A + B + C₀ * π ^ 2 / 6, by positivity, fun x T hx hT ↦ ?_⟩
  have hT0 : 0 < T := by linarith
  have hC0 : 0 < C₀ := by linarith
  have hadm := explicitThreshold_admissible hC₀ hT
  have hθ2 : T ≤ explicitThreshold C₀ T 2 := by
    have h := mul_le_mul_of_nonneg_right hC₀ hT0.le
    simp only [one_mul] at h
    exact h.trans hadm.2.2.1
  have hp := probability_allMomentGoodSet_compl_le w hC0.le hT0 (explicitThreshold C₀ T)
    hadm.1 hadm.2.1 hθ2 (fun q hq ↦ hS T hT _ hadm q hq x hx)
  have hs := hstar x T hx (by linarith)
  have hg := hgood x T (by linarith)
  calc
    _ ≤ probability w x (goodSetStar δ T)ᶜ + (C₀ * π ^ 2 / 6) / T := hp
    _ ≤ A / T + B / T + (C₀ * π ^ 2 / 6) / T := by linarith
    _ = _ := by ring


end BretecheTenenbaumMean.WeightedModel
