module

public import BretecheTenenbaumMean.ExplicitThresholds
public import BretecheTenenbaumMean.PropositionTwoOne

@[expose] public section

/-! # Simultaneous control of all positive moments -/

namespace BretecheTenenbaumMean

open Finset Real

def allMomentGoodSet (δ T : ℝ) (θ : ℕ → ℝ) : Set ℕ :=
  {n | ∀ q : ℕ, n ∈ momentGoodSet δ T θ q}

theorem allMomentGoodSet_subset (δ T : ℝ) (θ : ℕ → ℝ) (q : ℕ) :
    allMomentGoodSet δ T θ ⊆ momentGoodSet δ T θ q := fun _ hn ↦ hn q

theorem momentGoodSet_two_eq_star (δ T : ℝ) {θ : ℕ → ℝ}
    (hθ1 : 1 ≤ θ 1) (hθ2 : T ≤ θ 2) : momentGoodSet δ T θ 2 = goodSetStar δ T := by
  ext n
  constructor
  · exact And.left
  · intro hn
    have ht := tau_pos hn.1.1.ne_zero
    refine ⟨hn, fun j hj hj2 ↦ ?_⟩
    have hj' : j = 1 ∨ j = 2 := by omega
    rcases hj' with rfl | rfl
    · rw [moment_one]
      have h := mul_le_mul_of_nonneg_left hθ1 ht.le
      simpa only [mul_one] using h
    · have h := (div_le_iff₀ ht).1 hn.2
      have hh := mul_le_mul_of_nonneg_right hθ2 ht.le
      nlinarith

/-- Any failure after order two occurs in one consecutive moment drop. -/
theorem allMomentGoodSet_failure_cover (δ T : ℝ) {θ : ℕ → ℝ}
    (hθ1 : 1 ≤ θ 1) (hθ2 : T ≤ θ 2) :
    (allMomentGoodSet δ T θ)ᶜ ⊆ (goodSetStar δ T)ᶜ ∪
      {n | ∃ j : ℕ, n ∈ momentGoodSet δ T θ (j + 2) \ momentGoodSet δ T θ (j + 3)} := by
  intro n hn
  by_cases hstar : n ∈ goodSetStar δ T
  · right
    by_contra hnot
    have h2 : n ∈ momentGoodSet δ T θ 2 := by rw [momentGoodSet_two_eq_star δ T hθ1 hθ2]; exact hstar
    have hall : ∀ j : ℕ, n ∈ momentGoodSet δ T θ (j + 2) := by
      intro j
      induction j with
      | zero => simpa only [zero_add] using h2
      | succ j ih =>
        have h : n ∈ momentGoodSet δ T θ (j + 3) := by
          by_contra hfail
          exact hnot ⟨j, ih, hfail⟩
        simpa only [Nat.add_assoc, Nat.reduceAdd] using h
    apply hn
    intro q
    by_cases hq : q ≤ 2
    · exact momentGoodSet_antitone δ T θ hq h2
    · have h := hall (q - 2)
      simpa only [Nat.sub_add_cancel (by omega : 2 ≤ q)] using h
  · exact Or.inl hstar

/-- Summing the Markov bounds loses only the convergent inverse-square sum. -/
theorem probability_allMomentGoodSet_compl_le {δ T x C₀ : ℝ} (hC : 0 ≤ C₀) (hT : 0 < T)
    (θ : ℕ → ℝ) (hθ : ∀ q, 0 < θ q) (hθ1 : 1 ≤ θ 1) (hθ2 : T ≤ θ 2)
    (hS : ∀ q : ℕ, 3 ≤ q → truncatedMoment δ T θ q x ≤ C₀ * θ q / ((q : ℝ) ^ 2 * T)) :
    probability x (allMomentGoodSet δ T θ)ᶜ ≤
      probability x (goodSetStar δ T)ᶜ + (C₀ * π ^ 2 / 6) / T := by
  classical
  let E := fun j : ℕ ↦ momentGoodSet δ T θ (j + 2) \ momentGoodSet δ T θ (j + 3)
  have hdrop : ∀ j : ℕ, probability x (E j) ≤ C₀ / (((j + 3 : ℕ) : ℝ) ^ 2 * T) := by
    intro j
    have hm := probability_momentGoodSet_drop δ T x θ (j + 2) (hθ _)
    have hs := div_le_div_of_nonneg_right (hS (j + 3) (by omega)) (hθ (j + 3)).le
    norm_num only [Nat.add_assoc, Nat.reduceAdd] at hm
    calc
      _ ≤ truncatedMoment δ T θ (j + 3) x / θ (j + 3) := hm
      _ ≤ (C₀ * θ (j + 3) / (((j + 3 : ℕ) : ℝ) ^ 2 * T)) / θ (j + 3) := hs
      _ = _ := by field_simp [(hθ (j + 3)).ne']
  obtain ⟨s, hs⟩ := probability_exists_le_finite_sum x E
  have hsum : (∑ j ∈ s, 1 / (((j + 3 : ℕ) : ℝ) ^ 2)) ≤ π ^ 2 / 6 := by
    have he : (∑ j ∈ s, 1 / (((j + 3 : ℕ) : ℝ) ^ 2)) =
        ∑ k ∈ s.image (fun j : ℕ ↦ (j + 3 : ℕ)), 1 / (k : ℝ) ^ 2 := by
      rw [sum_image (fun a _ b _ hab ↦ Nat.add_right_cancel hab)]
    rw [he]
    exact sum_inv_sq_le_pi_sq_div_six _
  have hprob : probability x {n | ∃ j : ℕ, n ∈ E j} ≤ (C₀ * π ^ 2 / 6) / T := by
    calc
      _ ≤ ∑ j ∈ s, probability x (E j) := hs
      _ ≤ ∑ j ∈ s, C₀ / (((j + 3 : ℕ) : ℝ) ^ 2 * T) := sum_le_sum (fun j _ ↦ hdrop j)
      _ = (C₀ / T) * ∑ j ∈ s, 1 / (((j + 3 : ℕ) : ℝ) ^ 2) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        ring
      _ ≤ (C₀ / T) * (π ^ 2 / 6) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring
  calc
    _ ≤ probability x ((goodSetStar δ T)ᶜ ∪ {n | ∃ j : ℕ, n ∈ E j}) :=
      probability_mono x (allMomentGoodSet_failure_cover δ T hθ1 hθ2)
    _ ≤ probability x (goodSetStar δ T)ᶜ + probability x {n | ∃ j : ℕ, n ∈ E j} :=
      probability_union_le x _ _
    _ ≤ _ := add_le_add le_rfl hprob

/-- The simultaneous moment exceptional probability in §2.4. -/
theorem allMomentGoodSet_probability_bound {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 1000000) :
    ∃ C₀ ≥ (1 : ℝ), ∃ C > 0, ∀ x T : ℝ, 2 ≤ x → 3 ≤ T →
      probability x (allMomentGoodSet δ T (explicitThreshold C₀ T))ᶜ ≤ C / T := by
  obtain ⟨C₀, hC₀, hS⟩ := propositionTwoTwo_for_delta hδ
  obtain ⟨A, hA, hgood⟩ := goodSet_exceptional_probability_bound hδ hδsmall
  obtain ⟨B, hB, hstar⟩ := probability_goodSetStar_compl_le hδ
  refine ⟨C₀, hC₀, A + B + C₀ * π ^ 2 / 6, by positivity, fun x T hx hT ↦ ?_⟩
  have hT0 : 0 < T := by linarith
  have hC0 : 0 < C₀ := by linarith
  have hadm := explicitThreshold_admissible hC₀ hT
  have hθ2 : T ≤ explicitThreshold C₀ T 2 := by
    have h := mul_le_mul_of_nonneg_right hC₀ hT0.le
    simp only [one_mul] at h
    exact h.trans hadm.2.2.1
  have hp := probability_allMomentGoodSet_compl_le hC0.le hT0 (explicitThreshold C₀ T)
    hadm.1 hadm.2.1 hθ2 (fun q hq ↦ hS T hT _ hadm q hq x hx)
  have hs := hstar x T hx (by linarith)
  have hg := hgood x T (by linarith)
  calc
    _ ≤ probability x (goodSetStar δ T)ᶜ + (C₀ * π ^ 2 / 6) / T := hp
    _ ≤ A / T + B / T + (C₀ * π ^ 2 / 6) / T := by linarith
    _ = _ := by ring

end BretecheTenenbaumMean
