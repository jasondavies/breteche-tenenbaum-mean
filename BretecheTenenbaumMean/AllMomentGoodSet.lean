module

public import BretecheTenenbaumMean.ExplicitThresholds
public import BretecheTenenbaumMean.GridEntropy
public import BretecheTenenbaumMean.PrimeSums.Grid
public import BretecheTenenbaumMean.GaussianGrid
public import BretecheTenenbaumMean.SecondMomentTail

@[expose] public section

/-! # Simultaneous control of all positive moments -/

namespace BretecheTenenbaumMean

open Finset Real

def allMomentGoodSet (δ T : ℝ) (θ : ℕ → ℝ) : Set ℕ :=
  {n | ∀ q : ℕ, n ∈ momentGoodSet δ T θ q}

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

end BretecheTenenbaumMean
