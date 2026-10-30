module

public import BretecheTenenbaumMean.WeightedHighFrequencyMean
public import BretecheTenenbaumMean.WeightedInitialFrequency
public import BretecheTenenbaumMean.WeightedEventBounds
public import BretecheTenenbaumMean.SecondMomentTail

@[expose] public section

/-! # Weighted second-moment tails and the exceptional set -/

namespace BretecheTenenbaumMean.WeightedModel

open Real MeasureTheory

theorem high_frequency_probability_bound (w : MultiplicativeWeight) (hp : PrimeEstimates w) {δ : ℝ} (hδ : 0 < δ) : ∃ C > 0, ∀ T x a R,
    1 < T → 0 < a → a ≤ 1 → exp a⁻¹ ≤ x → 0 < R →
    probability w x {n | n ∈ goodSet δ T ∧ R < frequencyIntegral n a 1} ≤ C * T / R ^ 2 := by
  obtain ⟨C, hC, hmean⟩ := high_frequency_second_moment_bound w hp hδ
  refine ⟨C, hC, fun T x a R hT ha ha1 hx hR ↦ ?_⟩
  exact (probability_inter_gt_sq_le w x (goodSet δ T) (fun n ↦ frequencyIntegral n a 1) hR).trans
    (div_le_div_of_nonneg_right (hmean T x a hT ha ha1 hx) (sq_nonneg R))


theorem goodSet_second_moment_probability_bound (w : MultiplicativeWeight) (hp : PrimeEstimates w) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ x T, 2 ≤ x → 1 < T →
      probability w x {n | n ∈ goodSet δ T ∧ T < moment 2 n / tau n} ≤ C / T := by
  classical
  obtain ⟨C₀, hC₀, hinitial⟩ := initial_frequency_probability_bound w hp
  obtain ⟨C₁, hC₁, hhigh⟩ := high_frequency_probability_bound w hp hδ
  let A := π ^ 2 / 2
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨2 * A * C₀ + 4 * A ^ 2 * C₁, by positivity, fun x T hx hT ↦ ?_⟩
  have hT0 : 0 < T := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  let R := T / (2 * A)
  have hR : 0 < R := div_pos hT0 (by positivity)
  by_cases hlarge : exp 1 ≤ x
  · let a := (log x)⁻¹
    have hlog1 : 1 ≤ log x := (le_log_iff_exp_le (by linarith : 0 < x)).2 hlarge
    have ha : 0 < a := inv_pos.2 hl
    have ha1 : a ≤ 1 := (inv_le_one₀ hl).2 hlog1
    have haL : a * log x ≤ 1 := by dsimp only [a]; rw [inv_mul_cancel₀ hl.ne']
    have hax : exp a⁻¹ ≤ x := by dsimp only [a]; rw [inv_inv, exp_log (by linarith : 0 < x)]
    have hsubset : {n | n ∈ goodSet δ T ∧ T < moment 2 n / tau n} ⊆
        {n | R < frequencyIntegral n 0 a} ∪ {n | n ∈ goodSet δ T ∧ R < frequencyIntegral n a 1} := by
      intro n hn
      by_cases hi : R < frequencyIntegral n 0 a
      · exact Or.inl hi
      · right
        refine ⟨hn.1, ?_⟩
        by_contra hh
        have hm := normalized_moment_two_le_frequency_split n a
        have hsum : frequencyIntegral n 0 a + frequencyIntegral n a 1 ≤ 2 * R := by
          linarith [le_of_not_gt hi, le_of_not_gt hh]
        have hmul := mul_le_mul_of_nonneg_left hsum hA.le
        have he : A * (2 * R) = T := by dsimp only [R]; field_simp
        change moment 2 n / tau n ≤ A * (frequencyIntegral n 0 a + frequencyIntegral n a 1) at hm
        rw [he] at hmul
        linarith [hn.2]
    calc _ ≤ probability w x ({n | R < frequencyIntegral n 0 a} ∪
        {n | n ∈ goodSet δ T ∧ R < frequencyIntegral n a 1}) := probability_mono w x hsubset
      _ ≤ probability w x {n | R < frequencyIntegral n 0 a} +
        probability w x {n | n ∈ goodSet δ T ∧ R < frequencyIntegral n a 1} := probability_union_le w x _ _
      _ ≤ C₀ / R + C₁ * T / R ^ 2 :=
        add_le_add (hinitial x a R hx ha.le ha1 haL hR) (hhigh T x a R hT ha ha1 hax hR)
      _ = _ := by dsimp only [R]; field_simp; ring
  · have hlog1 : log x ≤ 1 := by
      have h := log_le_log (by linarith : 0 < x) (le_of_not_ge hlarge)
      simpa only [log_exp] using h
    have hsubset : {n | n ∈ goodSet δ T ∧ T < moment 2 n / tau n} ⊆
        {n | R < frequencyIntegral n 0 1} := by
      intro n hn
      by_contra hh
      have hm := normalized_moment_two_le_fourier_integral n
      have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt hh) hA.le
      have he : A * R = T / 2 := by dsimp only [R]; field_simp
      change moment 2 n / tau n ≤ A * frequencyIntegral n 0 1 at hm
      rw [he] at hmul
      linarith [hn.2]
    calc _ ≤ probability w x {n | R < frequencyIntegral n 0 1} := probability_mono w x hsubset
      _ ≤ C₀ / R := hinitial x 1 R hx (by norm_num) le_rfl (by simpa using hlog1) hR
      _ ≤ (2 * A * C₀ + 4 * A ^ 2 * C₁) / T := by
        have he : C₀ / R = 2 * A * C₀ / T := by dsimp only [R]; field_simp
        rw [he]
        apply div_le_div_of_nonneg_right _ hT0.le
        nlinarith [mul_nonneg (sq_nonneg A) hC₁.le]


theorem probability_goodSetStar_compl_le (w : MultiplicativeWeight) (hp : PrimeEstimates w) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ x T, 2 ≤ x → 1 < T →
      probability w x (goodSetStar δ T)ᶜ ≤ probability w x (goodSet δ T)ᶜ + C / T := by
  classical
  obtain ⟨C, hC, hbound⟩ := goodSet_second_moment_probability_bound w hp hδ
  refine ⟨C, hC, fun x T hx hT ↦ ?_⟩
  have hsubset : (goodSetStar δ T)ᶜ ⊆ (goodSet δ T)ᶜ ∪
      {n | n ∈ goodSet δ T ∧ T < moment 2 n / tau n} := by
    intro n hn
    by_cases hg : n ∈ goodSet δ T
    · right
      refine ⟨hg, ?_⟩
      by_contra hm
      exact hn ⟨hg, le_of_not_gt hm⟩
    · exact Or.inl hg
  exact (probability_mono w x hsubset).trans
    ((probability_union_le w x _ _).trans (add_le_add le_rfl (hbound x T hx hT)))


/-- The weighted upper exceptional-set bound, under explicit prime estimates. -/
theorem goodSetStar_exceptional_probability_bound (w : MultiplicativeWeight)
    (hp : PrimeEstimates w) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 1000000) :
    ∃ C > 0, ∀ x T, 2 ≤ x → 1 < T →
      probability w x (goodSetStar δ T)ᶜ ≤ C / T := by
  obtain ⟨C₀, hC₀, hgood⟩ := hp.goodSet_exceptional_bound hδ hδ1
  obtain ⟨C₁, hC₁, hmoment⟩ := probability_goodSetStar_compl_le w hp hδ
  refine ⟨C₀ + C₁, by positivity, fun x T hx hT ↦ ?_⟩
  calc
    _ ≤ probability w x (goodSet δ T)ᶜ + C₁ / T := hmoment x T hx hT
    _ ≤ C₀ / T + C₁ / T := add_le_add (hgood x T hT) le_rfl
    _ = _ := by ring

end BretecheTenenbaumMean.WeightedModel
