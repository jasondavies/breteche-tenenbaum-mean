module

public import BretecheTenenbaumMean.HighFrequencyMean
public import BretecheTenenbaumMean.EventBounds
public import BretecheTenenbaumMean.IntermediateFrequency

@[expose] public section

/-! # The second-moment tail inside the good set -/

namespace BretecheTenenbaumMean

open Real MeasureTheory

/-- The initial frequency interval has a uniform first-moment tail. -/
theorem initial_frequency_probability_bound : ∃ C > 0, ∀ x b R,
    2 ≤ x → 0 ≤ b → b ≤ 1 → b * log x ≤ 1 → 0 < R →
    probability x {n | R < frequencyIntegral n 0 b} ≤ C / R := by
  obtain ⟨C, hC, hmean⟩ := initial_frequency_integral_le
  refine ⟨C, hC, fun x b R hx hb hb1 hbL hR ↦ ?_⟩
  have hE : expectation x (fun n ↦ frequencyIntegral n 0 b) ≤ C := by
    have he := expectation_indicator_frequencyIntegral x 0 b Set.univ
    simp only [Set.indicator_univ] at he
    rw [he]
    exact hmean x b hx hb hb1 hbL
  exact (probability_gt_le x (fun n _ ↦ frequencyIntegral_nonneg n hb) hR).trans
    (div_le_div_of_nonneg_right hE hR.le)

/-- The high-frequency second-moment tail, uniformly in every admissible cutoff. -/
theorem high_frequency_probability_bound {δ : ℝ} (hδ : 0 < δ) : ∃ C > 0, ∀ T x a R,
    1 < T → 0 < a → a ≤ 1 → exp a⁻¹ ≤ x → 0 < R →
    probability x {n | n ∈ goodSet δ T ∧ R < frequencyIntegral n a 1} ≤ C * T / R ^ 2 := by
  obtain ⟨C, hC, hmean⟩ := high_frequency_second_moment_bound hδ
  refine ⟨C, hC, fun T x a R hT ha ha1 hx hR ↦ ?_⟩
  exact (probability_inter_gt_sq_le x (goodSet δ T) (fun n ↦ frequencyIntegral n a 1) hR).trans
    (div_le_div_of_nonneg_right (hmean T x a hT ha ha1 hx) (sq_nonneg R))

/-- The Fourier majorant splits exactly at any intermediate cutoff. -/
theorem normalized_moment_two_le_frequency_split (n : ℕ) (a : ℝ) :
    moment 2 n / tau n ≤ (π ^ 2 / 2) * (frequencyIntegral n 0 a + frequencyIntegral n a 1) := by
  have he := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_normalizedPolynomial n 0 a) (intervalIntegrable_normalizedPolynomial n a 1)
  unfold frequencyIntegral
  rw [he]
  simpa only [normalizedPolynomial] using normalized_moment_two_le_fourier_integral n

/-- The analytic conclusion of §2.2 inside `E_T`. The separate estimate of
`P(E_Tᶜ)` is not assumed or hidden in this statement. -/
theorem goodSet_second_moment_probability_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ x T, 2 ≤ x → 1 < T →
      probability x {n | n ∈ goodSet δ T ∧ T < moment 2 n / tau n} ≤ C / T := by
  classical
  obtain ⟨C₀, hC₀, hinitial⟩ := initial_frequency_probability_bound
  obtain ⟨C₁, hC₁, hhigh⟩ := high_frequency_probability_bound hδ
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
    calc _ ≤ probability x ({n | R < frequencyIntegral n 0 a} ∪
        {n | n ∈ goodSet δ T ∧ R < frequencyIntegral n a 1}) := probability_mono x hsubset
      _ ≤ probability x {n | R < frequencyIntegral n 0 a} +
        probability x {n | n ∈ goodSet δ T ∧ R < frequencyIntegral n a 1} := probability_union_le x _ _
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
    calc _ ≤ probability x {n | R < frequencyIntegral n 0 1} := probability_mono x hsubset
      _ ≤ C₀ / R := hinitial x 1 R hx (by norm_num) le_rfl (by simpa using hlog1) hR
      _ ≤ (2 * A * C₀ + 4 * A ^ 2 * C₁) / T := by
        have he : C₀ / R = 2 * A * C₀ / T := by dsimp only [R]; field_simp
        rw [he]
        apply div_le_div_of_nonneg_right _ hT0.le
        nlinarith [mul_nonneg (sq_nonneg A) hC₁.le]

/-- The remaining contribution to Proposition 2.1 is exactly the complement
of the original good set. Its independent large-deviation estimate is proved in `GoodSetExceptional`. -/
theorem probability_goodSetStar_compl_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ x T, 2 ≤ x → 1 < T →
      probability x (goodSetStar δ T)ᶜ ≤ probability x (goodSet δ T)ᶜ + C / T := by
  classical
  obtain ⟨C, hC, hbound⟩ := goodSet_second_moment_probability_bound hδ
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
  exact (probability_mono x hsubset).trans
    ((probability_union_le x _ _).trans (add_le_add le_rfl (hbound x T hx hT)))

end BretecheTenenbaumMean
