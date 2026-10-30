module

public import BretecheTenenbaumMean.DyadicLowerTail
public import BretecheTenenbaumMean.Targets

@[expose] public section

/-! # Proposition 2.1: the lower second-moment tail, with an admissible range -/

namespace BretecheTenenbaumMean

open Real

/-- Rounding the offset upward gives a strict tail threshold and costs only
an absolute factor after any prescribed initial offset. -/
theorem exists_dyadic_offset (t₀ : ℕ) {K T : ℝ} (hK : 1 ≤ K) (hT : 3 ≤ T) :
    ∃ t : ℕ, t₀ ≤ t ∧ T < (2 : ℝ) ^ t / (K + 1) ∧
      (2 : ℝ) ^ t ≤ ((2 : ℝ) ^ t₀ * 4 * (K + 1)) * T := by
  let R := (K + 1) * T
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : 1 ≤ R := by dsimp [R]; nlinarith
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  let a := log R / log 2
  have ha : 0 ≤ a := div_nonneg (log_nonneg hR1) hl2.le
  let N := ⌈a⌉₊
  have hNa : a ≤ (N : ℝ) := Nat.le_ceil _
  have hNa' : (N : ℝ) ≤ a + 1 := (Nat.ceil_lt_add_one ha).le
  have hid : a * log 2 = log R := by dsimp [a]; field_simp
  have hlow : R ≤ (2 : ℝ) ^ N := by
    calc
      _ = exp (log R) := (exp_log hR).symm
      _ ≤ exp ((N : ℝ) * log 2) := exp_le_exp.2 (by nlinarith)
      _ = _ := by rw [exp_nat_mul, exp_log (by norm_num : (0 : ℝ) < 2)]
  have hhigh : (2 : ℝ) ^ N ≤ 2 * R := by
    calc
      _ = exp ((N : ℝ) * log 2) := by
        rw [exp_nat_mul, exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ exp (log R + log 2) := exp_le_exp.2 (by nlinarith)
      _ = _ := by rw [exp_add, exp_log hR, exp_log (by norm_num : (0 : ℝ) < 2)]; ring
  refine ⟨t₀ + N + 1, by omega, ?_, ?_⟩
  · apply (lt_div_iff₀ (show 0 < K + 1 by linarith)).2
    have hpow : (1 : ℝ) ≤ 2 ^ t₀ := one_le_pow₀ (by norm_num)
    have he : 2 * R ≤ (2 : ℝ) ^ (t₀ + N + 1) := by
      rw [pow_succ, pow_add]
      have hh := mul_le_mul_of_nonneg_right hpow (show 0 ≤ (2 : ℝ) ^ N by positivity)
      nlinarith
    change T * (K + 1) < _
    dsimp only [R] at he hR
    nlinarith
  · rw [pow_succ, pow_add]
    have hh := mul_le_mul_of_nonneg_left hhigh (show 0 ≤ (2 : ℝ) ^ t₀ by positivity)
    dsimp only [R] at hh
    nlinarith

/-- A quantified valid range for the lower side of (2.5). The cutoff
`x ≥ exp((B*T)^4)` suffices, with absolute constants `c,B>0`. -/
theorem propositionTwoOneLower_quantitative : ∃ c > 0, ∃ B > 0,
    ∀ T : ℝ, 3 ≤ T → ∀ x : ℝ, exp ((B * T) ^ 4) ≤ x →
      c / T ≤ probability x {n | T < moment 2 n / tau n} := by
  obtain ⟨c, hc, K, hK, t₀, htail⟩ := dyadic_second_moment_lower_tail
  let B := (2 : ℝ) ^ t₀ * 4 * (K + 1)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨c / B, by positivity, B, hB, fun T hT x hx ↦ ?_⟩
  obtain ⟨t, ht, hthreshold, hupper⟩ := exists_dyadic_offset t₀ hK hT
  have hcut : exp ((2 : ℝ) ^ (4 * t)) ≤ x := by
    apply le_trans _ hx
    apply exp_le_exp.2
    rw [Nat.mul_comm 4 t, pow_mul]
    exact pow_le_pow_left₀ (by positivity) hupper 4
  calc
    _ = c / (B * T) := div_div c B T
    _ ≤ c / (2 : ℝ) ^ t := div_le_div_of_nonneg_left hc.le (by positivity) hupper
    _ ≤ probability x {n | (2 : ℝ) ^ t / (K + 1) ≤ moment 2 n / tau n} := htail t ht x hcut
    _ ≤ _ := probability_mono x (fun _ hn ↦ hthreshold.trans_le hn)

/-- The lower-tail target, with the ambient cutoff allowed to depend on `T`. -/
theorem propositionTwoOneLower : PropositionTwoOneLower := by
  obtain ⟨c, hc, B, hB, htail⟩ := propositionTwoOneLower_quantitative
  refine ⟨c, hc, fun T hT ↦ ⟨max 2 (exp ((B * T) ^ 4)), le_max_left _ _, fun x hx ↦ ?_⟩⟩
  exact htail T hT x ((le_max_right _ _).trans hx)

end BretecheTenenbaumMean
