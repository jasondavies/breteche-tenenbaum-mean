module

public import NairTenenbaum.PrimeLogSums
public import BretecheTenenbaumMean.PrimeSums.Strict

@[expose] public section

/-! # Reciprocal-logarithmic prime tails -/

namespace BretecheTenenbaumMean.PrimeSums

open Finset Real MeasureTheory intervalIntegral

noncomputable def primeLogReciprocal (n : ℕ) : ℝ := NairTenenbaum.primeLogWeight n / n

theorem primeLogReciprocal_nonneg (n : ℕ) : 0 ≤ primeLogReciprocal n := by
  unfold primeLogReciprocal NairTenenbaum.primeLogWeight
  split_ifs with h
  · exact div_nonneg (log_nonneg (by exact_mod_cast h.one_le)) (Nat.cast_nonneg n)
  · simp

theorem sum_primeLogReciprocal (t : ℝ) :
    (∑ n ∈ Icc 0 ⌊t⌋₊, primeLogReciprocal n) = NairTenenbaum.primeLogSum t := by
  simp only [NairTenenbaum.primeLogSum, sum_filter, primeLogReciprocal, NairTenenbaum.primeLogWeight]
  apply sum_congr rfl
  intro n _
  split_ifs <;> simp

theorem primeLogSum_nonneg (t : ℝ) : 0 ≤ NairTenenbaum.primeLogSum t := by
  rw [← sum_primeLogReciprocal]
  exact sum_nonneg (fun n _ ↦ primeLogReciprocal_nonneg n)

theorem primeLogSum_mono : Monotone NairTenenbaum.primeLogSum := by
  intro a b hab
  rw [← sum_primeLogReciprocal, ← sum_primeLogReciprocal]
  exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl (Nat.floor_mono hab))
    (fun n _ _ ↦ primeLogReciprocal_nonneg n)

theorem primeLogSum_le_mul_log : ∃ B > 0, ∀ t : ℝ, 2 ≤ t → NairTenenbaum.primeLogSum t ≤ B * log t := by
  let B := log 4 * (1 + (log 2)⁻¹)
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  have hl4 : 0 < log 4 := log_pos (by norm_num)
  refine ⟨B, by dsimp only [B]; positivity, fun t ht ↦ ?_⟩
  have hlt := log_le_log (by norm_num : (0 : ℝ) < 2) ht
  have h : 1 ≤ log t * (log 2)⁻¹ := (le_div_iff₀ hl2).2 (by simpa using hlt)
  have hmul := mul_le_mul_of_nonneg_left h hl4.le
  have hbound := NairTenenbaum.primeLogSum_le ht
  dsimp only [B]
  nlinarith

/-- A finite tail with a strict lower endpoint. -/
theorem prime_inv_log_Ioc_bound : ∃ C > 0, ∀ a b : ℝ, 2 ≤ a → a ≤ b →
    (∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if p.Prime then 1 / ((p : ℝ) * log p) else 0) ≤ C / log a := by
  obtain ⟨B, hB, hbound⟩ := primeLogSum_le_mul_log
  refine ⟨2 * B, by positivity, fun a b ha hab ↦ ?_⟩
  have hpos : ∀ t ∈ Set.Icc a b, 1 < t := fun t ht ↦ by linarith [ht.1]
  have hder : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun t : ℝ ↦ (log t ^ 2)⁻¹) (-(2 / (t * log t ^ 3))) t := by
    intro t ht
    have ht0 : 0 < t := by linarith [hpos t ht]
    have hlog : 0 < log t := log_pos (hpos t ht)
    convert (((hasDerivAt_log ht0.ne').pow 2).inv (pow_ne_zero 2 hlog.ne')) using 1
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply]
    field_simp
  have hc : ContinuousOn (fun t : ℝ ↦ -(2 / (t * log t ^ 3))) (Set.Icc a b) := by
    intro t ht
    have ht0 : 0 < t := by linarith [hpos t ht]
    have hlog : 0 < log t := log_pos (hpos t ht)
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have hi : IntegrableOn (deriv (fun t : ℝ ↦ (log t ^ 2)⁻¹)) (Set.Icc a b) :=
    hc.integrableOn_Icc.congr_fun (fun t ht ↦ (hder t ht).deriv.symm) measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul primeLogReciprocal
    (f := fun t : ℝ ↦ (log t ^ 2)⁻¹) (by linarith) hab
    (fun t ht ↦ (hder t ht).differentiableAt) hi
  simp only [sum_primeLogReciprocal] at habel
  rw [setIntegral_congr_fun measurableSet_Ioc
    (g := fun t : ℝ ↦ -(2 / (t * log t ^ 3)) * NairTenenbaum.primeLogSum t)
    (fun t ht ↦ by rw [(hder t (Set.Ioc_subset_Icc_self ht)).deriv]),
    ← intervalIntegral.integral_of_le hab] at habel
  have hsum : (∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (log (p : ℝ) ^ 2)⁻¹ * primeLogReciprocal p) =
      ∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if p.Prime then 1 / ((p : ℝ) * log p) else 0 := by
    apply sum_congr rfl
    intro p _
    unfold primeLogReciprocal NairTenenbaum.primeLogWeight
    split_ifs with hp
    · have hl : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
      field_simp
    · simp
  rw [hsum] at habel
  have hneg : (∫ t in a..b, -(2 / (t * log t ^ 3)) * NairTenenbaum.primeLogSum t) =
      -(∫ t in a..b, (2 / (t * log t ^ 3)) * NairTenenbaum.primeLogSum t) := by
    rw [← intervalIntegral.integral_neg]
    apply integral_congr
    intro t _
    ring
  rw [hneg, sub_neg_eq_add] at habel
  have hc' : ContinuousOn (fun t : ℝ ↦ 2 / (t * log t ^ 3)) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    have h := hc.neg
    change ContinuousOn (fun t : ℝ ↦ -(-(2 / (t * log t ^ 3)))) _ at h
    simpa only [neg_neg] using h
  have hiU : IntervalIntegrable (fun t : ℝ ↦ (2 / (t * log t ^ 3)) * NairTenenbaum.primeLogSum t) volume a b :=
    primeLogSum_mono.intervalIntegrable.continuousOn_mul hc'
  have hcM : ContinuousOn (fun t : ℝ ↦ t⁻¹ / log t ^ 2) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    have ht0 : 0 < t := by linarith [hpos t ht]
    have hlog : 0 < log t := log_pos (hpos t ht)
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have hint : (∫ t in a..b, (2 / (t * log t ^ 3)) * NairTenenbaum.primeLogSum t) ≤
      2 * B * ((log a)⁻¹ - (log b)⁻¹) := by
    rw [← integral_inv_div_log_sq (by linarith : 1 < a) (by linarith : 1 < b), ← intervalIntegral.integral_const_mul]
    apply integral_mono_on hab hiU (hcM.intervalIntegrable.const_mul _)
    intro t ht
    have ht0 : 0 < t := by linarith [hpos t ht]
    have hlog : 0 < log t := log_pos (hpos t ht)
    calc
      _ ≤ (2 / (t * log t ^ 3)) * (B * log t) :=
        mul_le_mul_of_nonneg_left (hbound t (by linarith [ht.1])) (by positivity)
      _ = _ := by field_simp
  have hloga : 0 < log a := log_pos (by linarith)
  have hlogb : 0 < log b := log_pos (by linarith)
  have hupper : (log b ^ 2)⁻¹ * NairTenenbaum.primeLogSum b ≤ B / log b := by
    have h := mul_le_mul_of_nonneg_left (hbound b (by linarith)) (by positivity : 0 ≤ (log b ^ 2)⁻¹)
    convert h using 1
    field_simp
  have hlower : 0 ≤ (log a ^ 2)⁻¹ * NairTenenbaum.primeLogSum a :=
    mul_nonneg (by positivity) (primeLogSum_nonneg a)
  have hlast : 0 ≤ B / log b := by positivity
  rw [habel]
  simp only [div_eq_mul_inv] at hupper hlast
  change _ ≤ 2 * B * (log a)⁻¹
  linarith

/-- Uniform reciprocal-logarithmic tail for an arbitrary finite prime set,
including primes exactly equal to the lower endpoint. -/
theorem prime_inv_log_tail_bound : ∃ C > 0, ∀ z : ℝ, 2 ≤ z →
    ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ z ≤ (p : ℝ)) →
    (∑ p ∈ s, 1 / ((p : ℝ) * log p)) ≤ C / log z := by
  classical
  obtain ⟨C, hC, htail⟩ := prime_inv_log_Ioc_bound
  refine ⟨C + 1, by linarith, fun z hz s hs ↦ ?_⟩
  let b : ℝ := max z ((s.sup (fun p : ℕ ↦ p) : ℕ) : ℝ)
  let e := s.filter (fun p : ℕ ↦ (p : ℝ) ≤ z)
  let r := s.filter (fun p : ℕ ↦ ¬ (p : ℝ) ≤ z)
  have hz0 : 0 < z := by linarith
  have hlog : 0 < log z := log_pos (by linarith)
  have heq : ∀ p ∈ e, (p : ℝ) = z := by
    intro p hp
    obtain ⟨hp, hle⟩ := mem_filter.1 hp
    exact le_antisymm hle (hs p hp).2
  have hcard : e.card ≤ 1 := card_le_one.2 (fun p hp q hq ↦ by
    exact_mod_cast (heq p hp).trans (heq q hq).symm)
  have he : (∑ p ∈ e, 1 / ((p : ℝ) * log p)) ≤ 1 / log z := by
    calc
      _ = e.card * (1 / (z * log z)) := by
        rw [← nsmul_eq_mul, ← sum_const]
        exact sum_congr rfl (fun p hp ↦ by rw [heq p hp])
      _ ≤ 1 * (1 / (z * log z)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard
      _ ≤ 1 / log z := by
        rw [one_mul]
        exact one_div_le_one_div_of_le hlog (by nlinarith)
  have hrsub : r ⊆ Ioc ⌊z⌋₊ ⌊b⌋₊ := by
    intro p hp
    obtain ⟨hps, hpz⟩ := mem_filter.1 hp
    apply mem_Ioc.2
    constructor
    · exact (Nat.floor_lt hz0.le).2 (lt_of_not_ge hpz)
    · apply (Nat.le_floor_iff (hz0.le.trans (le_max_left _ _))).2
      have hle : (p : ℝ) ≤ ((s.sup (fun p : ℕ ↦ p) : ℕ) : ℝ) := by
        exact_mod_cast (le_sup (f := id) hps)
      exact hle.trans (le_max_right _ _)
  have hr : (∑ p ∈ r, 1 / ((p : ℝ) * log p)) ≤ C / log z := by
    calc
      _ = ∑ p ∈ r, if p.Prime then 1 / ((p : ℝ) * log p) else 0 := by
        apply sum_congr rfl
        intro p hp
        rw [ite_eq_left (hs p (mem_filter.1 hp).1).1]
      _ ≤ ∑ p ∈ Ioc ⌊z⌋₊ ⌊b⌋₊, if p.Prime then 1 / ((p : ℝ) * log p) else 0 := by
        apply sum_le_sum_of_subset_of_nonneg hrsub
        intro p _ _
        split_ifs with hp
        · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
          have hpl : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
          positivity
        · exact le_rfl
      _ ≤ _ := htail z b hz (le_max_left _ _)
  have hsplit := sum_filter_add_sum_filter_not s (fun p : ℕ ↦ (p : ℝ) ≤ z)
    (fun p : ℕ ↦ 1 / ((p : ℝ) * log p))
  change (∑ p ∈ e, _) + (∑ p ∈ r, _) = _ at hsplit
  rw [← hsplit, add_div]
  linarith

/-- The form of the prime tail used after smoothing the moment recursion. -/
theorem prime_inv_log_sqrt_tail_bound : ∃ C > 0, ∀ y : ℝ, 1 ≤ y →
    ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ sqrt y ≤ (p : ℝ)) →
    (∑ p ∈ s, 1 / ((p : ℝ) * log p)) ≤ C / log (3 * y) := by
  obtain ⟨C, hC, htail⟩ := prime_inv_log_tail_bound
  refine ⟨4 * C, by positivity, fun y hy s hs ↦ ?_⟩
  let z := max 2 (sqrt y)
  have hz : 2 ≤ z := le_max_left _ _
  have hz0 : 0 < z := by linarith
  have hy0 : 0 < y := by linarith
  have hlz : 0 < log z := log_pos (by linarith)
  have hly : 0 < log (3 * y) := log_pos (by linarith)
  have hlog : log (3 * y) ≤ 4 * log z := by
    have hyz : y ≤ z ^ 2 := (sqrt_le_left hz0.le).1 (le_max_right _ _)
    have h1 := log_le_log hy0 hyz
    rw [log_pow] at h1
    have h2 := log_le_log (by norm_num : (0 : ℝ) < 3)
      (show (3 : ℝ) ≤ z ^ 2 by nlinarith)
    rw [log_pow] at h2
    rw [log_mul (by norm_num) hy0.ne']
    norm_num only [Nat.cast_ofNat] at h1 h2
    linarith
  calc
    _ ≤ C / log z := htail z hz s (fun p hp ↦ ⟨(hs p hp).1,
      max_le (by exact_mod_cast (hs p hp).1.two_le) (hs p hp).2⟩)
    _ ≤ 4 * C / log (3 * y) := by
      apply (div_le_div_iff₀ hlz hly).2
      nlinarith

end BretecheTenenbaumMean.PrimeSums
