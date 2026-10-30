module

public import BretecheTenenbaumMean.Sieve.Interval

@[expose] public section

/-! # Short prime intervals with a square-root error -/

namespace BretecheTenenbaumMean.PrimeSums

open Finset Real

/-- A uniform prime-counting bound on every natural interval `(a,b]`.
Choosing the sieve cutoff `a^(1/16)` makes its error `sqrt a`. -/
theorem prime_count_Ioc_le : ∃ C > 0, ∀ a b : ℕ, 2 ≤ a → a ≤ b →
    (((Ioc a b).filter Nat.Prime).card : ℝ) ≤
      C * (((b : ℝ) - a) / log a + sqrt a) := by
  obtain ⟨K, hK, hsieve⟩ := Sieve.prime_interval_sieve_bound
  obtain ⟨c, _, hc, _, hnormal⟩ := normalizer_bounds
  refine ⟨64 / c + K + 256, by positivity, fun a b ha hab ↦ ?_⟩
  have ha2 : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := by linarith
  have hla : 0 < log a := log_pos (by linarith)
  have hD : 0 ≤ (b : ℝ) - a := sub_nonneg.2 (by exact_mod_cast hab)
  have hDdiv : 0 ≤ ((b : ℝ) - a) / log a := div_nonneg hD hla.le
  by_cases hlarge : 256 ≤ log a
  · let z := (a : ℝ) ^ (1 / 16 : ℝ)
    have hz0 : 0 < z := rpow_pos_of_pos ha0 _
    have hlogz : log z = log a / 16 := by dsimp only [z]; rw [log_rpow ha0]; ring
    have hzlog : 16 ≤ log z := by rw [hlogz]; linarith
    have hz : 2 ≤ z := by
      have he : 17 ≤ exp (log z) := (show (17 : ℝ) ≤ 1 + log z by linarith).trans
        (by simpa only [add_comm] using add_one_le_exp (log z))
      rw [exp_log hz0] at he
      linarith
    have hza : z ≤ a := rpow_le_self_of_one_le (by linarith) (by norm_num)
    have hz8 : z ^ 8 = sqrt a := by
      dsimp only [z]
      rw [← rpow_mul_natCast ha0.le, sqrt_eq_rpow]
      norm_num
    have hmain : 4 * ((b : ℝ) - a) / normalizer z ≤
        (64 / c) * (((b : ℝ) - a) / log a) := by
      calc
        _ ≤ 4 * ((b : ℝ) - a) / (c * log z) :=
          div_le_div_of_nonneg_left (by positivity) (mul_pos hc (by linarith)) (hnormal z hz).1
        _ = _ := by rw [hlogz]; field_simp; ring
    have h := hsieve a b z hab hz hzlog hza
    rw [hz8] at h
    have h64 : 0 ≤ 64 / c := by positivity
    have hK0 : 0 ≤ K := by linarith
    have hs : 0 ≤ sqrt a := sqrt_nonneg _
    nlinarith [h.trans (add_le_add hmain le_rfl), mul_nonneg h64 hs,
      mul_nonneg hK0 hDdiv]
  · have hcount : (((Ioc a b).filter Nat.Prime).card : ℝ) ≤ (b : ℝ) - a := by
      have h := card_filter_le (Ioc a b) Nat.Prime
      rw [Nat.card_Ioc] at h
      exact_mod_cast h
    have hsmall : (b : ℝ) - a ≤ 256 * (((b : ℝ) - a) / log a) := by
      have h := mul_le_mul_of_nonneg_right (le_of_not_ge hlarge) hDdiv
      have he : log a * (((b : ℝ) - a) / log a) = (b : ℝ) - a := by field_simp
      rw [he] at h
      exact h
    have h64 : 0 ≤ 64 / c := by positivity
    have hK0 : 0 ≤ K := by linarith
    have hs : 0 ≤ sqrt a := sqrt_nonneg _
    nlinarith [hcount.trans hsmall, mul_nonneg h64 hDdiv, mul_nonneg hK0 hDdiv,
      mul_nonneg (by positivity : 0 ≤ 64 / c + K + 256) hs]


/-- Real endpoints, including both endpoint primes. The harmless floor
errors are absorbed into the square-root term. -/
theorem prime_count_real_interval_le : ∃ C > 0, ∀ u v : ℝ, 2 ≤ u → u ≤ v →
    (((Icc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime).card : ℝ) ≤
      C * ((v - u) / log u + sqrt u) := by
  obtain ⟨C, hC, hcount⟩ := prime_count_Ioc_le
  refine ⟨5 * C + 1, by positivity, fun u v hu huv ↦ ?_⟩
  have hu0 : 0 < u := by linarith
  have hv0 : 0 ≤ v := by linarith
  have ha : 2 ≤ ⌊u⌋₊ := Nat.le_floor hu
  have hab : ⌊u⌋₊ ≤ ⌊v⌋₊ := Nat.floor_mono huv
  have ha2 : (2 : ℝ) ≤ ⌊u⌋₊ := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < ⌊u⌋₊ := by linarith
  have hal : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu0.le
  have hau : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
  have hbl : (⌊v⌋₊ : ℝ) ≤ v := Nat.floor_le hv0
  have hla : 0 < log (⌊u⌋₊ : ℝ) := log_pos (by linarith)
  have hlu : 0 < log u := log_pos (by linarith)
  have hlog : log u ≤ 2 * log (⌊u⌋₊ : ℝ) := by
    have h := log_le_log hu0 (show u ≤ (⌊u⌋₊ : ℝ) ^ 2 by nlinarith)
    simpa only [log_pow, Nat.cast_ofNat] using h
  have hhalf : (1 / 2 : ℝ) ≤ log u :=
    (show (1 / 2 : ℝ) ≤ log 2 by linarith [log_two_gt_d9]).trans (log_le_log (by norm_num) hu)
  have hs1 : 1 ≤ sqrt u := by
    simpa only [sqrt_one] using sqrt_le_sqrt (show (1 : ℝ) ≤ u by linarith)
  have hlength : ((⌊v⌋₊ : ℝ) - ⌊u⌋₊) / log (⌊u⌋₊ : ℝ) ≤
      2 * ((v - u) / log u) + 4 := by
    calc
      _ ≤ (v - u + 1) / log (⌊u⌋₊ : ℝ) :=
        div_le_div_of_nonneg_right (by linarith) hla.le
      _ ≤ (v - u + 1) / (log u / 2) :=
        div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
      _ = 2 * ((v - u) / log u) + 2 / log u := by ring
      _ ≤ _ := by
        have h : 2 / log u ≤ 4 := (div_le_iff₀ hlu).2 (by linarith)
        linarith
  have hIcc : (((Icc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime).card : ℝ) ≤
      (((Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime).card : ℝ) + 1 := by
    have hsub : (Icc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime ⊆
        insert ⌊u⌋₊ ((Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime) := by
      intro p hp
      simp only [mem_filter, mem_Icc] at hp
      simp only [mem_insert, mem_filter, mem_Ioc]
      by_cases he : p = ⌊u⌋₊
      · exact Or.inl he
      · exact Or.inr ⟨⟨by omega, hp.1.2⟩, hp.2⟩
    exact_mod_cast (card_le_card hsub).trans (card_insert_le _ _)
  have hroot : sqrt (⌊u⌋₊ : ℝ) ≤ sqrt u := sqrt_le_sqrt hal
  have hsum := add_le_add hlength hroot
  have hc := (hcount _ _ ha hab).trans (mul_le_mul_of_nonneg_left hsum hC.le)
  have hD : 0 ≤ (v - u) / log u := div_nonneg (sub_nonneg.2 huv) hlu.le
  nlinarith [hIcc.trans (add_le_add hc le_rfl), mul_nonneg hC.le hD,
    mul_le_mul_of_nonneg_left hs1 hC.le]


/-- The reciprocal-prime short-interval estimate used in averaging divisor
windows. The finite set may omit either endpoint or any other primes. -/
theorem prime_reciprocal_interval_bound : ∃ C > 0, ∀ u v : ℝ,
    2 ≤ u → u ≤ v → v ≤ 100 * u → ∀ s : Finset ℕ,
    (∀ p ∈ s, p.Prime ∧ u ≤ p ∧ (p : ℝ) ≤ v) →
    (∑ p ∈ s, (p : ℝ)⁻¹) ≤ C * (log (v / u) / log u + 1 / sqrt u) := by
  obtain ⟨C, hC, hcount⟩ := prime_count_real_interval_le
  refine ⟨100 * C, by positivity, fun u v hu huv hvu s hs ↦ ?_⟩
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := hu0.trans_le huv
  have hlu : 0 < log u := log_pos (by linarith)
  have hsqrt : 0 < sqrt u := sqrt_pos.2 hu0
  have hsub : s ⊆ (Icc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpp, hup, hpv⟩ := hs p hp
    exact mem_filter.2 ⟨mem_Icc.2 ⟨by
      have h := (Nat.floor_le hu0.le).trans hup
      exact_mod_cast h, Nat.le_floor hpv⟩, hpp⟩
  have hcard : (s.card : ℝ) ≤ C * ((v - u) / log u + sqrt u) :=
    (show (s.card : ℝ) ≤ (((Icc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime).card : ℝ) by
      exact_mod_cast card_le_card hsub).trans (hcount u v hu huv)
  have hsum : (∑ p ∈ s, (p : ℝ)⁻¹) ≤ (s.card : ℝ) / u := by
    calc
      _ ≤ ∑ _ ∈ s, u⁻¹ := sum_le_sum (fun p hp ↦ inv_anti₀ hu0 (hs p hp).2.1)
      _ = _ := by simp only [sum_const, nsmul_eq_mul, div_eq_mul_inv]
  have hlog0 : 0 ≤ log (v / u) := log_nonneg ((one_le_div hu0).2 huv)
  have hlog : (v - u) / u ≤ 100 * log (v / u) := by
    have h := one_sub_inv_le_log_of_pos (div_pos hv0 hu0)
    rw [inv_div] at h
    have he : (1 - u / v) * v = v - u := by field_simp
    have hmul := mul_le_mul_of_nonneg_right h hv0.le
    rw [he] at hmul
    have hlarge := mul_le_mul_of_nonneg_left hvu hlog0
    apply (div_le_iff₀ hu0).2
    nlinarith
  have hmain : ((v - u) / log u + sqrt u) / u ≤
      100 * (log (v / u) / log u + 1 / sqrt u) := by
    have hq := div_le_div_of_nonneg_right hlog hlu.le
    have he : sqrt u / u = 1 / sqrt u := by
      apply (div_eq_div_iff hu0.ne' hsqrt.ne').2
      simpa only [one_mul, ← pow_two] using sq_sqrt hu0.le
    calc
      _ = ((v - u) / u) / log u + 1 / sqrt u := by rw [add_div, he]; ring
      _ ≤ (100 * log (v / u)) / log u + 1 / sqrt u := add_le_add hq le_rfl
      _ ≤ _ := by
        rw [mul_div_assoc]
        have := one_div_pos.2 hsqrt
        nlinarith
  calc
    _ ≤ (s.card : ℝ) / u := hsum
    _ ≤ (C * ((v - u) / log u + sqrt u)) / u := div_le_div_of_nonneg_right hcard hu0.le
    _ = C * (((v - u) / log u + sqrt u) / u) := by ring
    _ ≤ C * (100 * (log (v / u) / log u + 1 / sqrt u)) := mul_le_mul_of_nonneg_left hmain hC.le
    _ = _ := by ring

end BretecheTenenbaumMean.PrimeSums
