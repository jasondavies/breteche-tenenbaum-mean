module

public import BretecheTenenbaumMean.TupleWindows
public import BretecheTenenbaumMean.PrimeSums.ShortIntervals
public import BretecheTenenbaumMean.Reflection

@[expose] public section

/-! # Averaging divisor-window powers over primes -/

namespace BretecheTenenbaumMean

open Finset Real MeasureTheory

/-- A short interval in `log p`, restricted to primes above a cutoff.
Its endpoints can lie below the cutoff. -/
theorem prime_reciprocal_log_interval_bound : ∃ C > 0, ∀ z a b : ℝ,
    2 ≤ z → a ≤ b → b ≤ a + 1 → ∀ s : Finset ℕ,
    (∀ p ∈ s, p.Prime ∧ z ≤ p ∧ a < log p ∧ log p ≤ b) →
    (∑ p ∈ s, (p : ℝ)⁻¹) ≤ C * ((b - a) / log z + 1 / sqrt z) := by
  obtain ⟨C, hC, hbound⟩ := PrimeSums.prime_reciprocal_interval_bound
  refine ⟨C, hC, fun z a b hz hab hba s hs ↦ ?_⟩
  have hz0 : 0 < z := by linarith
  have hlz : 0 < log z := log_pos (by linarith)
  by_cases hne : s.Nonempty
  · let u := max z (exp a)
    let v := exp b
    have hu : 2 ≤ u := hz.trans (le_max_left _ _)
    have hu0 : 0 < u := by linarith
    have hlu : 0 < log u := log_pos (by linarith)
    have hpinterval : ∀ p ∈ s, p.Prime ∧ u ≤ p ∧ (p : ℝ) ≤ v := by
      intro p hp
      obtain ⟨hpp, hzp, hap, hpb⟩ := hs p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      refine ⟨hpp, max_le hzp ?_, ?_⟩
      · exact ((exp_lt_exp.2 hap).trans_eq (exp_log hp0)).le
      · calc (p : ℝ) = exp (log p) := (exp_log hp0).symm
             _ ≤ exp b := exp_le_exp.2 hpb
    obtain ⟨p, hp⟩ := hne
    have huv : u ≤ v := (hpinterval p hp).2.1.trans (hpinterval p hp).2.2
    have hcomp : v ≤ 100 * u := by
      calc v ≤ exp (a + 1) := exp_le_exp.2 hba
           _ = exp 1 * exp a := by rw [exp_add]; ring
           _ ≤ 100 * u := mul_le_mul
             (by linarith [exp_one_lt_d9] : exp 1 ≤ 100) (le_max_right z (exp a))
             (exp_pos _).le (by norm_num)
    have hlogu : log z ≤ log u := log_le_log hz0 (le_max_left _ _)
    have ha : a ≤ log u := by
      have h := log_le_log (exp_pos a) (le_max_right z (exp a))
      simpa only [log_exp] using h
    have hratio : log (v / u) ≤ b - a := by rw [log_div (exp_ne_zero b) hu0.ne', log_exp]; linarith
    have hterm : log (v / u) / log u ≤ (b - a) / log z :=
      div_le_div₀ (sub_nonneg.2 hab) hratio hlz hlogu
    have hroot : 1 / sqrt u ≤ 1 / sqrt z :=
      one_div_le_one_div_of_le (sqrt_pos.2 hz0) (sqrt_le_sqrt (le_max_left _ _))
    exact (hbound u v hu huv hcomp s hpinterval).trans
      (mul_le_mul_of_nonneg_left (add_le_add hterm hroot) hC.le)
  · rw [not_nonempty_iff_eq_empty.1 hne, sum_empty]
    exact mul_nonneg hC.le (add_nonneg (div_nonneg (sub_nonneg.2 hab) hlz.le) (by positivity))

/-- A single tuple's overlap interval has the expected prime average, with
one square-root error for every coherent tuple. -/
theorem tuple_window_prime_bound : ∃ C > 0, ∀ {ι : Type} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (z u : ℝ), 2 ≤ z → ∀ s : Finset ℕ,
    (∀ p ∈ s, p.Prime ∧ z ≤ p) →
    (∑ p ∈ s, (Set.Ico (tupleMax a - 1) (tupleMin a)).indicator
      (fun _ : ℝ ↦ (1 : ℝ)) (u - log p) / p) ≤
      C * (max (1 + tupleMin a - tupleMax a) 0 / log z +
        (if tupleMax a < tupleMin a + 1 then (1 : ℝ) else 0) / sqrt z) := by
  classical
  obtain ⟨C, hC, hbound⟩ := prime_reciprocal_log_interval_bound
  refine ⟨C, hC, fun a z u hz s hs ↦ ?_⟩
  by_cases hcoh : tupleMax a < tupleMin a + 1
  · let t := s.filter (fun p : ℕ ↦ u - log p ∈ Set.Ico (tupleMax a - 1) (tupleMin a))
    have he : (∑ p ∈ s, (Set.Ico (tupleMax a - 1) (tupleMin a)).indicator
        (fun _ : ℝ ↦ (1 : ℝ)) (u - log p) / p) = ∑ p ∈ t, (p : ℝ)⁻¹ := by
      dsimp only [t]
      rw [sum_filter]
      apply sum_congr rfl
      intro p _
      simp only [Set.indicator_apply]
      split_ifs <;> simp only [one_div, zero_div]
    rw [he, ite_eq_left hcoh, max_eq_left (by linarith : 0 ≤ 1 + tupleMin a - tupleMax a)]
    have h := hbound z (u - tupleMin a) (u - tupleMax a + 1) hz (by linarith)
      (by linarith [tupleMin_le_tupleMax a]) t (by
        intro p hp
        obtain ⟨hps, hlo, hhi⟩ := mem_filter.1 hp
        exact ⟨(hs p hps).1, (hs p hps).2, by linarith, by linarith⟩)
    convert h using 1
    ring
  · have hempty : Set.Ico (tupleMax a - 1) (tupleMin a) = ∅ := Set.Ico_eq_empty (by linarith)
    rw [hempty]
    simp only [Set.indicator_empty, zero_div, sum_const_zero,
      ite_eq_right hcoh, max_eq_right (by linarith : 1 + tupleMin a - tupleMax a ≤ 0), zero_add, mul_zero, le_refl]


/-- Averaging a positive power of a translated divisor window over primes.
The constant is independent of `n,j,u,z` and the finite prime set. -/
theorem delta_pow_prime_average_bound : ∃ C > 0, ∀ n j : ℕ, ∀ (_ : NeZero j) (z u : ℝ),
    2 ≤ z → ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ z ≤ p) →
    (∑ p ∈ s, delta n (u - log p) ^ j / p) ≤
      C * (1 / log z + 2 ^ j / sqrt z) * moment j n := by
  classical
  obtain ⟨C, hC, htuple⟩ := tuple_window_prime_bound
  refine ⟨C, hC, fun n j hj z u hz s hs ↦ ?_⟩
  let : NeZero j := hj
  have hlog : 0 < log z := log_pos (by linarith)
  have hroot : 0 < sqrt z := sqrt_pos.2 (by linarith)
  calc
    _ = ∑ d ∈ divisorTuples n j, ∑ p ∈ s,
        (Set.Ico (tupleMax (fun i ↦ log (d i)) - 1) (tupleMin (fun i ↦ log (d i)))).indicator
          (fun _ : ℝ ↦ (1 : ℝ)) (u - log p) / p := by
      simp_rw [← wideDelta_one, wideDelta_pow_eq_tuple_sum, sum_div]
      exact sum_comm
    _ ≤ ∑ d ∈ divisorTuples n j, C *
        (max (1 + tupleMin (fun i ↦ log (d i)) - tupleMax (fun i ↦ log (d i))) 0 / log z +
          (if tupleMax (fun i ↦ log (d i)) < tupleMin (fun i ↦ log (d i)) + 1 then (1 : ℝ) else 0) / sqrt z) :=
      sum_le_sum (fun d _ ↦ htuple _ z u hz s hs)
    _ = C * (moment j n / log z +
        (∑ d ∈ divisorTuples n j,
          if tupleMax (fun i ↦ log (d i)) < tupleMin (fun i ↦ log (d i)) + 1 then (1 : ℝ) else 0) / sqrt z) := by
      rw [← mul_sum, sum_add_distrib, ← sum_div, ← sum_div, ← moment_eq_tuple_sum]
    _ ≤ C * (moment j n / log z + (2 ^ j * moment j n) / sqrt z) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (div_le_div_of_nonneg_right (coherent_tuple_count_le n j) hroot.le)) hC.le
    _ = _ := by ring

/-- The prime average of the mixed moments used in §2.3. Reflection puts
the smaller exponent on the shifted window, retaining the factor `2^j`. -/
theorem mixedMoment_prime_average_bound : ∃ C > 0, ∀ n q j : ℕ,
    1 ≤ j → j < q → ∀ z : ℝ, 2 ≤ z → ∀ s : Finset ℕ,
    (∀ p ∈ s, p.Prime ∧ z ≤ p) →
    (∑ p ∈ s, mixedMoment j q n p / p) ≤
      C * (1 / log z + 2 ^ j / sqrt z) * moment j n * moment (q - j) n := by
  obtain ⟨C, hC, havg⟩ := delta_pow_prime_average_bound
  refine ⟨C, hC, fun n q j hj hjq z hz s hs ↦ ?_⟩
  let : NeZero j := ⟨by omega⟩
  have hq : 1 ≤ q := by omega
  have hsub : q - (q - j) = j := by omega
  have hf (p : ℕ) : Integrable (fun u : ℝ ↦ delta n u ^ (q - j) * delta n (u - log p) ^ j / p) := by
    have h := (integrable_mixedMoment (q - j) q n p hq).div_const (p : ℝ)
    simpa only [hsub] using h
  have he : (∑ p ∈ s, mixedMoment j q n p / p) =
      ∫ u : ℝ, ∑ p ∈ s, delta n u ^ (q - j) * delta n (u - log p) ^ j / p := by
    rw [integral_finsetSum _ (fun p _ ↦ hf p)]
    apply sum_congr rfl
    intro p _
    rw [mixedMoment_symm n p q j (by omega), mixedMoment, hsub, integral_div]
  have hi := integrable_delta_pow n (q - j) (by omega)
  calc
    _ = ∫ u : ℝ, ∑ p ∈ s, delta n u ^ (q - j) * delta n (u - log p) ^ j / p := he
    _ ≤ ∫ u : ℝ, delta n u ^ (q - j) *
        (C * (1 / log z + 2 ^ j / sqrt z) * moment j n) := by
      apply integral_mono (integrable_finsetSum _ (fun p _ ↦ hf p)) (hi.mul_const _)
      intro u
      have h := mul_le_mul_of_nonneg_left (havg n j inferInstance z u hz s hs)
        (pow_nonneg (delta_nonneg n u) (q - j))
      simpa only [mul_sum, mul_div_assoc] using h
    _ = _ := by
      rw [integral_mul_const]
      change moment (q - j) n * (C * (1 / log z + 2 ^ j / sqrt z) * moment j n) = _
      ring


/-- A uniform elementary bound, useful when the prime cutoff is small. -/
theorem mixedMoment_le_moment_product (n p q j : ℕ) (hj : 1 ≤ j) (hjq : j < q) :
    mixedMoment j q n p ≤ 2 ^ j * moment j n * moment (q - j) n := by
  have hi := (integrable_delta_pow n (q - j) (by omega)).comp_sub_right (log (p : ℝ))
  calc
    _ ≤ ∫ u : ℝ, (2 ^ j * moment j n) * delta n (u - log p) ^ (q - j) := by
      apply integral_mono (integrable_mixedMoment j q n p (by omega)) (hi.const_mul _)
      intro u
      exact mul_le_mul_of_nonneg_right (delta_pow_le_moment n j hj u)
        (pow_nonneg (delta_nonneg n _) _)
    _ = _ := by
      rw [integral_const_mul, integral_sub_right_eq_self (fun u : ℝ ↦ delta n u ^ (q - j)) (log (p : ℝ))]
      rfl

/-- The prime-averaging input to §2.3, with the paper's logarithmic offset
and fourth-root error. Endpoints and bounded cutoffs are included. -/
theorem mixedMoment_prime_band_bound : ∃ C > 0, ∀ n q j : ℕ,
    1 ≤ j → j < q → ∀ y : ℝ, 1 ≤ y → ∀ s : Finset ℕ,
    (∀ p ∈ s, p.Prime ∧ sqrt y ≤ p ∧ (p : ℝ) ≤ y) →
    (∑ p ∈ s, mixedMoment j q n p / p) ≤
      C * (1 / log (3 * y) + 2 ^ j / y ^ (1 / 4 : ℝ)) * moment j n * moment (q - j) n := by
  obtain ⟨C, hC, hbound⟩ := mixedMoment_prime_average_bound
  refine ⟨4 * C + 6, by positivity, fun n q j hj hjq y hy s hs ↦ ?_⟩
  have hy0 : 0 < y := by linarith
  have hL : 0 < log (3 * y) := log_pos (by linarith)
  have hroot : 0 < y ^ (1 / 4 : ℝ) := rpow_pos_of_pos hy0 _
  have hMj := moment_nonneg j n
  have hMk := moment_nonneg (q - j) n
  have hm : 0 ≤ moment j n * moment (q - j) n := mul_nonneg (moment_nonneg _ _) (moment_nonneg _ _)
  have he : sqrt (sqrt y) = y ^ (1 / 4 : ℝ) := by
    rw [sqrt_eq_rpow, sqrt_eq_rpow, ← rpow_mul hy0.le]
    norm_num
  by_cases hlarge : 4 ≤ y
  · have hz : 2 ≤ sqrt y := by
      have h := sqrt_le_sqrt hlarge
      norm_num at h ⊢
      exact h
    have hlog : 0 < log y := log_pos (by linarith)
    have hLcomp : log (3 * y) ≤ 2 * log y := by
      rw [log_mul (by norm_num : (3 : ℝ) ≠ 0) hy0.ne']
      have h := log_le_log (by norm_num : (0 : ℝ) < 3) (show 3 ≤ y by linarith)
      linarith
    have hcoef : 1 / log (sqrt y) + 2 ^ j / sqrt (sqrt y) ≤
        4 * (1 / log (3 * y) + 2 ^ j / y ^ (1 / 4 : ℝ)) := by
      rw [he, log_sqrt hy0.le]
      have hfirst : 1 / (log y / 2) ≤ 4 / log (3 * y) := by
        apply (div_le_div_iff₀ (by positivity : 0 < log y / 2) hL).2
        linarith
      have herr : 0 ≤ (2 : ℝ) ^ j / y ^ (1 / 4 : ℝ) := by positivity
      have he4 : 4 / log (3 * y) = 4 * (1 / log (3 * y)) := by ring
      rw [he4] at hfirst
      nlinarith
    have hmain := hbound n q j hj hjq (sqrt y) hz s (fun p hp ↦ ⟨(hs p hp).1, (hs p hp).2.1⟩)
    have hcoef' := mul_le_mul_of_nonneg_left hcoef hC.le
    have hprod := mul_le_mul_of_nonneg_right hcoef' hm
    have hrest : 0 ≤ (1 / log (3 * y) + (2 : ℝ) ^ j / y ^ (1 / 4 : ℝ)) *
        (moment j n * moment (q - j) n) := by positivity
    nlinarith [hmain, hprod]
  · have hsub : s ⊆ Icc 2 4 := by
      intro p hp
      obtain ⟨hpp, _, hpy⟩ := hs p hp
      exact mem_Icc.2 ⟨hpp.two_le, by exact_mod_cast (hpy.trans (le_of_not_ge hlarge))⟩
    have hcard : (s.card : ℝ) ≤ 3 := by
      have h := card_le_card hsub
      norm_num at h
      exact_mod_cast h
    have hsum : (∑ p ∈ s, (p : ℝ)⁻¹) ≤ 3 := by
      calc
        _ ≤ ∑ _ ∈ s, (1 : ℝ) := sum_le_sum (fun p hp ↦ by
          have hp1 : (1 : ℝ) < p := by exact_mod_cast (hs p hp).1.one_lt
          exact (inv_lt_one_of_one_lt₀ hp1).le)
        _ = (s.card : ℝ) := by simp
        _ ≤ _ := hcard
    have hrough : (∑ p ∈ s, mixedMoment j q n p / p) ≤
        3 * (2 ^ j * moment j n * moment (q - j) n) := by
      calc
        _ ≤ ∑ p ∈ s, (2 ^ j * moment j n * moment (q - j) n) / p :=
          sum_le_sum (fun p _ ↦ div_le_div_of_nonneg_right
            (mixedMoment_le_moment_product n p q j hj hjq) (Nat.cast_nonneg p))
        _ = (2 ^ j * moment j n * moment (q - j) n) * ∑ p ∈ s, (p : ℝ)⁻¹ := by
          rw [mul_sum]
          apply sum_congr rfl
          intro p _
          rw [div_eq_mul_inv]
        _ ≤ (2 ^ j * moment j n * moment (q - j) n) * 3 :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = _ := by ring
    have hsmall : y ^ (1 / 4 : ℝ) ≤ 2 := by
      rw [← he]
      apply sqrt_le_left (by norm_num) |>.2
      have h := sqrt_le_sqrt (le_of_not_ge hlarge)
      norm_num at h ⊢
      linarith
    have hpw : (2 : ℝ) ^ j ≤ 2 * (2 ^ j / y ^ (1 / 4 : ℝ)) := by
      have h := mul_le_mul_of_nonneg_left hsmall
        (by positivity : 0 ≤ (2 : ℝ) ^ j / y ^ (1 / 4 : ℝ))
      rw [div_mul_cancel₀ _ hroot.ne'] at h
      nlinarith
    have hcoef : 3 * (2 : ℝ) ^ j ≤
        (4 * C + 6) * (1 / log (3 * y) + 2 ^ j / y ^ (1 / 4 : ℝ)) := by
      have hinv : 0 ≤ 1 / log (3 * y) := by positivity
      have herr : 0 ≤ (2 : ℝ) ^ j / y ^ (1 / 4 : ℝ) := by positivity
      nlinarith [mul_nonneg hC.le hinv, mul_nonneg hC.le herr]
    have h := mul_le_mul_of_nonneg_right hcoef hm
    nlinarith [hrough]

end BretecheTenenbaumMean
