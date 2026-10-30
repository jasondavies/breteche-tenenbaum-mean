module

public import BretecheTenenbaumMean.WindowBounds

@[expose] public section

/-! # Divisor tuples and overlap lengths of windows -/

namespace BretecheTenenbaumMean

open Finset Real MeasureTheory

noncomputable def tupleMin {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ) : ℝ :=
  univ.inf' univ_nonempty a

noncomputable def tupleMax {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ) : ℝ :=
  univ.sup' univ_nonempty a

theorem tupleMin_le {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ) (i : ι) :
    tupleMin a ≤ a i := inf'_le a (mem_univ i)

theorem le_tupleMax {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ) (i : ι) :
    a i ≤ tupleMax a := le_sup' a (mem_univ i)

theorem tupleMin_le_tupleMax {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ) :
    tupleMin a ≤ tupleMax a :=
  (tupleMin_le a (Classical.arbitrary ι)).trans (le_tupleMax a _)

/-- A tuple fits in a window exactly when its extreme coordinates do. -/
theorem mem_tuple_window_iff {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (w u : ℝ) :
    u ∈ Set.Ico (tupleMax a - w) (tupleMin a) ↔ ∀ i, u ∈ Set.Ico (a i - w) (a i) := by
  simp only [Set.mem_Ico]
  constructor
  · intro h i
    exact ⟨by linarith [le_tupleMax a i], lt_of_lt_of_le h.2 (tupleMin_le a i)⟩
  · intro h
    have hmax : tupleMax a ≤ u + w := (sup'_le_iff univ_nonempty a).2 (fun i _ ↦ by linarith [(h i).1])
    have hmin : u < tupleMin a := (lt_inf'_iff univ_nonempty).2 (fun i _ ↦ (h i).2)
    exact ⟨by linarith, hmin⟩

/-- A product of window indicators is the indicator of the overlap interval. -/
theorem prod_window_indicator {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (w u : ℝ) :
    (∏ i, (Set.Ico (a i - w) (a i)).indicator (fun _ : ℝ ↦ (1 : ℝ)) u) =
      (Set.Ico (tupleMax a - w) (tupleMin a)).indicator (fun _ : ℝ ↦ (1 : ℝ)) u := by
  classical
  by_cases h : u ∈ Set.Ico (tupleMax a - w) (tupleMin a)
  · rw [Set.indicator_of_mem h]
    apply prod_eq_one
    intro i _
    exact Set.indicator_of_mem ((mem_tuple_window_iff a w u).1 h i) _
  · rw [Set.indicator_of_notMem h]
    have hn : ¬ ∀ i, u ∈ Set.Ico (a i - w) (a i) := fun hh ↦ h ((mem_tuple_window_iff a w u).2 hh)
    obtain ⟨i, hi⟩ := not_forall.1 hn
    exact prod_eq_zero (mem_univ i) (Set.indicator_of_notMem hi _)

noncomputable def divisorTuples (n q : ℕ) : Finset (Fin q → ℕ) :=
  Fintype.piFinset (fun _ : Fin q ↦ n.divisors)

/-- A divisor window of arbitrary real width. -/
noncomputable def wideDelta (n : ℕ) (w u : ℝ) : ℝ :=
  ∑ d ∈ n.divisors, (Set.Ico (log d - w) (log d)).indicator (fun _ : ℝ ↦ (1 : ℝ)) u

theorem wideDelta_one (n : ℕ) (u : ℝ) : wideDelta n 1 u = delta n u :=
  (delta_eq_sum_indicator n u).symm

theorem wideDelta_nonneg (n : ℕ) (w u : ℝ) : 0 ≤ wideDelta n w u :=
  sum_nonneg (fun _ _ ↦ Set.indicator_nonneg (fun _ _ ↦ by norm_num) _)

/-- The exact finite tuple expansion of a positive power of a window count. -/
theorem wideDelta_pow_eq_tuple_sum (n q : ℕ) [NeZero q] (w u : ℝ) :
    wideDelta n w u ^ q = ∑ d ∈ divisorTuples n q,
      (Set.Ico (tupleMax (fun i ↦ log (d i)) - w) (tupleMin (fun i ↦ log (d i)))).indicator
        (fun _ : ℝ ↦ (1 : ℝ)) u := by
  rw [wideDelta, sum_pow']
  apply sum_congr rfl
  intro d _
  exact prod_window_indicator _ w u

theorem integrable_tuple_window {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ) (w : ℝ) :
    Integrable ((Set.Ico (tupleMax a - w) (tupleMin a)).indicator (fun _ : ℝ ↦ (1 : ℝ))) :=
  (integrableOn_const (measure_Ico_lt_top.ne)).integrable_indicator measurableSet_Ico

theorem integrable_wideDelta_pow (n q : ℕ) [NeZero q] (w : ℝ) :
    Integrable (fun u ↦ wideDelta n w u ^ q) := by
  simp_rw [wideDelta_pow_eq_tuple_sum]
  exact integrable_finsetSum _ (fun d _ ↦ integrable_tuple_window _ w)

/-- The integral of a window power is the sum of the tuple overlap lengths. -/
theorem integral_wideDelta_pow (n q : ℕ) [NeZero q] (w : ℝ) :
    (∫ u : ℝ, wideDelta n w u ^ q) = ∑ d ∈ divisorTuples n q,
      max (w + tupleMin (fun i ↦ log (d i)) - tupleMax (fun i ↦ log (d i))) 0 := by
  simp_rw [wideDelta_pow_eq_tuple_sum]
  rw [integral_finsetSum _ (fun d _ ↦ integrable_tuple_window _ w)]
  apply sum_congr rfl
  intro d _
  rw [integral_indicator_const (1 : ℝ) measurableSet_Ico]
  simp only [smul_eq_mul, mul_one, Real.volume_real_Ico]
  congr 1
  ring

/-- The general-order version of the divisor-pair overlap formula. -/
theorem moment_eq_tuple_sum (n q : ℕ) [NeZero q] :
    moment q n = ∑ d ∈ divisorTuples n q,
      max (1 + tupleMin (fun i ↦ log (d i)) - tupleMax (fun i ↦ log (d i))) 0 := by
  simpa only [wideDelta_one, moment] using integral_wideDelta_pow n q 1

/-- A width-two window splits into two adjacent unit windows. -/
theorem wideDelta_two (n : ℕ) (u : ℝ) : wideDelta n 2 u = delta n u + delta n (u + 1) := by
  rw [delta_eq_sum_indicator, delta_eq_sum_indicator, ← sum_add_distrib]
  apply sum_congr rfl
  intro d _
  simp only [Set.indicator_apply, Set.mem_Ico]
  split_ifs <;> norm_num at * <;> grind

/-- The doubled-width moment has at most `2^q` times the unit-width mass. -/
theorem integral_wideDelta_two_le (n q : ℕ) [NeZero q] :
    (∫ u : ℝ, wideDelta n 2 u ^ q) ≤ 2 ^ q * moment q n := by
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hi := integrable_delta_pow n q hq
  have hs := hi.comp_add_right 1
  calc
    _ ≤ ∫ u : ℝ, 2 ^ (q - 1) * (delta n u ^ q + delta n (u + 1) ^ q) := by
      apply integral_mono (integrable_wideDelta_pow n q 2) ((hi.add hs).const_mul _)
      intro u
      change wideDelta n 2 u ^ q ≤ 2 ^ (q - 1) * (delta n u ^ q + delta n (u + 1) ^ q)
      rw [wideDelta_two]
      exact add_pow_le (delta_nonneg n u) (delta_nonneg n (u + 1)) q
    _ = 2 ^ q * moment q n := by
      rw [integral_const_mul, integral_add hi hs, integral_add_right_eq_self (fun u : ℝ ↦ delta n u ^ q) (1 : ℝ)]
      change 2 ^ (q - 1) * (moment q n + moment q n) = 2 ^ q * moment q n
      have hpow : (2 : ℝ) ^ q = 2 ^ (q - 1) * 2 := by
        conv_lhs => rw [← Nat.sub_add_cancel hq]
        exact pow_succ _ _
      rw [hpow]
      ring

/-- The number of coherent divisor tuples is controlled by the moment.
This is the source of the `2^j` factor in the prime-averaging error. -/
theorem coherent_tuple_count_le (n q : ℕ) [NeZero q] :
    (∑ d ∈ divisorTuples n q,
      if tupleMax (fun i ↦ log (d i)) < tupleMin (fun i ↦ log (d i)) + 1 then (1 : ℝ) else 0) ≤
        2 ^ q * moment q n := by
  calc
    _ ≤ ∑ d ∈ divisorTuples n q,
        max (2 + tupleMin (fun i ↦ log (d i)) - tupleMax (fun i ↦ log (d i))) 0 := by
      apply sum_le_sum
      intro d _
      split_ifs with h
      · exact (by linarith : (1 : ℝ) ≤ 2 + tupleMin (fun i ↦ log (d i)) - tupleMax (fun i ↦ log (d i))).trans (le_max_left _ _)
      · exact le_max_right _ _
    _ = ∫ u : ℝ, wideDelta n 2 u ^ q := (integral_wideDelta_pow n q 2).symm
    _ ≤ _ := integral_wideDelta_two_le n q

end BretecheTenenbaumMean
