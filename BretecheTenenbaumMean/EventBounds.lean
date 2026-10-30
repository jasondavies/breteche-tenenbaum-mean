module

public import BretecheTenenbaumMean.Probability

@[expose] public section

/-! # Elementary event bounds for the finite probability model -/

namespace BretecheTenenbaumMean

open Real

theorem probability_mono (x : ℝ) {E F : Set ℕ} (hEF : E ⊆ F) :
    probability x E ≤ probability x F := by
  classical
  apply expectation_mono
  intro n _
  by_cases hn : n ∈ E
  · simp only [Set.indicator_of_mem hn, Set.indicator_of_mem (hEF hn), le_refl]
  · simp only [Set.indicator_of_notMem hn]
    exact Set.indicator_nonneg (fun _ _ ↦ zero_le_one) n

theorem probability_union_le (x : ℝ) (E F : Set ℕ) :
    probability x (E ∪ F) ≤ probability x E + probability x F := by
  classical
  unfold probability
  rw [← expectation_add]
  apply expectation_mono
  intro n _
  by_cases he : n ∈ E <;> by_cases hf : n ∈ F <;> simp [Set.indicator, he, hf]

/-- Markov's inequality restricted to any arithmetic event. -/
theorem probability_inter_gt_le (x : ℝ) (E : Set ℕ) (f : ℕ → ℝ)
    (hf : ∀ n ∈ smoothSupport x, 0 ≤ f n) {R : ℝ} (hR : 0 < R) :
    probability x {n | n ∈ E ∧ R < f n} ≤ expectation x (E.indicator f) / R := by
  classical
  have he : {n | n ∈ E ∧ R < f n} = {n | R < E.indicator f n} := by
    ext n
    by_cases hn : n ∈ E
    · simp only [Set.mem_ofPred_eq, hn, true_and, Set.indicator_of_mem hn]
    · simp only [Set.mem_ofPred_eq, hn, false_and, Set.indicator_of_notMem hn, not_lt.mpr hR.le]
  rw [he]
  apply probability_gt_le x _ hR
  intro n hn
  by_cases he : n ∈ E
  · simpa only [Set.indicator_of_mem he] using hf n hn
  · simp only [Set.indicator_of_notMem he, le_refl]

/-- Partition an upper-tail event over any finite range containing the statistic. -/
theorem probability_ge_eq_sum_fibers_of_mem (x : ℝ) (g : ℕ → ℕ) (k : ℕ) (s : Finset ℕ)
    (hs : ∀ n ∈ smoothSupport x, g n ∈ s) :
    probability x {n | k ≤ g n} =
      ∑ r ∈ s.filter (fun r ↦ k ≤ r),
        probability x {n | g n = r} := by
  classical
  unfold probability expectation
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.sum_div]
  congr 1
  by_cases hg : k ≤ g n
  · rw [Set.indicator_of_mem (show n ∈ {m | k ≤ g m} from hg)]
    symm
    calc
      _ = ({m | g m = g n} : Set ℕ).indicator (fun _ ↦ (1 : ℝ)) n := by
        apply Finset.sum_eq_single (g n)
        · intro r _ hr
          apply Set.indicator_of_notMem
          exact fun h ↦ hr h.symm
        · intro hnot
          exact (hnot (Finset.mem_filter.2 ⟨hs n hn, hg⟩)).elim
      _ = 1 := Set.indicator_of_mem (show n ∈ {m | g m = g n} from rfl) _
  · rw [Set.indicator_of_notMem (show n ∉ {m | k ≤ g m} from hg)]
    symm
    apply Finset.sum_eq_zero
    intro r hr
    apply Set.indicator_of_notMem
    intro he
    exact hg (he.symm ▸ (Finset.mem_filter.1 hr).2)

/-- Events need only agree on the finite support of the probability model. -/
theorem probability_congr_on_support (x : ℝ) {E F : Set ℕ}
    (h : ∀ n ∈ smoothSupport x, n ∈ E ↔ n ∈ F) : probability x E = probability x F := by
  classical
  unfold probability expectation
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Set.indicator, h n hn]

/-- Event inclusion can likewise be checked only on the finite support. -/
theorem probability_mono_on_support (x : ℝ) {E F : Set ℕ}
    (h : ∀ n ∈ smoothSupport x, n ∈ E → n ∈ F) : probability x E ≤ probability x F := by
  classical
  apply expectation_mono
  intro n hn
  by_cases he : n ∈ E
  · simp only [Set.indicator_of_mem he, Set.indicator_of_mem (h n hn he), le_refl]
  · simp only [Set.indicator_of_notMem he]
    exact Set.indicator_nonneg (fun _ _ ↦ zero_le_one) n

/-- Finite Boole inequality for an indexed family of events. -/
theorem probability_exists_mem_le_sum (x : ℝ) (s : Finset ℕ) (E : ℕ → Set ℕ) :
    probability x {n | ∃ j ∈ s, n ∈ E j} ≤ ∑ j ∈ s, probability x (E j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [probability, expectation, Set.indicator]
  | @insert j s hj ih =>
    have he : {n | ∃ i ∈ insert j s, n ∈ E i} = E j ∪ {n | ∃ i ∈ s, n ∈ E i} := by
      ext n
      simp
    rw [he, Finset.sum_insert hj]
    exact (probability_union_le x _ _).trans (add_le_add le_rfl ih)

end BretecheTenenbaumMean
