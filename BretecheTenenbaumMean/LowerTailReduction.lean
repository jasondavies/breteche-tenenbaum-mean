module

public import BretecheTenenbaumMean.SeparatedEvents
public import BretecheTenenbaumMean.TiltedPrimeLayers
public import BretecheTenenbaumMean.SecondMomentPigeonhole

@[expose] public section

/-! # Reduction of the lower tail to marginal prime-count probabilities -/

namespace BretecheTenenbaumMean

open Finset Real

/-- It suffices to remove the bad part of each event locally. This avoids
requiring one integer to satisfy size bounds at every cutoff simultaneously. -/
theorem probability_local_good_union (x : ℝ) (s : Finset ℕ)
    (E G : ℕ → Set ℕ) :
    probability x {n | ∃ i ∈ s, n ∈ E i} -
      (∑ i ∈ s, probability x (E i ∩ (G i)ᶜ)) ≤
    probability x {n | ∃ i ∈ s, n ∈ E i ∩ G i} := by
  have hsub : {n | ∃ i ∈ s, n ∈ E i} ⊆
      {n | ∃ i ∈ s, n ∈ E i ∩ G i} ∪ {n | ∃ i ∈ s, n ∈ E i ∩ (G i)ᶜ} := by
    rintro n ⟨i, hi, he⟩
    by_cases hg : n ∈ G i
    · exact Or.inl ⟨i, hi, he, hg⟩
    · exact Or.inr ⟨i, hi, he, hg⟩
  have hu := (probability_mono x hsub).trans (probability_union_le x _ _)
  have hb := probability_exists_mem_le_sum x s (fun i ↦ E i ∩ (G i)ᶜ)
  linarith

/-- A fixed spacing and size cutoff retain a quarter of the sum of marginal
layer probabilities, and every retained event forces the required moment tail.
All constants are chosen before the ambient cutoff, index set, and offset. -/
theorem lower_tail_dyadic_reduction : ∃ m : ℕ, 0 < m ∧ ∃ K ≥ (1 : ℝ),
    ∃ L₀ > 0, ∀ x : ℝ, ∀ s : Finset ℕ, ∀ t : ℕ,
    (∀ i ∈ s, exp ((2 : ℝ) ^ (m * i)) ≤ x) →
    (∀ i ∈ s, L₀ ≤ (m * i : ℕ) * log 2) →
    (∀ i ∈ s, (m * i + t : ℕ) ≤ 4 * ((m * i : ℕ) * log 2)) →
    (1 / 4 : ℝ) * (∑ i ∈ s, probability (exp ((2 : ℝ) ^ (m * i)))
      {n | n.primeFactors.card = m * i + t}) ≤
    probability x {n | (2 : ℝ) ^ t / (K + 1) ≤ moment 2 n / tau n} := by
  obtain ⟨m, hm, hspacing⟩ := exists_dyadic_spacing
  obtain ⟨D, hD, L₀, hL₀, hbad⟩ := probability_smallPrime_size_exception
    (show (0 : ℝ) < 4 by norm_num)
  let K := max 1 (log (4 * D))
  have hK : 1 ≤ K := le_max_left _ _
  have hsmall : D * exp (-K) ≤ 1 / 4 := by
    have he : 4 * D ≤ exp K := by
      calc
        _ = exp (log (4 * D)) := (exp_log (by positivity)).symm
        _ ≤ _ := exp_le_exp.2 (le_max_right _ _)
    rw [exp_neg, ← div_eq_mul_inv]
    apply (div_le_iff₀ (exp_pos K)).2
    linarith
  refine ⟨m, hm, K, hK, L₀, hL₀, fun x s t hx hL hk ↦ ?_⟩
  let y := fun i : ℕ ↦ exp ((2 : ℝ) ^ (m * i))
  let E : ℕ → Set ℕ := fun i ↦ {n | (smallPrimePart n (y i)).primeFactors.card = m * i + t}
  let G : ℕ → Set ℕ := fun i ↦ {n | (smallPrimePart n (y i) : ℝ) ≤ (y i) ^ K}
  let S := ∑ i ∈ s, probability (y i) {n | n.primeFactors.card = m * i + t}
  have hS : 0 ≤ S := sum_nonneg (fun _ _ ↦ probability_nonneg _ _)
  have hexception : (∑ i ∈ s, probability x (E i ∩ (G i)ᶜ)) ≤ (1 / 4 : ℝ) * S := by
    calc
      _ ≤ ∑ i ∈ s, (D * exp (-K)) * probability (y i) {n | n.primeFactors.card = m * i + t} := by
        apply sum_le_sum
        intro i hi
        have hy : 2 ≤ y i := exp_one_gt_two.le.trans
          (exp_le_exp.2 (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
        have he : E i ∩ (G i)ᶜ = {n | (smallPrimePart n (y i)).primeFactors.card = m * i + t ∧
            (y i) ^ K < (smallPrimePart n (y i) : ℝ)} := by
          ext n
          simp only [E, G, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
        rw [he]
        apply hbad x (y i) (hx i hi) hy
        · simpa only [y, log_exp, log_pow] using hL i hi
        · simpa only [y, log_exp, log_pow] using hk i hi
      _ = (D * exp (-K)) * S := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmall hS
  have hunion : (1 / 2 : ℝ) * S ≤ probability x {n | ∃ i ∈ s, n ∈ E i} :=
    hspacing x s t hx
  have hgood := probability_local_good_union x s E G
  have hquarter : (1 / 4 : ℝ) * S ≤ probability x {n | ∃ i ∈ s, n ∈ E i ∩ G i} := by
    linarith
  apply hquarter.trans
  apply probability_mono_on_support
  intro n hn he
  obtain ⟨i, hi, hcount, hsize⟩ := he
  exact normalized_second_moment_dyadic_layer (mem_smoothSupport.1 hn).1 (m * i) t hK hcount hsize

end BretecheTenenbaumMean
