module

public import BretecheTenenbaumMean.Sieve.SelbergRemainder
public import BretecheTenenbaumMean.PrimeSums.Product

@[expose] public section

/-! # Selberg's sieve on an interval of natural numbers -/

namespace BretecheTenenbaumMean.Sieve

open Finset Real

/-- Exact count of multiples in an interval with strict lower endpoint. -/
theorem card_multiples_Ioc (a b d : ℕ) :
    ((Ioc a b).filter (fun n ↦ d ∣ n)).card = b / d - a / d := by
  have he : (Ioc a b).filter (fun n ↦ d ∣ n) =
      ((Ioc 0 b).filter (fun n ↦ d ∣ n)) \ ((Ioc 0 a).filter (fun n ↦ d ∣ n)) := by
    ext n
    simp only [mem_filter, mem_Ioc, mem_sdiff]
    omega
  by_cases hab : a ≤ b
  · rw [he, card_sdiff_of_subset]
    · rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div]
    · intro n hn
      simp only [mem_filter, mem_Ioc] at hn ⊢
      exact ⟨⟨hn.1.1, hn.1.2.trans hab⟩, hn.2⟩
  · rw [Ioc_eq_empty (by omega), filter_empty, card_empty, Nat.sub_eq_zero_of_le
      (Nat.div_le_div_right (by omega : b ≤ a))]

/-- The discrepancy of the multiples count is bounded by one, uniformly
in the endpoints and the positive modulus. -/
theorem card_multiples_Ioc_error {a b d : ℕ} (hab : a ≤ b) (hd : 0 < d) :
    |(((Ioc a b).filter (fun n ↦ d ∣ n)).card : ℝ) - ((b : ℝ) - a) / d| ≤ 1 := by
  rw [card_multiples_Ioc, Nat.cast_sub (Nat.div_le_div_right hab)]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hdiv (n : ℕ) : 0 ≤ (n : ℝ) / d - (n / d : ℕ) ∧
      (n : ℝ) / d - (n / d : ℕ) < 1 := by
    have he : (n : ℝ) = (n % d : ℕ) + (d : ℝ) * (n / d : ℕ) := by
      exact_mod_cast (Nat.mod_add_div n d).symm
    have hr0 : (0 : ℝ) ≤ (n % d : ℕ) := Nat.cast_nonneg _
    have hr : ((n % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt n hd
    constructor
    · apply sub_nonneg.2
      rw [le_div_iff₀ hd0]
      nlinarith
    · rw [sub_lt_iff_lt_add, div_lt_iff₀ hd0]
      nlinarith
  have ha := hdiv a
  have hb := hdiv b
  rw [sub_div, abs_le]
  constructor <;> linarith

noncomputable def reciprocalDensity : ArithmeticFunction ℝ :=
  ⟨fun n ↦ (n : ℝ)⁻¹, by simp⟩

theorem reciprocalDensity_multiplicative : reciprocalDensity.IsMultiplicative := by
  constructor
  · norm_num [reciprocalDensity]
  · intro m n _
    simp [reciprocalDensity, Nat.cast_mul, mul_comm]

/-- Sifting all primes below `z` from the interval `(a,b]`. -/
noncomputable def intervalSieve (a b : ℕ) (z : ℝ) : BoundingSieve where
  support := Ioc a b
  prodPrimes := primeProduct z
  prodPrimes_squarefree := primeProduct_squarefree z
  weights := fun _ ↦ 1
  weights_nonneg := fun _ ↦ by norm_num
  totalMass := (b : ℝ) - a
  nu := reciprocalDensity
  nu_mult := reciprocalDensity_multiplicative
  nu_pos_of_prime := fun p hp _ ↦ by
    change 0 < (p : ℝ)⁻¹
    exact inv_pos.2 (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := fun p hp _ ↦ by
    change (p : ℝ)⁻¹ < 1
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

theorem intervalSieve_rem_le {a b : ℕ} (hab : a ≤ b) (z : ℝ) {d : ℕ}
    (hd : d ∣ (intervalSieve a b z).prodPrimes) :
    |(intervalSieve a b z).rem d| ≤ 1 := by
  have hd0 := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero (primeProduct_ne_zero z) hd)
  have h := card_multiples_Ioc_error hab hd0
  simpa only [BoundingSieve.rem, BoundingSieve.multSum, intervalSieve, reciprocalDensity,
    ArithmeticFunction.coe_mk, ← sum_filter, sum_const, nsmul_eq_mul, mul_one,
    div_eq_mul_inv, mul_comm] using h

/-- Primes above the sifting cutoff survive the sieve. -/
theorem prime_interval_le_siftedSum {a b : ℕ} {z : ℝ} (hz : z ≤ a) :
    (((Ioc a b).filter Nat.Prime).card : ℝ) ≤ (intervalSieve a b z).siftedSum := by
  classical
  have he : (((Ioc a b).filter Nat.Prime).card : ℝ) =
      ∑ p ∈ Ioc a b, if p.Prime then (1 : ℝ) else 0 := by
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul, mul_one]
  rw [he]
  simp only [BoundingSieve.siftedSum, intervalSieve]
  apply sum_le_sum
  intro p hp
  change (if p.Prime then (1 : ℝ) else 0) ≤ (if (primeProduct z).Coprime p then 1 else 0)
  by_cases hprime : p.Prime
  · have hpn : ¬ p ∣ primeProduct z := by
      intro hdiv
      have hmem : p ∈ (primeProduct z).primeFactors :=
        Nat.mem_primeFactors.2 ⟨hprime, hdiv, primeProduct_ne_zero z⟩
      rw [primeFactors_primeProduct] at hmem
      have hl := (mem_primesLT.1 hmem).2
      have hap : (a : ℝ) < p := by exact_mod_cast (mem_Ioc.1 hp).1
      linarith
    have hcop := (hprime.coprime_iff_not_dvd.2 hpn).symm
    rw [ite_eq_left hprime, ite_eq_left hcop]
  · simp only [hprime, ite_false]
    split_ifs <;> norm_num

/-- The sifting product is at most the reciprocal positive normalizer. -/
theorem siftingProduct_le_normalizer_inv (z : ℝ) :
    (∏ p ∈ primesLT z, (1 - (p : ℝ)⁻¹)) ≤ (normalizer z)⁻¹ := by
  rw [← one_div]
  apply (le_div_iff₀ (normalizer_pos z)).2
  unfold normalizer
  rw [← prod_mul_distrib]
  apply prod_le_one₀
  · intro p hp
    have hp1 : 1 < (p : ℝ) := by exact_mod_cast (mem_primesLT.1 hp).1.one_lt
    have hi : (p : ℝ)⁻¹ ≤ 1 := (inv_lt_one_of_one_lt₀ hp1).le
    exact mul_nonneg (by linarith) (by positivity)
  · intro p _
    nlinarith [sq_nonneg ((p : ℝ)⁻¹)]

/-- Quantitative interval sieve bound, keeping the cutoff as a free parameter.
Its error is small enough to give square-root errors in short prime intervals. -/
theorem prime_interval_sieve_bound : ∃ K ≥ 1, ∀ (a b : ℕ) (z : ℝ),
    a ≤ b → 2 ≤ z → 16 ≤ log z → z ≤ a →
    (((Ioc a b).filter Nat.Prime).card : ℝ) ≤
      4 * ((b : ℝ) - a) / normalizer z + K * z ^ 8 := by
  obtain ⟨K, hK, hbound⟩ := exists_selberg_upper_bound (g := 1) (η := 1) (by norm_num) (by norm_num)
  refine ⟨K, hK, fun a b z hab hz hzlog hza ↦ ?_⟩
  let s := intervalSieve a b z
  have hmass : 0 ≤ (b : ℝ) - a := sub_nonneg.2 (by exact_mod_cast hab)
  have h := hbound s z 1 hz hzlog (by norm_num) hmass
    (by intro p hp; exact (mem_primesLT.1 (by simpa only [s, intervalSieve, primeFactors_primeProduct] using hp)).2.le)
    (by intro p _; change (p : ℝ)⁻¹ ≤ 1 / p; rw [one_div])
    (by
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp)
      change (p : ℝ)⁻¹ ≤ 1 - 1 / (p : ℝ)
      rw [one_div]
      have hi : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
      norm_num at hi
      linarith)
    (by intro d hd; simpa only [one_pow, one_mul] using intervalSieve_rem_le hab z hd)
  norm_num only [s, intervalSieve, reciprocalDensity, ArithmeticFunction.coe_mk,
    primeFactors_primeProduct, one_mul, mul_one, Real.rpow_natCast] at h
  norm_num only [Real.rpow_ofNat] at h
  refine (prime_interval_le_siftedSum hza).trans (h.trans ?_)
  apply add_le_add _ le_rfl
  have he := mul_le_mul_of_nonneg_left (siftingProduct_le_normalizer_inv z)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hmass)
  simpa only [div_eq_mul_inv] using he

end BretecheTenenbaumMean.Sieve
