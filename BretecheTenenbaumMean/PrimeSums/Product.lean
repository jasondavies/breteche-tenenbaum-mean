module

public import BretecheTenenbaumMean.PrimeSums.Strict

@[expose] public section

/-! # Uniform estimates for the finite Euler products

The probability normalizer is comparable to `log x`. We also bound the error
in replacing the logarithm of an Euler product by its linear prime sum.
-/

open Real Finset

namespace BretecheTenenbaumMean.PrimeSums

/-- The elementary quadratic remainder for a nonnegative Euler factor. -/
theorem abs_log_one_add_sub_le {t : ℝ} (ht : 0 ≤ t) :
    |log (1 + t) - t| ≤ t ^ 2 := by
  have hp : 0 < 1 + t := by linarith
  have hu := log_le_sub_one_of_pos hp
  have hl := one_sub_inv_le_log_of_pos hp
  have hi : (1 + t) * (1 + t)⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
  have h : t - t ^ 2 ≤ 1 - (1 + t)⁻¹ := by
    have : 0 ≤ t ^ 3 := by positivity
    nlinarith [mul_nonneg ht (inv_nonneg.2 hp.le)]
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- Telescoping reciprocal differences (as in the example project's product proof). -/
theorem sum_Ico_inv_sub_inv {m M : ℕ} (hmM : m ≤ M) :
    ∑ n ∈ Ico m M, (((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹) =
      ((m : ℝ) - 1)⁻¹ - ((M : ℝ) - 1)⁻¹ := by
  induction M, hmM using Nat.le_induction with
  | base => simp
  | succ M hmM ih =>
    rw [sum_Ico_succ_top hmM, ih]
    push_cast
    ring

/-- A uniform elementary bound; no asymptotic estimate is needed for the quadratic error. -/
theorem sum_prime_inv_sq_le_one (x : ℝ) :
    ∑ p ∈ primesLT x, ((p : ℝ)⁻¹) ^ 2 ≤ 1 := by
  let N := max 2 (⌊x⌋₊ + 1)
  have hsub : primesLT x ⊆ Ico 2 N := by
    intro p hp
    have h := mem_primesLT.1 hp
    exact mem_Ico.2 ⟨h.1.two_le,
      (Nat.lt_succ_of_le (Nat.le_floor h.2.le)).trans_le (le_max_right _ _)⟩
  have hbound : ∀ n ∈ Ico 2 N, ((n : ℝ)⁻¹) ^ 2 ≤
      ((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹ := by
    intro n hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (mem_Ico.1 hn).1
    have hn0 : 0 < (n : ℝ) := by linarith
    have hn1 : 0 < (n : ℝ) - 1 := by linarith
    have he : ((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹ =
        ((n : ℝ) - 1)⁻¹ * (n : ℝ)⁻¹ := by field_simp; ring
    rw [he, pow_two]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hn1 (by linarith)) (by positivity)
  calc ∑ p ∈ primesLT x, ((p : ℝ)⁻¹) ^ 2
      ≤ ∑ n ∈ Ico 2 N, ((n : ℝ)⁻¹) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
    _ ≤ ∑ n ∈ Ico 2 N, (((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹) := sum_le_sum hbound
    _ = 1 - ((N : ℝ) - 1)⁻¹ := by
        simpa only [Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, inv_one] using
          (sum_Ico_inv_sub_inv (m := 2) (M := N) (le_max_left _ _))
    _ ≤ 1 := by
        have : (2 : ℝ) ≤ N := by exact_mod_cast le_max_left 2 (⌊x⌋₊ + 1)
        have : 0 ≤ ((N : ℝ) - 1)⁻¹ := inv_nonneg.2 (by linarith)
        linarith

/-- Uniform in the cutoff and in all weights between `0` and `A`. -/
theorem abs_log_prod_sub_sum_le {x A : ℝ} {w : ℕ → ℝ}
    (hw : ∀ p ∈ primesLT x, 0 ≤ w p ∧ w p ≤ A) :
    |log (∏ p ∈ primesLT x, (1 + w p / p)) - ∑ p ∈ primesLT x, w p / p| ≤ A ^ 2 := by
  have hp : ∀ p ∈ primesLT x, 0 < 1 + w p / p := by
    intro p hp
    have := (hw p hp).1
    positivity
  rw [log_prod (fun p hp' ↦ (hp p hp').ne'), ← sum_sub_distrib]
  calc |∑ p ∈ primesLT x, (log (1 + w p / p) - w p / p)|
      ≤ ∑ p ∈ primesLT x, |log (1 + w p / p) - w p / p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ primesLT x, A ^ 2 * ((p : ℝ)⁻¹) ^ 2 := by
        refine sum_le_sum fun p hp' ↦ (abs_log_one_add_sub_le (by
          exact div_nonneg (hw p hp').1 (Nat.cast_nonneg p))).trans ?_
        rw [div_eq_mul_inv, mul_pow]
        gcongr
        exacts [(hw p hp').1, (hw p hp').2]
    _ = A ^ 2 * ∑ p ∈ primesLT x, ((p : ℝ)⁻¹) ^ 2 := (mul_sum _ _ _).symm
    _ ≤ A ^ 2 := by nlinarith [sum_prime_inv_sq_le_one x, sq_nonneg A]

theorem abs_log_normalizer_sub_SLT_le (x : ℝ) :
    |log (normalizer x) - SLT x| ≤ 1 := by
  simpa only [normalizer, SLT, one_div, one_pow] using
    abs_log_prod_sub_sum_le (x := x) (A := 1) (w := fun _ ↦ 1) (by intros; norm_num)

/-- Logarithmic form of the two-sided Mertens estimate for the normalizer. -/
theorem abs_log_normalizer_sub_loglog_le :
    ∃ C ≥ 0, ∀ x ≥ 2, |log (normalizer x) - log (log x)| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := abs_SLT_sub_loglog_le
  refine ⟨1 + C, by positivity, fun x hx ↦ ?_⟩
  calc |log (normalizer x) - log (log x)|
      ≤ |log (normalizer x) - SLT x| + |SLT x - log (log x)| := abs_sub_le _ _ _
    _ ≤ 1 + C := add_le_add (abs_log_normalizer_sub_SLT_le x) (hC x hx)

/-- The normalizing product has order `log x`, uniformly for `x ≥ 2`. -/
theorem normalizer_bounds : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ x ≥ 2, c * log x ≤ normalizer x ∧ normalizer x ≤ C * log x := by
  obtain ⟨K, -, hK⟩ := abs_log_normalizer_sub_loglog_le
  refine ⟨exp (-K), exp K, exp_pos _, exp_pos _, fun x hx ↦ ?_⟩
  have hl : 0 < log x := log_pos (by linarith)
  have h := abs_le.1 (hK x hx)
  constructor
  · calc exp (-K) * log x = exp (-K + log (log x)) := by rw [exp_add, exp_log hl]
         _ ≤ exp (log (normalizer x)) := exp_le_exp.2 (by linarith)
         _ = normalizer x := exp_log (normalizer_pos x)
  · calc normalizer x = exp (log (normalizer x)) := (exp_log (normalizer_pos x)).symm
         _ ≤ exp (K + log (log x)) := exp_le_exp.2 (by linarith)
         _ = exp K * log x := by rw [exp_add, exp_log hl]

/-- Bounds for an interval of primes, as used in the probabilities of §2.1. -/
theorem normalizer_ratio_bounds : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ x y, 2 ≤ x → 2 ≤ y →
      c * (log y / log x) ≤ normalizer y / normalizer x ∧
      normalizer y / normalizer x ≤ C * (log y / log x) := by
  obtain ⟨c, C, hc, hC, h⟩ := normalizer_bounds
  refine ⟨c / C, C / c, div_pos hc hC, div_pos hC hc, fun x y hx hy ↦ ?_⟩
  have hxlog : 0 < log x := log_pos (by linarith)
  have hylog : 0 < log y := log_pos (by linarith)
  constructor
  · calc c / C * (log y / log x) = (c * log y) / (C * log x) := by ring
         _ ≤ normalizer y / normalizer x :=
           div_le_div₀ (normalizer_pos y).le (h y hy).1 (normalizer_pos x) (h x hx).2
  · calc normalizer y / normalizer x ≤ (C * log y) / (c * log x) :=
           div_le_div₀ (by positivity) (h y hy).2 (mul_pos hc hxlog) (h x hx).1
         _ = C / c * (log y / log x) := by ring

/-- Constant-weight Euler products, with constants allowed to depend on the weight. -/
theorem prod_one_add_nat_div_le (a : ℕ) : ∃ C > 0, ∀ x ≥ 2,
    (∏ p ∈ primesLT x, (1 + (a : ℝ) / p)) ≤ C * log x ^ a := by
  obtain ⟨K, hK0, hK⟩ := abs_SLT_sub_loglog_le
  refine ⟨exp ((a : ℝ) * K + (a : ℝ) ^ 2), exp_pos _, fun x hx ↦ ?_⟩
  have hxlog : 0 < log x := log_pos (by linarith)
  have hp : 0 < ∏ p ∈ primesLT x, (1 + (a : ℝ) / p) :=
    prod_pos (fun _ _ ↦ by positivity)
  have h := (abs_le.1 (abs_log_prod_sub_sum_le (x := x) (A := a)
    (w := fun _ ↦ a) (fun _ _ ↦ ⟨Nat.cast_nonneg a, le_rfl⟩))).2
  have hs : ∑ p ∈ primesLT x, (a : ℝ) / p = (a : ℝ) * SLT x := by
    simp only [SLT, div_eq_mul_inv, mul_sum]
  rw [hs] at h
  have hlog : log (∏ p ∈ primesLT x, (1 + (a : ℝ) / p)) ≤
      (a : ℝ) * K + (a : ℝ) ^ 2 + (a : ℝ) * log (log x) := by
    have h' := mul_le_mul_of_nonneg_left (abs_le.1 (hK x hx)).2 (Nat.cast_nonneg a)
    nlinarith
  calc ∏ p ∈ primesLT x, (1 + (a : ℝ) / p)
      = exp (log (∏ p ∈ primesLT x, (1 + (a : ℝ) / p))) := (exp_log hp).symm
    _ ≤ exp ((a : ℝ) * K + (a : ℝ) ^ 2 + (a : ℝ) * log (log x)) := exp_le_exp.2 hlog
    _ = exp ((a : ℝ) * K + (a : ℝ) ^ 2) * log x ^ a := by
        rw [exp_add, exp_nat_mul, exp_log hxlog]

/-- `E_x(τ^k) ≪_k (log x)^(2^k-1)`, including `k = 0`. -/
theorem expectation_tau_pow_le (k : ℕ) : ∃ C > 0, ∀ x ≥ 2,
    expectation x (fun n ↦ tau n ^ k) ≤ C * log x ^ (2 ^ k - 1) := by
  obtain ⟨c, _, hc, _, h⟩ := normalizer_bounds
  obtain ⟨C, hC, hprod⟩ := prod_one_add_nat_div_le (2 ^ k)
  refine ⟨C / c, div_pos hC hc, fun x hx ↦ ?_⟩
  have hxlog : 0 < log x := log_pos (by linarith)
  have hprod' : (∏ p ∈ primesLT x, (1 + (2 : ℝ) ^ k / p)) ≤ C * log x ^ (2 ^ k) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hprod x hx
  rw [expectation_tau_pow]
  calc (∏ p ∈ primesLT x, (1 + (2 : ℝ) ^ k / p)) / normalizer x
      ≤ (C * log x ^ (2 ^ k)) / (c * log x) :=
        div_le_div₀ (by positivity) hprod' (mul_pos hc hxlog) (h x hx).1
    _ = C / c * log x ^ (2 ^ k - 1) := by
        have he : 2 ^ k = (2 ^ k - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_pow k 2 (by decide))).symm
        conv_lhs => rw [he, pow_succ]
        field_simp

end BretecheTenenbaumMean.PrimeSums
