module

public import BretecheTenenbaumMean.PrimeDampingError

@[expose] public section

/-! # Removing exponential damping for arbitrary bounded prime coefficients -/

namespace BretecheTenenbaumMean

open Real Finset

/-- A uniform bound on the total variation of the kernels removes damping
for any bounded real coefficients, including oscillating cosine coefficients. -/
theorem bounded_prime_unsmoothing : ∃ C ≥ (0 : ℝ), ∀ x : ℝ, exp 1 ≤ x →
    ∀ (f : Nat.Primes → ℝ) (D : ℝ), 0 ≤ D → (∀ p, |f p| ≤ D) →
      Summable (fun p ↦ f p * primeDamping x p.val) ∧
      |(∑ p ∈ primeCutoff x, f p / p.val) -
        ∑' p : Nat.Primes, f p * primeDamping x p.val| ≤ D * C := by
  classical
  obtain ⟨C, hC, herror⟩ := primeDamping_absolute_error_bound
  refine ⟨C, hC, fun x hx f D _hD hf ↦ ?_⟩
  obtain ⟨hE, hEb⟩ := herror x hx
  obtain ⟨A, _hA, hmass⟩ := primeDamping_mass_bound
  have hbase := (hmass x hx).1
  have hb : Summable (fun p ↦ f p * primeDamping x p.val) :=
    (hbase.mul_left D).of_norm_bounded (fun p ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (primeDamping_nonneg x p.val)]
      exact mul_le_mul_of_nonneg_right (hf p) (primeDamping_nonneg x p.val))
  have hzero : ∀ p, p ∉ primeCutoff x → f p * sharpPrimeKernel x p = 0 := by
    intro p hp
    simp only [sharpPrimeKernel, ite_eq_right hp, mul_zero]
  have ha : Summable (fun p ↦ f p * sharpPrimeKernel x p) := summable_of_ne_finset_zero hzero
  have hfinite : (∑' p, f p * sharpPrimeKernel x p) = ∑ p ∈ primeCutoff x, f p / p.val := by
    rw [tsum_eq_sum hzero]
    apply sum_congr rfl
    intro p hp
    simp only [sharpPrimeKernel, ite_eq_left hp, div_eq_mul_inv]
  refine ⟨hb, ?_⟩
  rw [← hfinite, ← ha.tsum_sub hb, ← Real.norm_eq_abs]
  apply (norm_tsum_le_tsum_norm (ha.sub hb).norm).trans
  have hpoint (p : Nat.Primes) :
      ‖f p * sharpPrimeKernel x p - f p * primeDamping x p.val‖ ≤
        D * |sharpPrimeKernel x p - primeDamping x p.val| := by
    rw [← mul_sub, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hf p) (abs_nonneg _)
  calc
    _ ≤ ∑' p : Nat.Primes, D * |sharpPrimeKernel x p - primeDamping x p.val| :=
      (ha.sub hb).norm.tsum_le_tsum hpoint (hE.mul_left D)
    _ = D * ∑' p : Nat.Primes, |sharpPrimeKernel x p - primeDamping x p.val| := tsum_mul_left
    _ ≤ D * C := mul_le_mul_of_nonneg_left hEb _hD

end BretecheTenenbaumMean
