module

public import BretecheTenenbaumMean.PrimeDamping

@[expose] public section

/-! # A uniformly bounded error between sharp and damped prime kernels -/

namespace BretecheTenenbaumMean

open Real Finset

/-- The strict prime cutoff, indexed by the type of rational primes. -/
noncomputable def primeCutoff (x : ℝ) : Finset Nat.Primes :=
  (primesLT x).subtype Nat.Prime

theorem sum_primeCutoff (x : ℝ) (f : ℕ → ℝ) :
    (∑ p ∈ primeCutoff x, f p.val) = ∑ p ∈ primesLT x, f p :=
  sum_subtype_of_mem f (fun _ hp ↦ (mem_primesLT.mp hp).1)

/-- The reciprocal-prime kernel with the original strict cutoff. -/
noncomputable def sharpPrimeKernel (x : ℝ) (p : Nat.Primes) : ℝ :=
  if p ∈ primeCutoff x then (p.val : ℝ)⁻¹ else 0

theorem primeDamping_le_inv {x : ℝ} (hx : 1 < x) (p : Nat.Primes) :
    primeDamping x p.val ≤ (p.val : ℝ)⁻¹ := by
  have hlx : 0 ≤ (log x)⁻¹ := inv_nonneg.mpr (log_pos hx).le
  have hlp : 0 ≤ log (p.val : ℝ) := log_nonneg (by exact_mod_cast p.prop.one_le)
  have he : exp (-(log x)⁻¹ * log p.val) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  simpa [primeDamping, one_div] using div_le_div_of_nonneg_right he (Nat.cast_nonneg p.val)

/-- The total variation between the sharp reciprocal-prime kernel and its
exponentially damped counterpart stays bounded independently of the cutoff. -/
theorem primeDamping_absolute_error_bound : ∃ C ≥ (0 : ℝ), ∀ x : ℝ, exp 1 ≤ x →
    Summable (fun p : Nat.Primes ↦ |sharpPrimeKernel x p - primeDamping x p.val|) ∧
      (∑' p : Nat.Primes, |sharpPrimeKernel x p - primeDamping x p.val|) ≤ C := by
  classical
  obtain ⟨A, hA, hmass⟩ := primeDamping_mass_bound
  obtain ⟨B, hB, hloss⟩ := primeDamping_lower_loss_bound
  obtain ⟨D, hD, hmertens⟩ := PrimeSums.abs_SLT_sub_loglog_le
  refine ⟨A + D + 2 * B, by positivity, fun x hx ↦ ?_⟩
  have hx2 : 2 ≤ x := (by nlinarith [Real.add_one_le_exp (1 : ℝ)] : (2 : ℝ) ≤ exp 1).trans hx
  have hx1 : 1 < x := by linarith
  let l : Nat.Primes → ℝ := fun p ↦ if p ∈ primeCutoff x then
    (p.val : ℝ)⁻¹ - primeDamping x p.val else 0
  have hsharp0 : ∀ p, p ∉ primeCutoff x → sharpPrimeKernel x p = 0 := by
    intro p hp
    simp [sharpPrimeKernel, hp]
  have hl0 : ∀ p, p ∉ primeCutoff x → l p = 0 := by
    intro p hp
    simp only [l, ite_eq_right hp]
  have hsharp : Summable (sharpPrimeKernel x) := summable_of_ne_finset_zero hsharp0
  have hl : Summable l := summable_of_ne_finset_zero hl0
  obtain ⟨hd, hdbound⟩ := hmass x hx
  have he (p : Nat.Primes) : |sharpPrimeKernel x p - primeDamping x p.val| =
      (primeDamping x p.val - sharpPrimeKernel x p) + 2 * l p := by
    by_cases hp : p ∈ primeCutoff x
    · simp only [sharpPrimeKernel, l, ite_eq_left hp]
      rw [abs_of_nonneg (sub_nonneg.mpr (primeDamping_le_inv hx1 p))]
      ring
    · simp only [sharpPrimeKernel, l, ite_eq_right hp, zero_sub, abs_neg,
        abs_of_nonneg (primeDamping_nonneg x p.val), sub_zero, mul_zero, add_zero]
  have hsum : Summable (fun p : Nat.Primes ↦ |sharpPrimeKernel x p - primeDamping x p.val|) :=
    ((hd.sub hsharp).add (hl.mul_left 2)).congr (fun p ↦ (he p).symm)
  refine ⟨hsum, ?_⟩
  have hsval : (∑' p, sharpPrimeKernel x p) = PrimeSums.SLT x := by
    rw [tsum_eq_sum hsharp0]
    simp only [sharpPrimeKernel, sum_ite_mem, inter_self]
    exact sum_primeCutoff x (fun p ↦ (p : ℝ)⁻¹)
  have hlval : (∑' p, l p) = ∑ p ∈ primesLT x, ((p : ℝ)⁻¹ - primeDamping x p) := by
    rw [tsum_eq_sum hl0]
    simp only [l, sum_ite_mem, inter_self]
    exact sum_primeCutoff x (fun p ↦ (p : ℝ)⁻¹ - primeDamping x p)
  have heq : (∑' p : Nat.Primes, |sharpPrimeKernel x p - primeDamping x p.val|) =
      (∑' p : Nat.Primes, primeDamping x p.val) - PrimeSums.SLT x +
        2 * ∑ p ∈ primesLT x, ((p : ℝ)⁻¹ - primeDamping x p) := by
    simp_rw [he]
    rw [(hd.sub hsharp).tsum_add (hl.mul_left 2), hd.tsum_sub hsharp, tsum_mul_left, hsval, hlval]
  rw [heq]
  have hm := hmertens x hx2
  have hh := (hloss x hx2).2
  have hupper := (abs_le.mp hdbound).2
  have hlower := (abs_le.mp hm).1
  linarith

end BretecheTenenbaumMean
