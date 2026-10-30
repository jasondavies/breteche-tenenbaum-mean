module

public import BretecheTenenbaumMean.PolynomialSmoothedPrimeSum
public import BretecheTenenbaumMean.PrimeSums.LogTail
public import BretecheTenenbaumMean.PrimeSums.Strict

@[expose] public section

/-! # Real exponential damping of reciprocal prime sums -/

namespace BretecheTenenbaumMean

open Real Finset

/-- The real part of a prime Dirichlet term is the usual cosine term with
an exponential damping factor. -/
theorem real_primeDirichlet_term (a p δ θ : ℝ) (hp : 0 < p) :
    ((a : ℂ) / (p : ℂ) ^ ((1 + δ : ℝ) + θ * Complex.I)).re =
      a * cos (θ * log p) / p * exp (-δ * log p) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
    ← Complex.ofReal_log hp.le, div_eq_mul_inv, ← Complex.exp_neg]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_re, Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
  rw [Real.cos_neg, mul_comm (log p) θ]
  have he : -(log p * (1 + δ)) = -log p + (-δ * log p) := by ring
  rw [he, Real.exp_add, Real.exp_neg, Real.exp_log hp]
  ring

/-- The positive damping kernel used at scale `1/log x`. -/
noncomputable def primeDamping (x : ℝ) (p : ℕ) : ℝ :=
  exp (-(log x)⁻¹ * log p) / p

theorem primeDamping_nonneg (x : ℝ) (p : ℕ) : 0 ≤ primeDamping x p := by
  unfold primeDamping
  positivity

/-- Specializing the polynomial estimate to `X` gives the mass of the
positive damping kernel. -/
theorem primeDamping_mass_bound : ∃ C ≥ (0 : ℝ), ∀ x : ℝ, exp 1 ≤ x →
    Summable (fun p : Nat.Primes ↦ primeDamping x p.val) ∧
      |(∑' p : Nat.Primes, primeDamping x p.val) - log (log x)| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := smoothed_polynomialRoot_sum_log_ratio Polynomial.X
    Polynomial.irreducible_X (by simp)
  refine ⟨C, hC, fun x hx ↦ ?_⟩
  obtain ⟨hs, hb⟩ := hbound x 0 hx (by norm_num)
  have he (p : Nat.Primes) :
      ((NairTenenbaum.rootCount Polynomial.X p.val : ℂ) /
        (p.val : ℂ) ^ ((1 + (log x)⁻¹ : ℝ) + (0 : ℝ) * Complex.I)).re = primeDamping x p.val := by
    rw [NairTenenbaum.rootCount_X]
    have hp : (0 : ℝ) < p.val := Nat.cast_pos.mpr p.prop.pos
    simpa [primeDamping, div_eq_mul_inv, mul_comm] using real_primeDirichlet_term 1 p.val (log x)⁻¹ 0 hp
  refine ⟨(Complex.reCLM.summable hs).congr he, ?_⟩
  rw [Complex.re_tsum hs] at hb
  simp only [abs_zero, zero_mul, add_zero, div_one] at hb
  simpa only [he] using hb

/-- Exponential damping removes only bounded mass below its cutoff. -/
theorem primeDamping_lower_loss_bound : ∃ B > (0 : ℝ), ∀ x : ℝ, 2 ≤ x →
    0 ≤ (∑ p ∈ primesLT x, ((p : ℝ)⁻¹ - primeDamping x p)) ∧
      (∑ p ∈ primesLT x, ((p : ℝ)⁻¹ - primeDamping x p)) ≤ B := by
  obtain ⟨B, hB, hlog⟩ := PrimeSums.primeLogSum_le_mul_log
  refine ⟨B, hB, fun x hx ↦ ?_⟩
  have hlx : 0 < log x := log_pos (by linarith)
  have hlocal (p : ℕ) (hp : p ∈ primesLT x) :
      0 ≤ (p : ℝ)⁻¹ - primeDamping x p ∧
      (p : ℝ)⁻¹ - primeDamping x p ≤ (log x)⁻¹ * (log p / p) := by
    have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (mem_primesLT.mp hp).1.pos
    have hlp : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast (mem_primesLT.mp hp).1.one_le)
    have ht : 0 ≤ (log x)⁻¹ * log p := mul_nonneg (inv_nonneg.mpr hlx.le) hlp
    have he1 : exp (-(log x)⁻¹ * log p) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
    have he2 := Real.add_one_le_exp (-(log x)⁻¹ * log p)
    unfold primeDamping
    constructor
    · rw [inv_eq_one_div, ← sub_div]
      exact div_nonneg (by linarith) hp0.le
    · have h := div_le_div_of_nonneg_right (show 1 - exp (-(log x)⁻¹ * log p) ≤
          (log x)⁻¹ * log p by linarith) hp0.le
      convert h using 1 <;> ring
  refine ⟨sum_nonneg (fun p hp ↦ (hlocal p hp).1), ?_⟩
  have hlogs : (∑ p ∈ primesLT x, log p / p) ≤ Sieve.primeLogSum x := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor (mem_primesLT.mp hp).2.le⟩,
        (mem_primesLT.mp hp).1⟩
    · intro p hp _
      exact div_nonneg (log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le))
        (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ p ∈ primesLT x, (log x)⁻¹ * (log p / p) := sum_le_sum (fun p hp ↦ (hlocal p hp).2)
    _ = (log x)⁻¹ * ∑ p ∈ primesLT x, log p / p := (mul_sum ..).symm
    _ ≤ (log x)⁻¹ * (B * log x) := mul_le_mul_of_nonneg_left (hlogs.trans (hlog x hx))
      (inv_nonneg.mpr hlx.le)
    _ = B := by field_simp

end BretecheTenenbaumMean
