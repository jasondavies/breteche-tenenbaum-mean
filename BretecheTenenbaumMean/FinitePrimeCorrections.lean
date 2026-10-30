module

public import BretecheTenenbaumMean.DedekindEulerLog

@[expose] public section

/-! # Uniform bounds for finitely many exceptional prime coefficients -/

namespace BretecheTenenbaumMean

/-- A reciprocal prime Dirichlet term has norm at most one in the closed
right half-plane `Re(s) ≥ 1`. -/
theorem prime_reciprocal_cpow_norm_le_one (p : Nat.Primes) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖1 / (p.val : ℂ) ^ s‖ ≤ 1 := by
  rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos p.prop.pos]
  have hp : (1 : ℝ) ≤ p.val := by exact_mod_cast p.prop.one_lt.le
  exact (div_le_one (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _)).mpr
    (Real.one_le_rpow hp (by linarith))

/-- Changing finitely many prime coefficients preserves convergence and costs
a uniformly bounded amount throughout `Re(s) ≥ 1`. -/
theorem finite_primeDirichlet_correction (a b : Nat.Primes → ℂ) (S : Finset Nat.Primes)
    (hab : ∀ p, p ∉ S → a p = b p) :
    ∃ C ≥ (0 : ℝ), ∀ s : ℂ, 1 ≤ s.re →
      Summable (fun p ↦ b p / (p.val : ℂ) ^ s) →
      Summable (fun p ↦ a p / (p.val : ℂ) ^ s) ∧
        ‖(∑' p, a p / (p.val : ℂ) ^ s) - (∑' p, b p / (p.val : ℂ) ^ s)‖ ≤ C := by
  classical
  refine ⟨∑ p ∈ S, ‖a p - b p‖, Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _),
    fun s hs hb ↦ ?_⟩
  let d := fun p ↦ (a p - b p) / (p.val : ℂ) ^ s
  have hd0 : ∀ p, p ∉ S → d p = 0 := by
    intro p hp
    simp [d, hab p hp]
  have hd : HasSum d (∑ p ∈ S, d p) := hasSum_sum_of_ne_finset_zero hd0
  have ha : Summable (fun p ↦ a p / (p.val : ℂ) ^ s) :=
    (hd.summable.add hb).congr (fun p ↦ by dsimp [d]; ring)
  refine ⟨ha, ?_⟩
  have heq : (∑' p, a p / (p.val : ℂ) ^ s) - (∑' p, b p / (p.val : ℂ) ^ s) =
      ∑ p ∈ S, d p := by
    rw [← ha.tsum_sub hb]
    convert hd.tsum_eq using 1
    apply tsum_congr
    intro p
    exact (sub_div _ _ _).symm
  rw [heq]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p _
  calc
    ‖d p‖ = ‖a p - b p‖ * ‖1 / (p.val : ℂ) ^ s‖ := by
      dsimp [d]
      rw [← norm_mul]
      congr 1
      ring
    _ ≤ ‖a p - b p‖ * 1 := mul_le_mul_of_nonneg_left
      (prime_reciprocal_cpow_norm_le_one p hs) (norm_nonneg _)
    _ = _ := mul_one _

end BretecheTenenbaumMean
