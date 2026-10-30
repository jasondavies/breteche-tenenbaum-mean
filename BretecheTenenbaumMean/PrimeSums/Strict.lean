module

public import BretecheTenenbaumMean.PrimeSums.Mertens

@[expose] public section

/-! # Strict prime cutoffs

The probability model uses `p < x`, whereas the Abel summation formula uses `p ≤ x`.
The endpoint discrepancy is at most `1/x`, including at prime integer cutoffs.
-/

open Real Finset

namespace BretecheTenenbaumMean.PrimeSums

noncomputable def SLT (x : ℝ) : ℝ := ∑ p ∈ primesLT x, (p : ℝ)⁻¹

theorem primesLT_mono {x y : ℝ} (hxy : x ≤ y) : primesLT x ⊆ primesLT y := by
  intro p hp
  rw [mem_primesLT] at hp ⊢
  exact ⟨hp.1, hp.2.trans_le hxy⟩

theorem mem_primesLT_floor_add_one {p : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    p ∈ primesLT ((⌊x⌋₊ : ℝ) + 1) ↔ p.Prime ∧ (p : ℝ) ≤ x := by
  rw [mem_primesLT]
  have h : (p : ℝ) < (⌊x⌋₊ : ℝ) + 1 ↔ p ≤ ⌊x⌋₊ := by
    exact_mod_cast Nat.lt_succ_iff
  rw [h, Nat.le_floor_iff hx]

/-- Exact endpoint control between weak and strict cutoffs. -/
theorem S_sub_SLT {x : ℝ} (hx : 0 < x) :
    0 ≤ S x - SLT x ∧ S x - SLT x ≤ x⁻¹ := by
  have hsub := primesLT_mono (show x ≤ (⌊x⌋₊ : ℝ) + 1 from (Nat.lt_floor_add_one x).le)
  rw [S, SLT, ← sum_sdiff hsub, add_sub_cancel_right]
  refine ⟨sum_nonneg fun p _ ↦ by positivity, ?_⟩
  have hmem : ∀ p ∈ primesLT ((⌊x⌋₊ : ℝ) + 1) \ primesLT x, (p : ℝ) = x := by
    intro p hp
    rw [mem_sdiff, mem_primesLT_floor_add_one hx.le, mem_primesLT] at hp
    exact le_antisymm hp.1.2 (not_lt.1 fun h ↦ hp.2 ⟨hp.1.1, h⟩)
  have hcard : (primesLT ((⌊x⌋₊ : ℝ) + 1) \ primesLT x).card ≤ 1 := by
    apply card_le_one.2
    intro a ha b hb
    exact_mod_cast (hmem a ha).trans (hmem b hb).symm
  calc ∑ p ∈ primesLT ((⌊x⌋₊ : ℝ) + 1) \ primesLT x, (p : ℝ)⁻¹
      = ∑ p ∈ primesLT ((⌊x⌋₊ : ℝ) + 1) \ primesLT x, x⁻¹ :=
        sum_congr rfl fun p hp ↦ by rw [hmem p hp]
    _ = (primesLT ((⌊x⌋₊ : ℝ) + 1) \ primesLT x).card * x⁻¹ := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ 1 * x⁻¹ := by gcongr; exact_mod_cast hcard
    _ = x⁻¹ := one_mul _

/-- Mertens' second theorem in the strict-cutoff convention. -/
theorem SLT_asymp : ∃ c C : ℝ, 0 ≤ C ∧
    ∀ x ≥ 2, |SLT x - log (log x) - c| ≤ C * pntE x := by
  obtain ⟨c, C, hC⟩ := S_asymp
  have hC0 : 0 ≤ C :=
    nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hC 2 le_rfl)) (pntE_pos 2)
  refine ⟨c, C + 1, by positivity, fun x hx ↦ ?_⟩
  have he := S_sub_SLT (x := x) (by linarith)
  have hi := inv_le_pntE hx
  have h := hC x hx
  rw [abs_le] at h ⊢
  constructor <;> nlinarith

/-- A uniform bounded remainder, sufficient for Mertens product comparisons. -/
theorem abs_SLT_sub_loglog_le : ∃ C ≥ 0, ∀ x ≥ 2, |SLT x - log (log x)| ≤ C := by
  obtain ⟨c, C, hC0, hC⟩ := SLT_asymp
  refine ⟨C + |c|, by positivity, fun x hx ↦ ?_⟩
  calc |SLT x - log (log x)| ≤ |SLT x - log (log x) - c| + |c| := by
          simpa using abs_add_le (SLT x - log (log x) - c) c
    _ ≤ C * pntE x + |c| := by linarith [hC x hx]
    _ ≤ C + |c| := by nlinarith [pntE_le_one x]

end BretecheTenenbaumMean.PrimeSums
