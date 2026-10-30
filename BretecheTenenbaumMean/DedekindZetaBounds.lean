module

public import TauCeti.NumberTheory.NumberField.DedekindZeta
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-! # Uniform bounds for the regularized Dedekind zeta function

The nonvanishing continuation is obtained from the selected Tau Ceti
Dedekind-zeta theorems. Compactness then provides both sides of the
logarithmic estimate needed for reciprocal prime sums.
-/

namespace BretecheTenenbaumMean

open NumberField Complex Filter
open scoped Topology

/-- The simple pole can be removed without introducing a zero anywhere on
the closed half-plane of real part at least one. The construction follows
the regularization in Tau Ceti's logarithmic-derivative proof. -/
theorem exists_regularized_dedekindZeta (K : Type*) [Field K] [NumberField K] :
    ∃ H : ℂ → ℂ, ContinuousOn H {s | 1 ≤ s.re} ∧
      (∀ s : ℂ, 1 ≤ s.re → H s ≠ 0) ∧
      ∀ s : ℂ, 1 < s.re → H s = (s - 1) * dedekindZeta K s := by
  obtain ⟨G, hG, hGζ⟩ := TauCeti.exists_differentiableOn_eq_dedekindZeta_sub K
  let U := {s : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hsub : {s : ℂ | 1 ≤ s.re} ⊆ U :=
    TauCeti.setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K
  let H : ℂ → ℂ := fun s ↦ (s - 1) * G s + (dedekindZeta_residue K : ℂ)
  have hH : DifferentiableOn ℂ H U :=
    ((differentiableOn_id.sub_const 1).mul hG).add_const _
  have hne {s : ℂ} (hs : 1 < s.re) : s - 1 ≠ 0 :=
    sub_ne_zero.mpr (fun h ↦ by simp [h] at hs)
  have he {s : ℂ} (hs : 1 < s.re) : H s = (s - 1) * dedekindZeta K s := by
    dsimp only [H]
    rw [hGζ s hs]
    field_simp [hne hs]
    ring
  refine ⟨H, hH.continuousOn.mono hsub, ?_, fun s hs ↦ he hs⟩
  intro s hs
  rcases hs.lt_or_eq with hs | hs
  · rw [he hs]
    exact mul_ne_zero (hne hs) (TauCeti.dedekindZeta_ne_zero_of_one_lt_re hs)
  by_cases hs1 : s = 1
  · subst s
    simpa [H] using dedekindZeta_residue_ne_zero K
  have hmem : U ∈ 𝓝 s := hU.mem_nhds (hsub hs.le)
  have hζ := TauCeti.ne_zero_of_eqOn_dedekindZeta (K := K)
    (f := fun z ↦ H z / (z - 1)) hs.symm hs1
    ((hH.differentiableAt hmem).div (differentiableAt_id.sub_const 1)
      (sub_ne_zero.mpr hs1))
    (fun z hz ↦ by simp only [he hz, mul_div_cancel_left₀ _ (hne hz)])
  exact fun hz ↦ hζ (by simp [hz])

/-- Uniform upper and positive lower bounds on any bounded strip next to
the pole. The constants depend on the number field and strip height. -/
theorem regularized_dedekindZeta_norm_bounds (K : Type*) [Field K] [NumberField K]
    {R : ℝ} (hR : 0 ≤ R) : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → |s.im| ≤ R →
        c ≤ ‖(s - 1) * dedekindZeta K s‖ ∧
          ‖(s - 1) * dedekindZeta K s‖ ≤ C := by
  obtain ⟨H, hH, hH0, he⟩ := exists_regularized_dedekindZeta K
  let S : Set ℂ := {s | s.re ∈ Set.Icc 1 2 ∧ s.im ∈ Set.Icc (-R) R}
  have hc : IsCompact S := (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) 2)).reProdIm isCompact_Icc
  have hS : S.Nonempty := ⟨1, by simpa [S] using And.intro (by norm_num : (1 : ℝ) ∈ Set.Icc 1 2) (show (0 : ℝ) ∈ Set.Icc (-R) R by constructor <;> linarith)⟩
  have hcont : ContinuousOn (fun s ↦ ‖H s‖) S := hH.norm.mono (fun s hs ↦ hs.1.1)
  obtain ⟨a, ha, hmin⟩ := hc.exists_isMinOn hS hcont
  obtain ⟨b, hb, hmax⟩ := hc.exists_isMaxOn hS hcont
  have ha0 : 0 < ‖H a‖ := norm_pos_iff.2 (hH0 a ha.1.1)
  have hb0 : 0 < ‖H b‖ := norm_pos_iff.2 (hH0 b hb.1.1)
  refine ⟨‖H a‖, ‖H b‖, ha0, hb0, fun s hs hs2 him ↦ ?_⟩
  have hsS : s ∈ S := ⟨⟨hs.le, hs2⟩, abs_le.1 him⟩
  rw [← he s hs]
  exact ⟨hmin hsS, hmax hsS⟩

/-- A uniform logarithmic estimate, with the pole retained exactly. -/
theorem dedekindZeta_log_norm_bound (K : Type*) [Field K] [NumberField K]
    {R : ℝ} (hR : 0 ≤ R) : ∃ B ≥ (0 : ℝ), ∀ s : ℂ,
      1 < s.re → s.re ≤ 2 → |s.im| ≤ R →
      |Real.log ‖dedekindZeta K s‖ + Real.log ‖s - 1‖| ≤ B := by
  obtain ⟨c, C, hc, hC, hb⟩ := regularized_dedekindZeta_norm_bounds K hR
  refine ⟨|Real.log c| + |Real.log C|, by positivity, fun s hs hs2 him ↦ ?_⟩
  obtain ⟨hl, hu⟩ := hb s hs hs2 him
  have hn : 0 < ‖(s - 1) * dedekindZeta K s‖ := hc.trans_le hl
  have hlogl := Real.log_le_log hc hl
  have hlogu := Real.log_le_log hn hu
  have hab : |Real.log ‖(s - 1) * dedekindZeta K s‖| ≤ |Real.log c| + |Real.log C| := by
    apply abs_le.2
    constructor <;> linarith [neg_abs_le (Real.log c), le_abs_self (Real.log C),
      abs_nonneg (Real.log c), abs_nonneg (Real.log C)]
  have hs0 : s - 1 ≠ 0 := sub_ne_zero.mpr (fun h ↦ by simp [h] at hs)
  have hz0 := TauCeti.dedekindZeta_ne_zero_of_one_lt_re (K := K) hs
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.2 hs0) (norm_ne_zero_iff.2 hz0)] at hab
  simpa only [add_comm] using hab

end BretecheTenenbaumMean
