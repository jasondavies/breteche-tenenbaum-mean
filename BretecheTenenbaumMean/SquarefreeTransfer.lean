module

public import BretecheTenenbaumMean.SquareDivisorSum

@[expose] public section

/-! # Transferring the harmonic mean to the squarefree probability model -/

namespace BretecheTenenbaumMean

open Finset Real

/-- Extract a square factor for a nonnegative function with a bounded
square-factor weight. The larger prime cutoff handles strict endpoints. -/
theorem harmonic_squareFactor_bound_cutoff (f w : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (hw : ∀ n, 0 ≤ w n) (hmul : ∀ b a, b ≠ 0 → Squarefree a → f (b ^ 2 * a) ≤ w b * f a)
    {C : ℝ} (hsum : ∀ N : ℕ, (∑ b ∈ Ioc 0 N, w b / (b : ℝ) ^ 2) ≤ C)
    {x z : ℝ} (hz : (⌊x⌋₊ : ℝ) < z) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, f n / n) ≤
      (∑ a ∈ smoothSupport z, f a / a) * C := by
  classical
  choose b a hprod hsf using (fun n : ℕ ↦ exists_sq_mul_squarefree n)
  let e : ℕ → ℕ × ℕ := fun n ↦ (a n, b n)
  have hbounds (n : ℕ) (hn : n ∈ Ioc 0 ⌊x⌋₊) :
      a n ∈ smoothSupport z ∧ b n ∈ Ioc 0 ⌊x⌋₊ := by
    have hn' := mem_Ioc.1 hn
    have ha : a n ≤ n := Nat.le_of_dvd hn'.1 ⟨b n ^ 2, by rw [mul_comm]; exact (hprod n).symm⟩
    have hb : b n ^ 2 ≤ n := Nat.le_of_dvd hn'.1 ⟨a n, (hprod n).symm⟩
    have hb0 : 0 < b n := by
      by_contra h
      have hz : b n = 0 := by omega
      have hp := hprod n
      simp only [hz, zero_pow (by omega : 2 ≠ 0), zero_mul] at hp
      omega
    have hb' : b n ≤ n := (Nat.le_pow (by norm_num : 0 < 2)).trans hb
    refine ⟨mem_smoothSupport.2 ⟨hsf n, ?_⟩, mem_Ioc.2 ⟨hb0, hb'.trans hn'.2⟩⟩
    intro p hp
    have hp' : p ≤ ⌊x⌋₊ := (Nat.le_of_mem_primeFactors hp).trans (ha.trans hn'.2)
    exact (Nat.cast_le.2 hp').trans_lt hz
  have hinj : Set.InjOn e (↑(Ioc 0 ⌊x⌋₊) : Set ℕ) := by
    intro n _ m _ h
    have ha : a n = a m := congrArg Prod.fst h
    have hb : b n = b m := congrArg Prod.snd h
    rw [← hprod n, ← hprod m, ha, hb]
  have hsub : (Ioc 0 ⌊x⌋₊).image e ⊆ smoothSupport z ×ˢ Ioc 0 ⌊x⌋₊ := by
    intro d hd
    obtain ⟨n, hn, rfl⟩ := mem_image.1 hd
    exact mem_product.2 (hbounds n hn)
  calc
    _ ≤ ∑ d ∈ smoothSupport z ×ˢ Ioc 0 ⌊x⌋₊,
        (f d.1 / d.1) * (w d.2 / (d.2 : ℝ) ^ 2) := by
      apply sum_le_sum_of_injOn e hinj hsub
      · intro n hn
        have h := hmul (b n) (a n)
          (ne_of_gt (mem_Ioc.1 (hbounds n hn).2).1) (hsf n)
        rw [hprod n] at h
        calc
          _ ≤ (w (b n) * f (a n)) / n :=
            div_le_div_of_nonneg_right h (Nat.cast_nonneg _)
          _ = _ := by
            dsimp [e]
            conv_lhs => arg 2; rw [← hprod n, Nat.cast_mul, Nat.cast_pow]
            simp only [div_eq_mul_inv, mul_inv_rev]
            ring
      · intro d _ _
        exact mul_nonneg (div_nonneg (hf _) (Nat.cast_nonneg _))
          (div_nonneg (hw _) (sq_nonneg _))
    _ = (∑ a ∈ smoothSupport z, f a / a) *
        ∑ b ∈ Ioc 0 ⌊x⌋₊, w b / (b : ℝ) ^ 2 := by rw [sum_product, sum_mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hsum _) (sum_nonneg (fun n _ ↦ div_nonneg (hf n) (Nat.cast_nonneg _)))

/-- The convenient doubled-cutoff version of the squarefree transfer. -/
theorem harmonic_squareFactor_bound_of_squarefree (f w : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (hw : ∀ n, 0 ≤ w n)
    (hmul : ∀ b a, b ≠ 0 → Squarefree a → f (b ^ 2 * a) ≤ w b * f a)
    {C : ℝ} (hsum : ∀ N : ℕ, (∑ b ∈ Ioc 0 N, w b / (b : ℝ) ^ 2) ≤ C)
    {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, f n / n) ≤
      (∑ a ∈ smoothSupport (2 * x), f a / a) * C :=
  harmonic_squareFactor_bound_cutoff f w hf hw hmul hsum
    ((Nat.floor_le (by linarith : 0 ≤ x)).trans_lt (by linarith))

/-- A version with a square-factor estimate valid on all integers. -/
theorem harmonic_squareFactor_bound (f w : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (hw : ∀ n, 0 ≤ w n) (hmul : ∀ b a, f (b ^ 2 * a) ≤ w b * f a)
    {C : ℝ} (hsum : ∀ N : ℕ, (∑ b ∈ Ioc 0 N, w b / (b : ℝ) ^ 2) ≤ C)
    {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, f n / n) ≤
      (∑ a ∈ smoothSupport (2 * x), f a / a) * C :=
  harmonic_squareFactor_bound_of_squarefree f w hf hw (fun b a _ _ ↦ hmul b a) hsum hx

/-- The harmonic first mean is controlled by the squarefree model. -/
theorem harmonic_delta_le_squarefree {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, (hooleyDelta n : ℝ) / n) ≤
      (∑ a ∈ smoothSupport (2 * x), (hooleyDelta a : ℝ) / a) * (π ^ 2 / 6) ^ 3 :=
  harmonic_squareFactor_bound (fun n ↦ (hooleyDelta n : ℝ)) (fun b ↦ tau (b ^ 2))
    (fun _ ↦ Nat.cast_nonneg _) (fun _ ↦ Nat.cast_nonneg _)
    (fun b a ↦ hooleyDelta_mul_le_tau (b ^ 2) a) sum_tau_square_div_sq_le hx

/-- The complete comparison between the ordinary harmonic sum and the finite model. -/
theorem harmonic_delta_le_expectation {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, (hooleyDelta n : ℝ) / n) ≤
      (π ^ 2 / 6) ^ 3 * normalizer (2 * x) *
        expectation (2 * x) (fun n ↦ (hooleyDelta n : ℝ)) := by
  have h := harmonic_delta_le_squarefree hx
  convert h using 1
  unfold expectation
  field_simp [(normalizer_pos (2 * x)).ne']

end BretecheTenenbaumMean
