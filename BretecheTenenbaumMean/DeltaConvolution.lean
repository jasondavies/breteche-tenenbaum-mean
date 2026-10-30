module

public import BretecheTenenbaumMean.DeltaSubmultiplicative

@[expose] public section

/-! # Real-space convolution of divisor windows -/

namespace BretecheTenenbaumMean

open Real MeasureTheory Set Finset

/-- Reflection reverses the half-open endpoint convention only on a null set. -/
lemma windowIndicator_reflect_ae (a c : ℝ) :
    (fun u ↦ windowIndicator a (c - u)) =ᵐ[volume] windowIndicator (c - a + 1) := by
  have h : (fun u ↦ windowIndicator a (c - u)) =
      (Ioc (c - a) (c - a + 1)).indicator (fun _ : ℝ ↦ (1 : ℝ)) := by
    funext u
    have hm : c - u ∈ Ico (a - 1) a ↔ u ∈ Ioc (c - a) (c - a + 1) := by
      simp only [Set.mem_Ico, Set.mem_Ioc]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    simp only [windowIndicator, indicator_apply, hm]
  rw [h]
  have he : c - a + 1 - 1 = c - a := by ring
  unfold windowIndicator
  rw [he]
  exact indicator_ae_eq_of_ae_eq_set Ico_ae_eq_Ioc.symm

lemma integrable_windowIndicator_convolution (a b c : ℝ) :
    Integrable (fun u ↦ windowIndicator a u * windowIndicator b (c - u)) := by
  apply (integrable_windowIndicator_mul a (c - b + 1)).congr
  filter_upwards [windowIndicator_reflect_ae b c] with u hu
  rw [hu]

lemma integral_windowIndicator_convolution (a b c : ℝ) :
    (∫ u, windowIndicator a u * windowIndicator b (c - u)) =
      max (1 - |a + b - c - 1|) 0 := by
  calc
    _ = ∫ u, windowIndicator a u * windowIndicator (c - b + 1) u := by
      apply integral_congr_ae
      filter_upwards [windowIndicator_reflect_ae b c] with u hu
      rw [hu]
    _ = max (1 - |a - (c - b + 1)|) 0 := integral_windowIndicator_mul _ _
    _ = _ := by congr 3; ring

noncomputable def deltaConvolution (m n : ℕ) (c : ℝ) : ℝ :=
  ∫ u, delta m u * delta n (c - u)

lemma deltaConvolution_nonneg (m n : ℕ) (c : ℝ) : 0 ≤ deltaConvolution m n c :=
  integral_nonneg (fun u ↦ mul_nonneg (delta_nonneg m u) (delta_nonneg n (c - u)))

lemma delta_product_eq_sum (m n : ℕ) (c u : ℝ) :
    delta m u * delta n (c - u) = ∑ a ∈ m.divisors, ∑ b ∈ n.divisors,
      windowIndicator (log a) u * windowIndicator (log b) (c - u) := by
  simp only [delta_eq_sum_indicator, windowIndicator, sum_mul_sum]

lemma integrable_delta_convolution (m n : ℕ) (c : ℝ) :
    Integrable (fun u ↦ delta m u * delta n (c - u)) := by
  simp_rw [delta_product_eq_sum]
  exact integrable_finsetSum _ (fun a _ ↦ integrable_finsetSum _
    (fun b _ ↦ integrable_windowIndicator_convolution (log (a : ℕ)) (log (b : ℕ)) c))

/-- The tent kernel arises from overlap lengths, with no Fourier theorem required. -/
theorem deltaConvolution_eq_sum (m n : ℕ) (c : ℝ) :
    deltaConvolution m n c = ∑ a ∈ m.divisors, ∑ b ∈ n.divisors,
      max (1 - |log a + log b - c - 1|) 0 := by
  unfold deltaConvolution
  simp_rw [delta_product_eq_sum]
  rw [integral_finsetSum _ (fun a _ ↦ integrable_finsetSum _
    (fun b _ ↦ integrable_windowIndicator_convolution (log (a : ℕ)) (log (b : ℕ)) c))]
  apply sum_congr rfl
  intro a _
  rw [integral_finsetSum _ (fun b _ ↦ integrable_windowIndicator_convolution (log (a : ℕ)) (log (b : ℕ)) c)]
  simp_rw [integral_windowIndicator_convolution]

/-- A unit-width divisor window is bounded by twice the centered tent sum. -/
theorem delta_mul_le_convolution (m n : ℕ) (u : ℝ) :
    delta (m * n) u ≤ 2 * deltaConvolution m n (u - 1 / 2) := by
  classical
  have h : delta (m * n) u ≤ ∑ a ∈ m.divisors, delta n (u - log a) := by
    unfold delta
    exact_mod_cast divisorWindow_mul_le_sum m n u
  apply h.trans
  rw [deltaConvolution_eq_sum, mul_sum]
  apply sum_le_sum
  intro a _
  rw [delta, divisorWindow_eq_sum, Nat.cast_sum, mul_sum]
  apply sum_le_sum
  intro b _
  split_ifs with hmem
  · norm_num only [Nat.cast_one]
    have hab : |log a + log b - (u - 1 / 2) - 1| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith [hmem.1, hmem.2]
    have hm := le_max_left (1 - |log a + log b - (u - 1 / 2) - 1|) (0 : ℝ)
    linarith
  · norm_num only [Nat.cast_zero]
    positivity

/-- Cauchy–Schwarz for the convolution, with the reflected second norm unchanged. -/
theorem deltaConvolution_sq_le (m n : ℕ) (c : ℝ) :
    deltaConvolution m n c ^ 2 ≤ moment 2 m * moment 2 n := by
  have hf := (memLp_two_iff_integrable_sq (measurable_delta m).aestronglyMeasurable).2
    (integrable_delta_pow m 2 (by omega))
  have hg := (memLp_two_iff_integrable_sq
    ((measurable_delta n).comp (measurable_const.sub measurable_id)).aestronglyMeasurable).2
    ((integrable_delta_pow n 2 (by omega)).comp_sub_left c)
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 by constructor <;> norm_num)
    (Filter.Eventually.of_forall (delta_nonneg m))
    (Filter.Eventually.of_forall (fun u ↦ delta_nonneg n (c - u)))
    (by simpa using hf) (by simpa only [ENNReal.ofReal_ofNat, Function.comp_def, Pi.sub_apply, id_eq] using hg)
  simp only [rpow_two] at h
  rw [integral_sub_left_eq_self (fun u ↦ delta n u ^ 2) volume c] at h
  change deltaConvolution m n c ≤ (moment 2 m) ^ (1 / 2 : ℝ) * (moment 2 n) ^ (1 / 2 : ℝ) at h
  rw [← sqrt_eq_rpow, ← sqrt_eq_rpow] at h
  have hh := mul_self_le_mul_self (deltaConvolution_nonneg m n c) h
  simpa only [← pow_two, mul_pow, sq_sqrt (moment_nonneg 2 m), sq_sqrt (moment_nonneg 2 n)] using hh

/-- The product-moment inequality in §4, valid without coprimality. -/
theorem hooleyDelta_mul_sq_le_moments (m n : ℕ) :
    (hooleyDelta (m * n) : ℝ) ^ 2 ≤ 4 * moment 2 m * moment 2 n := by
  obtain ⟨u, hu⟩ := hooleyDelta_attained (m * n)
  have hd : delta (m * n) u = (hooleyDelta (m * n) : ℝ) := congrArg Nat.cast hu
  have h := delta_mul_le_convolution m n u
  rw [hd] at h
  have hh := mul_self_le_mul_self (Nat.cast_nonneg (α := ℝ) (hooleyDelta (m * n))) h
  have hc := deltaConvolution_sq_le m n (u - 1 / 2)
  nlinarith

end BretecheTenenbaumMean
