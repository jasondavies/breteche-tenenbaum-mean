module

public import BretecheTenenbaumMean.PrimeSums.Tilted
public import BretecheTenenbaumMean.PrimeCoefficientBounds
public import BretecheTenenbaumMean.PrimeMarginal

@[expose] public section

/-! # Tilted moments and size exceptions on fixed prime-count layers -/

namespace BretecheTenenbaumMean

open Finset Real

/-- A multiplicative weight on a fixed prime-count layer is exactly one
weighted elementary-symmetric coefficient. -/
theorem expectation_prime_layer_multiplicative (y : ℝ) (k : ℕ) (f : ℕ → ℝ)
    (hf1 : f 1 = 1) (hfm : ∀ m n, m.Coprime n → f (m * n) = f m * f n) :
    expectation y ({n | n.primeFactors.card = k}.indicator f) =
      distinctProductSum (primesLT y) (fun p ↦ f p / p) k / normalizer y := by
  classical
  unfold expectation
  congr 1
  rw [sum_smoothSupport_eq_powerset, distinctProductSum, powersetCard_eq_filter, sum_filter]
  apply sum_congr rfl
  intro s hs
  have hprime : ∀ p ∈ s, p.Prime := fun p hp ↦
    (mem_primesLT.1 (mem_powerset.1 hs hp)).1
  simp only [Set.indicator, Set.mem_ofPred_eq, Nat.primeFactors_prod hprime]
  split_ifs
  · rw [map_prod_primes f hf1 hfm s hprime, Nat.cast_prod, prod_div_distrib]
  · simp

/-- The power tilt is bounded relative to the mass of the same count layer,
uniformly over all counts at most a fixed multiple of `log log y`. -/
theorem expectation_tilted_prime_layer_bound {A : ℝ} (hA : 0 < A) :
    ∃ D > 0, ∃ L₀ > 0, ∀ y : ℝ, 2 ≤ y → L₀ ≤ log (log y) →
      ∀ k : ℕ, (k : ℝ) ≤ A * log (log y) →
      expectation y ({n | n.primeFactors.card = k}.indicator
        (fun n ↦ (n : ℝ) ^ (1 / log y))) ≤
      D * probability y {n | n.primeFactors.card = k} := by
  obtain ⟨c, hc, C, hC, L₀, hL₀, hcoef⟩ := reciprocal_prime_coefficient_bounds hA
  obtain ⟨H, hH, htilt⟩ := PrimeSums.tilted_prime_sum_le
  refine ⟨exp (A * H) / c, by positivity, L₀, hL₀, fun y hy hL k hk ↦ ?_⟩
  let L := log (log y)
  let W := fun p : ℕ ↦ (p : ℝ) ^ (1 / log y) / p
  have hLpos : 0 < L := hL₀.trans_le hL
  have hW : ∀ p ∈ primesLT y, 0 ≤ W p := fun p _ ↦ by dsimp [W]; positivity
  have hS : 0 ≤ ∑ p ∈ primesLT y, W p := sum_nonneg hW
  have hpower : (L + H) ^ k ≤ exp (A * H) * L ^ k :=
    pow_le_exp_mul_pow_of_sub_le (by positivity) hLpos hH (by linarith) hk
  have hcoeff : distinctProductSum (primesLT y) W k ≤
      (exp (A * H) / c) * distinctProductSum (primesLT y) (fun p ↦ (p : ℝ)⁻¹) k := by
    calc
      _ ≤ (∑ p ∈ primesLT y, W p) ^ k / (k.factorial : ℝ) :=
        distinctProductSum_le _ _ _ hW
      _ ≤ (L + H) ^ k / (k.factorial : ℝ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact pow_le_pow_left₀ hS (htilt y hy) _
      _ ≤ (exp (A * H) * L ^ k) / (k.factorial : ℝ) :=
        div_le_div_of_nonneg_right hpower (by positivity)
      _ = (exp (A * H) / c) * (c * L ^ k / (k.factorial : ℝ)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcoef y hy hL k hk).1 (by positivity)
  rw [expectation_prime_layer_multiplicative y k _ (by simp)
    (fun m n _ ↦ by rw [Nat.cast_mul, mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]),
    probability_prime_layer_eq, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hcoeff (normalizer_pos y).le

/-- The event that a count-layer integer exceeds `y^K` loses an exponential
factor in `K`, with a constant independent of the cutoff and count. -/
theorem probability_prime_layer_size_exception {A : ℝ} (hA : 0 < A) :
    ∃ D > 0, ∃ L₀ > 0, ∀ y : ℝ, 2 ≤ y → L₀ ≤ log (log y) →
      ∀ k : ℕ, (k : ℝ) ≤ A * log (log y) → ∀ K : ℝ,
      probability y {n | n.primeFactors.card = k ∧ y ^ K < (n : ℝ)} ≤
        D * exp (-K) * probability y {n | n.primeFactors.card = k} := by
  obtain ⟨D, hD, L₀, hL₀, htilt⟩ := expectation_tilted_prime_layer_bound hA
  refine ⟨D, hD, L₀, hL₀, fun y hy hL k hk K ↦ ?_⟩
  have hy0 : 0 < y := by linarith
  have hly : 0 < log y := log_pos (by linarith)
  have hevent : {n : ℕ | n.primeFactors.card = k ∧ y ^ K < (n : ℝ)} ⊆
      {n : ℕ | n.primeFactors.card = k ∧ exp K < (n : ℝ) ^ (1 / log y)} := by
    intro n hn
    refine ⟨hn.1, ?_⟩
    have h := rpow_lt_rpow (rpow_nonneg hy0.le K) hn.2 (by positivity : 0 < 1 / log y)
    have hid : (y ^ K) ^ (1 / log y) = exp K := by
      rw [← rpow_mul hy0.le, rpow_def_of_pos hy0]
      congr 1
      field_simp
    rwa [hid] at h
  calc
    _ ≤ probability y {n | n.primeFactors.card = k ∧ exp K < (n : ℝ) ^ (1 / log y)} :=
      probability_mono y hevent
    _ ≤ expectation y ({n | n.primeFactors.card = k}.indicator
          (fun n ↦ (n : ℝ) ^ (1 / log y))) / exp K :=
      probability_inter_gt_le y _ _ (fun _ _ ↦ by positivity) (exp_pos K)
    _ ≤ (D * probability y {n | n.primeFactors.card = k}) / exp K :=
      div_le_div_of_nonneg_right (htilt y hy hL k hk) (exp_pos K).le
    _ = _ := by rw [exp_neg]; ring

/-- The same size exception can be estimated in a larger ambient model. -/
theorem probability_smallPrime_size_exception {A : ℝ} (hA : 0 < A) :
    ∃ D > 0, ∃ L₀ > 0, ∀ x y : ℝ, y ≤ x → 2 ≤ y → L₀ ≤ log (log y) →
      ∀ k : ℕ, (k : ℝ) ≤ A * log (log y) → ∀ K : ℝ,
      probability x {n | (smallPrimePart n y).primeFactors.card = k ∧
        y ^ K < (smallPrimePart n y : ℝ)} ≤
        D * exp (-K) * probability y {n | n.primeFactors.card = k} := by
  obtain ⟨D, hD, L₀, hL₀, hbad⟩ := probability_prime_layer_size_exception hA
  refine ⟨D, hD, L₀, hL₀, fun x y hyx hy hL k hk K ↦ ?_⟩
  have he := probability_smallPrimePart hyx
    {n | n.primeFactors.card = k ∧ y ^ K < (n : ℝ)}
  change probability x {n | (smallPrimePart n y).primeFactors.card = k ∧
    y ^ K < (smallPrimePart n y : ℝ)} = _ at he
  rw [he]
  exact hbad y hy hL k hk K

end BretecheTenenbaumMean
