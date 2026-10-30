module

public import BretecheTenenbaumMean.PrimeMarginal

@[expose] public section

/-! # Nonnegative multiplicative weights in the finite probability model

The weighted extension used for polynomial values has local prime weights
`ρ_F(p)/p`. The definitions below keep the exact normalizer rather than
assuming any prime mean estimate.
-/

namespace BretecheTenenbaumMean

open Finset Real

/-- The algebraic assumptions on a weight. No analytic mean bound is part of
this structure. Its value at zero is irrelevant on the squarefree support. -/
structure MultiplicativeWeight where
  toFun : ℕ → ℝ
  nonneg : ∀ n, 0 ≤ toFun n
  map_one : toFun 1 = 1
  map_mul : ∀ m n, m.Coprime n → toFun (m * n) = toFun m * toFun n

instance : CoeFun MultiplicativeWeight (fun _ ↦ ℕ → ℝ) := ⟨MultiplicativeWeight.toFun⟩

namespace WeightedModel

noncomputable def normalizer (w : MultiplicativeWeight) (x : ℝ) : ℝ :=
  ∏ p ∈ primesLT x, (1 + w p / p)

noncomputable def expectation (w : MultiplicativeWeight) (x : ℝ) (f : ℕ → ℝ) : ℝ :=
  (∑ n ∈ smoothSupport x, w n * f n / n) / normalizer w x

noncomputable def probability (w : MultiplicativeWeight) (x : ℝ) (E : Set ℕ) : ℝ :=
  expectation w x (E.indicator (fun _ ↦ 1))

theorem normalizer_pos (w : MultiplicativeWeight) (x : ℝ) : 0 < normalizer w x := by
  apply prod_pos
  intro p _
  have hw := w.nonneg p
  positivity

/-- The weighted squarefree sum is exactly a sum over independent prime subsets. -/
theorem sum_eq_powerset (w : MultiplicativeWeight) (x : ℝ) (f : ℕ → ℝ) :
    (∑ n ∈ smoothSupport x, w n * f n / n) =
      ∑ s ∈ (primesLT x).powerset, f (∏ p ∈ s, p) * ∏ p ∈ s, (w p / p) := by
  rw [sum_smoothSupport_eq_powerset]
  apply sum_congr rfl
  intro s hs
  have hprime : ∀ p ∈ s, p.Prime := fun p hp ↦
    (mem_primesLT.1 (mem_powerset.1 hs hp)).1
  rw [map_prod_primes w w.map_one w.map_mul s hprime, Nat.cast_prod, prod_div_distrib]
  ring

theorem sum_weight (w : MultiplicativeWeight) (x : ℝ) :
    (∑ n ∈ smoothSupport x, w n / n) = normalizer w x := by
  have h := sum_eq_powerset w x (fun _ ↦ 1)
  simpa only [mul_one, one_mul, ← prod_one_add, normalizer] using h

@[simp] theorem expectation_one (w : MultiplicativeWeight) (x : ℝ) :
    expectation w x (fun _ ↦ 1) = 1 := by
  simp only [expectation, mul_one, sum_weight, div_self (normalizer_pos w x).ne']

theorem expectation_nonneg (w : MultiplicativeWeight) (x : ℝ) {f : ℕ → ℝ}
    (hf : ∀ n ∈ smoothSupport x, 0 ≤ f n) : 0 ≤ expectation w x f := by
  apply div_nonneg _ (normalizer_pos w x).le
  exact sum_nonneg (fun n hn ↦ div_nonneg (mul_nonneg (w.nonneg n) (hf n hn)) (Nat.cast_nonneg _))

theorem expectation_mono (w : MultiplicativeWeight) (x : ℝ) {f g : ℕ → ℝ}
    (hfg : ∀ n ∈ smoothSupport x, f n ≤ g n) : expectation w x f ≤ expectation w x g := by
  apply div_le_div_of_nonneg_right _ (normalizer_pos w x).le
  apply sum_le_sum
  intro n hn
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hfg n hn) (w.nonneg n)) (Nat.cast_nonneg _)

theorem expectation_add (w : MultiplicativeWeight) (x : ℝ) (f g : ℕ → ℝ) :
    expectation w x (fun n ↦ f n + g n) = expectation w x f + expectation w x g := by
  simp only [expectation, mul_add, add_div, sum_add_distrib]

theorem expectation_const_mul (w : MultiplicativeWeight) (x c : ℝ) (f : ℕ → ℝ) :
    expectation w x (fun n ↦ c * f n) = c * expectation w x f := by
  unfold expectation
  rw [← mul_div_assoc]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro n _
  ring

theorem expectation_multiplicative (w : MultiplicativeWeight) (x : ℝ) (f : ℕ → ℝ)
    (hf1 : f 1 = 1) (hfm : ∀ m n, m.Coprime n → f (m * n) = f m * f n) :
    expectation w x f = (∏ p ∈ primesLT x, (1 + w p * f p / p)) / normalizer w x := by
  unfold expectation
  congr 1
  rw [sum_eq_powerset, prod_one_add]
  apply sum_congr rfl
  intro s hs
  have hprime : ∀ p ∈ s, p.Prime := fun p hp ↦
    (mem_primesLT.1 (mem_powerset.1 hs hp)).1
  rw [map_prod_primes f hf1 hfm s hprime, ← prod_mul_distrib]
  apply prod_congr rfl
  intro p _
  ring

/-- The divisor-count moment retains the exact weighted local factor. -/
theorem expectation_tau_pow (w : MultiplicativeWeight) (x : ℝ) (k : ℕ) :
    expectation w x (fun n ↦ tau n ^ k) =
      (∏ p ∈ primesLT x, (1 + w p * (2 : ℝ) ^ k / p)) / normalizer w x := by
  rw [expectation_multiplicative w x _ (by simp) (fun m n h ↦ by rw [tau_mul_of_coprime h, mul_pow])]
  congr 1
  apply prod_congr rfl
  intro p hp
  rw [tau_prime (mem_primesLT.1 hp).1]

theorem probability_nonneg (w : MultiplicativeWeight) (x : ℝ) (E : Set ℕ) :
    0 ≤ probability w x E :=
  expectation_nonneg w x (fun n _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) n)

theorem probability_gt_le (w : MultiplicativeWeight) (x : ℝ) (f : ℕ → ℝ)
    (hf : ∀ n ∈ smoothSupport x, 0 ≤ f n) {T : ℝ} (hT : 0 < T) :
    probability w x {n | T < f n} ≤ expectation w x f / T := by
  classical
  rw [le_div_iff₀ hT, mul_comm, probability, ← expectation_const_mul]
  apply expectation_mono
  intro n hn
  by_cases he : T < f n
  · simp only [Set.indicator, Set.mem_ofPred_eq, ite_eq_left he, mul_one]
    exact he.le
  · simp only [Set.indicator, Set.mem_ofPred_eq, ite_eq_right he, mul_zero]
    exact hf n hn

/-- Constant unit weight recovers the unweighted model exactly. -/
def unitWeight : MultiplicativeWeight where
  toFun := fun _ ↦ 1
  nonneg := fun _ ↦ zero_le_one
  map_one := rfl
  map_mul := fun _ _ _ ↦ by norm_num

@[simp] theorem normalizer_unit (x : ℝ) : normalizer unitWeight x = BretecheTenenbaumMean.normalizer x := by
  simp only [normalizer, BretecheTenenbaumMean.normalizer, unitWeight, one_div]

@[simp] theorem expectation_unit (x : ℝ) (f : ℕ → ℝ) :
    expectation unitWeight x f = BretecheTenenbaumMean.expectation x f := by
  unfold expectation
  rw [normalizer_unit]
  simp only [unitWeight, one_mul, BretecheTenenbaumMean.expectation]

end WeightedModel

end BretecheTenenbaumMean
