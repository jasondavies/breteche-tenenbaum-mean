module

public import BretecheTenenbaumMean.PrimeRecursion
public import BretecheTenenbaumMean.MomentConvexity

@[expose] public section

/-! # Monotonicity and local integrability of smooth-support sums -/

namespace BretecheTenenbaumMean

open Finset MeasureTheory

theorem smoothSupport_mono : Monotone smoothSupport := by
  intro x y hxy n hn
  obtain ⟨hsq, hp⟩ := mem_smoothSupport.1 hn
  exact mem_smoothSupport.2 ⟨hsq, fun p hpn ↦ (hp p hpn).trans_le hxy⟩

theorem sum_smoothSupport_mono {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    Monotone (fun y ↦ ∑ n ∈ smoothSupport y, f n) := by
  intro x y hxy
  exact sum_le_sum_of_subset_of_nonneg (smoothSupport_mono hxy) (fun n _ _ ↦ hf n)

end BretecheTenenbaumMean
