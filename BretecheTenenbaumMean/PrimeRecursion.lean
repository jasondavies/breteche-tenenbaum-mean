module

public import BretecheTenenbaumMean.OrderedRecursion
public import BretecheTenenbaumMean.PrimeSums.Product

@[expose] public section

/-! # Iterated largest-prime recursion for the truncated moments -/

namespace BretecheTenenbaumMean

open Finset Real

/-- Restricting a prime cutoff further to integers below `p`. -/
theorem primesLT_filter_lt {x : ℝ} {p : ℕ} (hp : (p : ℝ) ≤ x) :
    (primesLT x).filter (fun r ↦ r < p) = primesLT p := by
  ext r
  simp only [mem_filter, mem_primesLT]
  constructor
  · rintro ⟨⟨hr, _⟩, hrp⟩
    exact ⟨hr, by exact_mod_cast hrp⟩
  · rintro ⟨hr, hrp⟩
    exact ⟨⟨hr, hrp.trans_le hp⟩, by exact_mod_cast hrp⟩

end BretecheTenenbaumMean
