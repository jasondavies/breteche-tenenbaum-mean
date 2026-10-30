module

public import BretecheTenenbaumMean.TwoFrequencyWeight
public import BretecheTenenbaumMean.SmallPrimeFrequency

@[expose] public section

/-! # Prime-sum bounds for the three-range high-frequency majorant -/

namespace BretecheTenenbaumMean

open Real Finset
open PrimeSums

/-- Restricting an upper prime cutoff gives the smaller prime set exactly. -/
theorem filter_primesLT_of_le {a x : ℝ} (hax : a ≤ x) :
    (primesLT x).filter (fun p : ℕ ↦ (p : ℝ) < a) = primesLT a := by
  ext p
  simp only [mem_filter, mem_primesLT]
  exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.2.trans_le hax⟩, h.2⟩⟩

end BretecheTenenbaumMean
