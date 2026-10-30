module

public import BretecheTenenbaumMean.SmoothSums
public import BretecheTenenbaumMean.RangeCheck

@[expose] public section

/-! # Endpoint bounds for the moment induction -/

namespace BretecheTenenbaumMean

open Finset Real

theorem primesLT_eq_empty_of_le_two {x : ℝ} (hx : x ≤ 2) : primesLT x = ∅ := by
  apply eq_empty_iff_forall_notMem.2
  intro p hp
  obtain ⟨hp, hpx⟩ := mem_primesLT.1 hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  linarith

end BretecheTenenbaumMean
