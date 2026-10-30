module

public import BretecheTenenbaumMean.QuadraticLower
public import BretecheTenenbaumMean.QuadraticUpper

@[expose] public section

/-! # Theorem 1.2: both bounds for the quadratic mean -/

namespace BretecheTenenbaumMean

/-- Theorem 1.2, with absolute constants on the full printed range. -/
theorem theoremTwo : TheoremTwo := by
  obtain ⟨c, hc, hlow⟩ := theoremTwo_lower
  obtain ⟨C, hC, hupp⟩ := theoremTwo_upper
  exact ⟨c, hc, C, hC, fun x hx ↦ ⟨hlow x hx, hupp x hx⟩⟩

end BretecheTenenbaumMean
