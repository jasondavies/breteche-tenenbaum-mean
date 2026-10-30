module

public import BretecheTenenbaumMean.DistinctProductSum

@[expose] public section

/-! # Uniform comparison of powers whose positive bases differ by a bounded amount -/

namespace BretecheTenenbaumMean

open Real

/-- A bounded additive error in the base costs a bounded exponential factor
when the exponent is at most a constant times the reference base. -/
theorem pow_le_exp_mul_pow_of_sub_le {u v A H : ℝ} {k : ℕ}
    (hu : 0 < u) (hv : 0 < v) (hH : 0 ≤ H) (huv : u - v ≤ H)
    (hk : (k : ℝ) ≤ A * v) : u ^ k ≤ exp (A * H) * v ^ k := by
  have hlog : log u - log v ≤ H / v := by
    have h := log_le_sub_one_of_pos (div_pos hu hv)
    rw [log_div hu.ne' hv.ne'] at h
    have hd := div_le_div_of_nonneg_right huv hv.le
    rw [sub_div, div_self hv.ne'] at hd
    exact h.trans hd
  have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) k)
  have hkH := mul_le_mul_of_nonneg_right hk (div_nonneg hH hv.le)
  have he : A * v * (H / v) = A * H := by field_simp
  rw [he] at hkH
  have hpow : (k : ℝ) * log u ≤ A * H + (k : ℝ) * log v := by nlinarith
  calc
    _ = exp ((k : ℝ) * log u) := by rw [exp_nat_mul, exp_log hu]
    _ ≤ exp (A * H + (k : ℝ) * log v) := exp_le_exp.2 hpow
    _ = _ := by rw [exp_add, exp_nat_mul, exp_log hv]

end BretecheTenenbaumMean
