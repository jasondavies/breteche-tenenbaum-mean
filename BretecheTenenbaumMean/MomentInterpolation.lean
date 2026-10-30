module

public import BretecheTenenbaumMean.MomentConvexity
public import BretecheTenenbaumMean.MomentRecurrence

@[expose] public section

/-! # The full moment interpolation inequality from the introduction -/

namespace BretecheTenenbaumMean

open Real MeasureTheory

/-- Weighted arithmetic-geometric mean, integrated after normalization, gives
the Hölder interpolation inequality displayed after (1.5). -/
theorem moment_interpolation {n q j : ℕ} (hn : n ≠ 0) (hq : 2 ≤ q)
    (hj : 1 ≤ j) (hjq : j ≤ q - 1) :
    moment j n ≤ moment q n ^ (((j : ℝ) - 1) / ((q : ℝ) - 1)) *
      tau n ^ (((q : ℝ) - j) / ((q : ℝ) - 1)) := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjq' : (j : ℝ) < q := by exact_mod_cast (show j < q by omega)
  have hden : 0 < (q : ℝ) - 1 := by linarith
  have hM : 0 < moment q n := moment_pos hn (by omega)
  have ht : 0 < tau n := tau_pos hn
  by_cases hj1 : j = 1
  · subst j
    simp only [Nat.cast_one, sub_self, zero_div, rpow_zero, one_mul, div_self hden.ne', rpow_one, moment_one, le_refl]
  have hj2 : (1 : ℝ) < j := by exact_mod_cast (show 1 < j by omega)
  let a := ((j : ℝ) - 1) / ((q : ℝ) - 1)
  let b := ((q : ℝ) - j) / ((q : ℝ) - 1)
  have ha : 0 < a := div_pos (by linarith) hden
  have hb : 0 < b := div_pos (by linarith) hden
  have hab : a + b = 1 := by dsimp [a, b]; field_simp; ring
  have hpow : (q : ℝ) * a + b = j := by dsimp [a, b]; field_simp; ring
  let C := moment q n ^ a * tau n ^ b
  have hC : 0 < C := mul_pos (rpow_pos_of_pos hM _) (rpow_pos_of_pos ht _)
  have hpoint (u : ℝ) : delta n u ^ j ≤
      C * (a * (delta n u ^ q / moment q n) + b * (delta n u / tau n)) := by
    have hd := delta_nonneg n u
    have h := geom_mean_le_arith_mean2_weighted ha.le hb.le
      (div_nonneg (pow_nonneg hd q) hM.le) (div_nonneg hd ht.le) hab
    have hm := mul_le_mul_of_nonneg_left h hC.le
    have he : C * ((delta n u ^ q / moment q n) ^ a * (delta n u / tau n) ^ b) = delta n u ^ j := by
      by_cases hz : delta n u = 0
      · simp [hz, Nat.ne_zero_of_lt (show 0 < q by omega), Nat.ne_zero_of_lt hj, ha.ne', hb.ne']
      have hdpos : 0 < delta n u := lt_of_le_of_ne hd (Ne.symm hz)
      rw [div_rpow (pow_nonneg hd _) hM.le, div_rpow hd ht.le]
      have hMa : moment q n ^ a ≠ 0 := (rpow_pos_of_pos hM a).ne'
      have htb : tau n ^ b ≠ 0 := (rpow_pos_of_pos ht b).ne'
      calc
        _ = (delta n u ^ q) ^ a * delta n u ^ b := by dsimp [C]; field_simp
        _ = delta n u ^ ((q : ℝ) * a + b) := by
          rw [rpow_add hdpos, rpow_mul hd, rpow_natCast]
        _ = _ := by rw [hpow, rpow_natCast]
    rwa [he] at hm
  have hiA := ((integrable_delta_pow n q (by omega)).div_const (moment q n)).const_mul a
  have hiB := ((integrable_delta n).div_const (tau n)).const_mul b
  calc
    moment j n ≤ ∫ u, C * (a * (delta n u ^ q / moment q n) + b * (delta n u / tau n)) :=
      integral_mono (integrable_delta_pow n j hj) ((hiA.add hiB).const_mul C) hpoint
    _ = C := by
      rw [integral_const_mul, integral_add hiA hiB, integral_const_mul, integral_const_mul,
        integral_div, integral_div, integral_delta]
      change C * (a * (moment q n / moment q n) + b * (tau n / tau n)) = C
      rw [div_self hM.ne', div_self ht.ne', mul_one, mul_one, hab, mul_one]
    _ = _ := rfl

end BretecheTenenbaumMean
