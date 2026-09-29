/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Attr
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The logarithmic-mean inequality

For `u, v > 0`, `(u - v) (log u - log v) ≥ 4 (√u - √v)²`. With `u = a²` and `v = b²` this is the
inequality between the logarithmic and arithmetic means, `2 (a - b) / (a + b) ≤ log a - log b` for
`0 < b ≤ a`.

## Main results

* `CycleCutoff.two_mul_sub_div_add_le_log_sub_log`: for `0 < b ≤ a`,
  `2 (a - b) / (a + b) ≤ log a - log b`.
* `CycleCutoff.four_mul_sqrt_sub_sq_le`: for `u, v > 0`, `4 (√u - √v)² ≤ (u - v) (log u - log v)`.
-/

public section

open Real

namespace CycleCutoff

/-- The logarithmic mean is at most the arithmetic mean, in the form
`2 (a - b) / (a + b) ≤ log a - log b` for `0 < b ≤ a`. -/
theorem two_mul_sub_div_add_le_log_sub_log {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) :
    2 * (a - b) / (a + b) ≤ log a - log b := by
  have ha : 0 < a := hb.trans_le hab
  have key := le_log_one_add_of_nonneg (x := a / b - 1) <| by
    rw [sub_nonneg, one_le_div hb]; exact hab
  rwa [add_sub_cancel, log_div ha.ne' hb.ne', show a / b - 1 = (a - b) / b by field_simp,
    show (a - b) / b + 2 = (a + b) / b by field_simp; ring, ← mul_div_assoc,
    div_div_div_cancel_right₀ hb.ne'] at key

/-- **The logarithmic-mean inequality**: for `u, v > 0`,
`4 (√u - √v)² ≤ (u - v) (log u - log v)`. -/
@[cycle_cutoff "lem_log_mean_ineq"]
theorem four_mul_sqrt_sub_sq_le (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    4 * (Real.sqrt u - Real.sqrt v) ^ 2 ≤ (u - v) * (Real.log u - Real.log v) := by
  wlog h : v ≤ u generalizing u v
  · have := this v u hv hu (le_of_not_ge h)
    linarith [show (u - v) * (log u - log v) = (v - u) * (log v - log u) by ring,
      show (√u - √v) ^ 2 = (√v - √u) ^ 2 by ring]
  have hs : 0 < √u + √v := by positivity
  have key := two_mul_sub_div_add_le_log_sub_log (sqrt_pos.2 hv) (sqrt_le_sqrt h)
  rw [log_sqrt hu.le, log_sqrt hv.le, div_le_iff₀ hs] at key
  have hd : 0 ≤ √u - √v := sub_nonneg.2 (sqrt_le_sqrt h)
  have huv : u - v = (√u - √v) * (√u + √v) := by
    linear_combination (sq_sqrt hu.le).symm - (sq_sqrt hv.le).symm
  rw [huv]
  nlinarith [mul_le_mul_of_nonneg_left key hd]

end CycleCutoff
