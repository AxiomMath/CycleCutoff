/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Attr
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A pointwise bound for `t² log t² - t² + 1`

Let `ψ(t) = t² log(t²) - t² + 1`. For every real `t ≥ 0`,
`ψ(t) ≤ 3 (t - 1)² (1 + max(0, log(t²)))`. The three ranges of `t` are handled as follows:

* for `0 < t ≤ 1`, `log t ≤ t - 1` gives `ψ(t) ≤ (t - 1)² (2t + 1) ≤ 3 (t - 1)²`;
* for `1 < t < 2`, `log t ≤ (t - 1)(2t - 1) / t²`, which follows from
  `1 + y + y²/2 ≤ exp y` at `y = (t - 1)(2t - 1) / t²`, since
  `1 + y + y²/2 - t = (t - 1)² (1 + 2t(t - 1)(2 - t)) / (2t⁴) ≥ 0`; this bound on `log t`
  makes `ψ(t) ≤ 3 (t - 1)²` an identity;
* for `t ≥ 2`, use `log(t²) ≤ t² - 1` and `t + 1 ≤ 3 (t - 1)`.

## Main results

* `CycleCutoff.sq_mul_log_sq_sub_sq_add_one_le`: `ψ(t) ≤ 3 (t - 1)² (1 + max(0, log(t²)))`.
-/

public section

namespace CycleCutoff

/-- For `1 < t < 2`, `log t ≤ (t - 1)(2t - 1) / t²`. -/
private lemma log_le_of_one_lt_of_lt_two {t : ℝ} (h1 : 1 < t) (h2 : t < 2) :
    Real.log t ≤ (t - 1) * (2 * t - 1) / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hy : 0 ≤ (t - 1) * (2 * t - 1) / t ^ 2 :=
    div_nonneg (by nlinarith) (sq_nonneg t)
  have hpoly :
      t ≤ 1 + (t - 1) * (2 * t - 1) / t ^ 2 + ((t - 1) * (2 * t - 1) / t ^ 2) ^ 2 / 2 := by
    rw [← sub_nonneg]
    have key : 1 + (t - 1) * (2 * t - 1) / t ^ 2 + ((t - 1) * (2 * t - 1) / t ^ 2) ^ 2 / 2 - t
        = (t - 1) ^ 2 * (1 + 2 * t * (t - 1) * (2 - t)) / (2 * t ^ 4) := by
      field_simp
      ring
    rw [key]
    refine div_nonneg (mul_nonneg (sq_nonneg _) ?_) (by positivity)
    nlinarith [mul_nonneg (mul_nonneg ht0.le (by linarith : (0 : ℝ) ≤ t - 1))
      (by linarith : (0 : ℝ) ≤ 2 - t)]
  rw [Real.log_le_iff_le_exp ht0]
  linarith [Real.quadratic_le_exp_of_nonneg hy]

/-- **Pointwise bound for `t² log(t²) - t² + 1`.** For every real `t ≥ 0`,
`t² log(t²) - t² + 1 ≤ 3 (t - 1)² (1 + max(0, log(t²)))`. -/
@[cycle_cutoff "lem_psi_pointwise"]
theorem sq_mul_log_sq_sub_sq_add_one_le (t : ℝ) (ht : 0 ≤ t) :
    t ^ 2 * Real.log (t ^ 2) - t ^ 2 + 1 ≤ 3 * (t - 1) ^ 2 * (1 + max 0 (Real.log (t ^ 2))) := by
  rcases le_or_gt 2 t with h2 | h2
  · have hL : 0 ≤ Real.log (t ^ 2) := Real.log_nonneg (by nlinarith)
    have hL' : Real.log (t ^ 2) ≤ t ^ 2 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [max_eq_right hL]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ t - 1)
      (by linarith : (0 : ℝ) ≤ 2 * t - 4)) hL, sq_nonneg (t - 1)]
  suffices h : t ^ 2 * Real.log (t ^ 2) - t ^ 2 + 1 ≤ 3 * (t - 1) ^ 2 by
    nlinarith [mul_nonneg (sq_nonneg (t - 1)) (le_max_left 0 (Real.log (t ^ 2)))]
  rcases ht.eq_or_lt with rfl | ht0
  · norm_num
  rw [Real.log_pow]
  push_cast
  rcases le_or_gt t 1 with h1 | h1
  · nlinarith [mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos ht0) (sq_nonneg t)]
  · have h := mul_le_mul_of_nonneg_left (log_le_of_one_lt_of_lt_two h1 h2) (sq_nonneg t)
    rw [mul_div_cancel₀ _ (by positivity)] at h
    nlinarith

end CycleCutoff
