/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Cycle.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# A lower bound on the spectral gap `λ_n`

For `n ≥ 2`, `λ_n = 4 sin²(π/n) ≥ 16 / n²`.

## Main results

* `CycleCutoff.lambdaN_eq_four_mul_sin_sq`: `λ_n = 4 sin²(π/n)`.
* `CycleCutoff.sixteen_div_sq_le_lambdaN`: `16 / n² ≤ λ_n` for `n ≥ 2`.
-/

public section

open Real

namespace CycleCutoff

/-- The spectral gap in half-angle form, `λ_n = 4 sin²(π/n)`. -/
theorem lambdaN_eq_four_mul_sin_sq (n : ℕ) : lambdaN n = 4 * sin (π / n) ^ 2 := by
  rw [lambdaN, show 2 * π / n = 2 * (π / n) by ring, cos_two_mul, cos_sq']
  ring

/-- **Lower bound on the spectral gap**: `16 / n² ≤ λ_n` for `n ≥ 2`. -/
@[cycle_cutoff "lem_lambda_lower"]
theorem sixteen_div_sq_le_lambdaN {n : ℕ} (hn : 2 ≤ n) : 16 / (n : ℝ) ^ 2 ≤ lambdaN n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  have hj := mul_le_sin (div_nonneg pi_pos.le hpos.le)
    (div_le_div_of_nonneg_left pi_pos.le two_pos hn')
  rw [show 2 / π * (π / n) = 2 / n by field_simp] at hj
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 / n) hj 2
  rw [lambdaN_eq_four_mul_sin_sq]
  calc 16 / (n : ℝ) ^ 2 = 4 * (2 / n) ^ 2 := by field_simp; ring
    _ ≤ 4 * sin (π / n) ^ 2 := by linarith

end CycleCutoff
