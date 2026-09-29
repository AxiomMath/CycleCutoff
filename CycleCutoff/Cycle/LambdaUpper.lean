/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Cycle.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# An upper bound on the spectral gap of the cycle

For every `n : ℕ`, the spectral gap `λ_n = 2 - 2 cos(2π/n)` of the one-card walk satisfies
`λ_n ≤ 4π²/n²`.

## Main results

* `CycleCutoff.lambdaN_le_four_pi_sq_div_sq`: `λ_n ≤ 4π²/n²`.
-/

public section

open Real

namespace CycleCutoff

/-- The spectral gap of the cycle satisfies `λ_n ≤ 4π²/n²`. -/
@[cycle_cutoff "lem_lambda_upper"]
theorem lambdaN_le_four_pi_sq_div_sq (n : ℕ) :
    lambdaN n ≤ 4 * π ^ 2 / (n : ℝ) ^ 2 := by
  have h := one_sub_sq_div_two_le_cos (x := 2 * π / n)
  rw [lambdaN]
  have : (2 * π / n) ^ 2 = 4 * π ^ 2 / (n : ℝ) ^ 2 := by ring
  linarith

end CycleCutoff
