/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.OneCard.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# A lower bound on the one-card eigenvalues

For `0 ≤ j < n`, writing `j_* = min(j, n - j)`, the eigenvalue `λ_{n,j} = 2(1 - cos(2πj/n))`
of `-Δ` satisfies `λ_{n,j} ≥ 16 j_*² / n²`.

## Main results

* `CycleCutoff.sixteen_mul_sq_div_sq_le_lambdaNJ`: `16 j_*² / n² ≤ λ_{n,j}`.
-/

public section

open Real

namespace CycleCutoff

/-- `λ_{n,j} ≥ 16 j_*² / n²` with `j_* = min(j, n - j)`, for `0 ≤ j < n`. -/
@[cycle_cutoff "lem_eigenvalue_lower"]
theorem sixteen_mul_sq_div_sq_le_lambdaNJ {n j : ℕ} (hj : j < n) :
    16 * ((min j (n - j) : ℕ) : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤ lambdaNJ n j := by
  set k := min j (n - j) with hk
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hj)
  have hcos : cos (2 * π * j / n) = cos (2 * π * k / n) := by
    rcases min_choice j (n - j) with h | h
    · rw [hk, h]
    · rw [hk, h, Nat.cast_sub hj.le,
        show 2 * π * ((n : ℝ) - j) / n = 2 * π - 2 * π * j / n by field_simp, cos_two_pi_sub]
  have hk2 : ((2 * k : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : 2 * k ≤ n)
  push_cast at hk2
  set x := π * k / n with hx
  have hx0 : 0 ≤ x := by positivity
  have hxπ : x ≤ π / 2 := by
    rw [hx, div_le_iff₀ hn]
    nlinarith [pi_pos]
  have hlam : lambdaNJ n j = 4 * sin x ^ 2 := by
    rw [lambdaNJ, hcos, show 2 * π * k / n = 2 * x by rw [hx]; ring, cos_two_mul, cos_sq']
    ring
  have hsin : 2 * (k : ℝ) / n ≤ sin x := by
    have := mul_le_sin hx0 hxπ
    rwa [hx, show 2 / π * (π * k / n) = 2 * (k : ℝ) / n by field_simp] at this
  rw [hlam, show 16 * (k : ℝ) ^ 2 / (n : ℝ) ^ 2 = 4 * (2 * (k : ℝ) / n) ^ 2 by ring]
  gcongr

end CycleCutoff
