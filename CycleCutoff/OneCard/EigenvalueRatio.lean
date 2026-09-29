/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.OneCard.Defs
public import CycleCutoff.OneCard.EigenvalueLower
public import CycleCutoff.Cycle.LambdaUpper

/-!
# The one-card eigenvalues dominate the spectral gap

For `1 ≤ j ≤ n - 1`, writing `j_* = min(j, n - j)`, the eigenvalue `λ_{n,j}` of `-Δ` satisfies
`λ_{n,j} ≥ max(1, 4 j_*² / π²) λ_n`, where `λ_n = 2 - 2 cos(2π/n)` is the spectral gap.

## Main results

* `CycleCutoff.lambdaN_nonneg`: `0 ≤ λ_n`.
* `CycleCutoff.lambdaN_le_lambdaNJ`: `λ_n ≤ λ_{n,j}`.
* `CycleCutoff.max_mul_lambdaN_le_lambdaNJ`: `max(1, 4 j_*²/π²) λ_n ≤ λ_{n,j}`.
-/

public section

open Real

namespace CycleCutoff

/-- The spectral gap is nonnegative, `0 ≤ λ_n`. -/
theorem lambdaN_nonneg (n : ℕ) : 0 ≤ lambdaN n := by
  rw [lambdaN]
  linarith [cos_le_one (2 * π / n)]

/-- `λ_n ≤ λ_{n,j}` for `1 ≤ j ≤ n - 1`. -/
theorem lambdaN_le_lambdaNJ {n j : ℕ} (hj₁ : 1 ≤ j) (hj₂ : j ≤ n - 1) :
    lambdaN n ≤ lambdaNJ n j := by
  have hj : j < n := by omega
  set k := min j (n - j) with hk
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hj)
  have hcos : cos (2 * π * j / n) = cos (2 * π * k / n) := by
    rcases min_choice j (n - j) with h | h
    · rw [hk, h]
    · rw [hk, h, Nat.cast_sub hj.le,
        show 2 * π * ((n : ℝ) - j) / n = 2 * π - 2 * π * j / n by field_simp, cos_two_pi_sub]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hk2 : 2 * (k : ℝ) ≤ n := by exact_mod_cast (by omega : 2 * k ≤ n)
  have hle : cos (2 * π * k / n) ≤ cos (2 * π / n) := by
    apply cos_le_cos_of_nonneg_of_le_pi (by positivity)
    · rw [div_le_iff₀ hn]
      nlinarith [pi_pos]
    · rw [div_le_div_iff_of_pos_right hn]
      nlinarith [pi_pos]
  rw [lambdaN, lambdaNJ, hcos]
  linarith

/-- `max(1, 4 j_*²/π²) λ_n ≤ λ_{n,j}` with `j_* = min(j, n - j)`, for `1 ≤ j ≤ n - 1`. -/
@[cycle_cutoff "lem_eigenvalue_ratio"]
theorem max_mul_lambdaN_le_lambdaNJ {n j : ℕ} (hj₁ : 1 ≤ j) (hj₂ : j ≤ n - 1) :
    max 1 (4 * ((min j (n - j) : ℕ) : ℝ) ^ 2 / π ^ 2) * lambdaN n ≤ lambdaNJ n j := by
  have hj : j < n := by omega
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hj)
  rw [max_mul_of_nonneg _ _ (lambdaN_nonneg n), one_mul]
  refine max_le (lambdaN_le_lambdaNJ hj₁ hj₂) ?_
  set k : ℝ := ((min j (n - j) : ℕ) : ℝ)
  calc 4 * k ^ 2 / π ^ 2 * lambdaN n ≤ 4 * k ^ 2 / π ^ 2 * (4 * π ^ 2 / (n : ℝ) ^ 2) := by
        gcongr
        exact lambdaN_le_four_pi_sq_div_sq n
    _ = 16 * k ^ 2 / (n : ℝ) ^ 2 := by field_simp; ring
    _ ≤ lambdaNJ n j := sixteen_mul_sq_div_sq_le_lambdaNJ hj

end CycleCutoff
