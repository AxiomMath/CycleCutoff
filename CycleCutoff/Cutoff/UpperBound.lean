/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Cycle.Defs
public import CycleCutoff.Cutoff.TvSmallAfterWindow
public import CycleCutoff.Cycle.LambdaLower
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The upper bound on the mixing time

There is an absolute constant `C > 0` such that for every `ε ∈ (0, 1)` there are `C_ε > 0`
and `N₀` with `t_mix^{(n)}(ε) ≤ t_n + C n² log log n + C_ε n²` for all `n ≥ N₀`.

## Main results

* `CycleCutoff.exists_tmix_le`: the upper bound on the mixing time.

## References

* C. Defant, *Cutoff for the Adjacent Transposition Shuffle on a Cycle*, Section 7.1.
-/

public section

open Real

namespace CycleCutoff

/-- **Upper bound on the mixing time**: there is an absolute constant `C > 0` such that for
every `ε ∈ (0, 1)` there are `C_ε > 0` and `N₀` with
`t_mix^{(n)}(ε) ≤ t_n + C n² log log n + C_ε n²` for all `n ≥ N₀`. -/
@[cycle_cutoff "lem_upper_bound"]
theorem exists_tmix_le :
    ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ Cε > (0 : ℝ), ∃ N₀ : ℕ,
      ∀ (n : ℕ) [NeZero n], N₀ ≤ n →
        tmix n ε ≤ tn n + C * (n : ℝ) ^ 2 * Real.log (Real.log n) + Cε * (n : ℝ) ^ 2 := by
  obtain ⟨C, hC, h⟩ := exists_dn_le_after_window
  refine ⟨C, hC, fun ε hε hε1 => ?_⟩
  obtain ⟨Kε, hKε, N₁, hN⟩ := h ε hε hε1
  refine ⟨Kε, hKε, max N₁ 16, fun n _ hn => ?_⟩
  have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn0]
    linarith [Real.exp_one_lt_d9]
  have hlam : 0 < lambdaN n :=
    lt_of_lt_of_le (by positivity) (sixteen_div_sq_le_lambdaN (by omega))
  have htn : 0 ≤ tn n := div_nonneg (by linarith) (by positivity)
  have hll : 0 ≤ Real.log (Real.log n) := Real.log_nonneg hlog1
  exact csInf_le ⟨0, fun t ht => ht.1⟩ ⟨by positivity, hN n (le_of_max_le_left hn)⟩

end CycleCutoff
