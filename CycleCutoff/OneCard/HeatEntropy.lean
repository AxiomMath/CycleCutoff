/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.OneCard.Defs
public import CycleCutoff.OneCard.S2Bound
public import CycleCutoff.OneCard.BIntegrandNonneg

/-!
# The one-card entropy decays at twice the spectral gap

There is an absolute constant `c₈ > 0` such that for all `n ≥ 3` and `t ≥ a₀/λ_n`,
`h(t) ≤ c₈ e^{-2λ_n t}`, where `h(t) = ∑_x p_t(0, x) log(n p_t(0, x))`.

## Main results

* `CycleCutoff.oneCardEntropy_le_mul_S2_sub_one`: `h(t) ≤ n S₂(t) - 1` for `t ≥ 0`.
* `CycleCutoff.exists_oneCardEntropy_le`: `h(t) ≤ c₈ e^{-2λ_n t}` for `t ≥ a₀/λ_n`.
-/

public section

open Finset Real

namespace CycleCutoff

/-- The entropy is dominated by the collision sum: `h(t) ≤ n S₂(t) - 1` for `t ≥ 0`. -/
theorem oneCardEntropy_le_mul_S2_sub_one {n : ℕ} [NeZero n] {t : ℝ} (ht : 0 ≤ t) :
    oneCardEntropy n t ≤ (n : ℝ) * S2 n t - 1 := by
  have key : ∀ x : ZMod n, heatKernel n t 0 x * Real.log (n * heatKernel n t 0 x) ≤
      (n : ℝ) * heatKernel n t 0 x ^ 2 - heatKernel n t 0 x := by
    intro x
    have hp := heatKernel_nonneg ht 0 x
    rcases hp.eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
      have := Real.log_le_sub_one_of_pos (mul_pos hn hpos)
      nlinarith
  calc oneCardEntropy n t
      ≤ ∑ x : ZMod n, ((n : ℝ) * heatKernel n t 0 x ^ 2 - heatKernel n t 0 x) :=
        sum_le_sum fun x _ => key x
    _ = (n : ℝ) * S2 n t - 1 := by
        rw [sum_sub_distrib, ← mul_sum, sum_heatKernel, S2]

/-- The one-card entropy decays at twice the spectral gap: there is an absolute constant
`c₈ > 0` with `h(t) ≤ c₈ e^{-2λ_n t}` for all `n ≥ 3` and `t ≥ a₀/λ_n`. -/
@[cycle_cutoff "lem_heat_entropy"]
theorem exists_oneCardEntropy_le :
    ∃ c₈ > (0 : ℝ), ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ t : ℝ, a0 / lambdaN n ≤ t →
      oneCardEntropy n t ≤ c₈ * Real.exp (-2 * lambdaN n * t) := by
  obtain ⟨c, hc, hS2⟩ := exists_mul_S2_sub_one_le
  refine ⟨c, hc, fun n _ hn t ht => ?_⟩
  have ht0 : 0 ≤ t := (div_nonneg (by norm_num [a0]) (lambdaN_nonneg n)).trans ht
  exact (oneCardEntropy_le_mul_S2_sub_one ht0).trans (hS2 n hn t ht)

end CycleCutoff
