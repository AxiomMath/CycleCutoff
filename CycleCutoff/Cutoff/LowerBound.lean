/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Cycle.Defs
public import CycleCutoff.Cutoff.LowerTv
public import CycleCutoff.Cutoff.TvSmallAfterWindow
public import CycleCutoff.Cycle.LambdaLower
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The lower bound on the mixing time

For every `ε ∈ (0, 1)` there are `C_ε > 0` and `N₀` with `t_n - C_ε n² ≤ t_mix^{(n)}(ε)` for all
`n ≥ N₀`.

## Main results

* `CycleCutoff.exists_pos_mul_exp_neg_lt`: `K e^{-2s} < c` for some `s > 0`.
* `CycleCutoff.exists_tn_sub_le_tmix`: `t_n - C_ε n² ≤ t_mix^{(n)}(ε)` for `n ≥ N₀`.

## Implementation notes

`t_mix^{(n)}(ε)` is an infimum in `ℝ`, where `sInf ∅ = 0`.
-/

public section

namespace CycleCutoff

/-- For positive `K` and `c` some positive `s` has `K * exp (-2 * s) < c`. -/
theorem exists_pos_mul_exp_neg_lt {K c : ℝ} (hK : 0 < K) (hc : 0 < c) :
    ∃ s > (0 : ℝ), K * Real.exp (-2 * s) < c := by
  refine ⟨K / c, by positivity, ?_⟩
  rw [show -2 * (K / c) = -(2 * (K / c)) by ring, Real.exp_neg,
    mul_inv_lt_iff₀ (Real.exp_pos _)]
  nlinarith [Real.add_one_le_exp (2 * (K / c)), div_mul_cancel₀ K hc.ne', mul_pos hK hc]

/-- **Lower bound on the mixing time.** For every `ε ∈ (0, 1)` there are `C_ε > 0` and `N₀` with
`t_n - C_ε n² ≤ t_mix^{(n)}(ε)` for all `n ≥ N₀`. -/
@[cycle_cutoff "lem_lower_bound"]
theorem exists_tn_sub_le_tmix :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ Cε > (0 : ℝ), ∃ N₀ : ℕ, ∀ (n : ℕ) [NeZero n], N₀ ≤ n →
      tn n - Cε * (n : ℝ) ^ 2 ≤ tmix n ε := by
  intro ε hε hε1
  obtain ⟨K, hK, hlow⟩ := exists_one_sub_le_dn
  obtain ⟨C, hC, hwin⟩ := exists_dn_le_after_window
  obtain ⟨Kε, hKε, N₁, hN₁⟩ := hwin ε hε hε1
  obtain ⟨sε, hsε0, hKs⟩ := exists_pos_mul_exp_neg_lt hK (show (0 : ℝ) < 1 - ε by linarith)
  refine ⟨sε / 16, by positivity, max N₁ 3, fun n _ hN => ?_⟩
  have hn3 : 3 ≤ n := le_of_max_le_right hN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlam16 : 16 / (n : ℝ) ^ 2 ≤ lambdaN n := sixteen_div_sq_le_lambdaN (by omega)
  have hlam : 0 < lambdaN n := lt_of_lt_of_le (by positivity) hlam16
  have hne : {t : ℝ | 0 ≤ t ∧ dn n t ≤ ε}.Nonempty := by
    refine ⟨_, ?_, hN₁ n (le_of_max_le_left hN)⟩
    have hlog1 : 1 ≤ Real.log n := by
      rw [Real.le_log_iff_exp_le hn0]
      calc Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
        _ ≤ n := by exact_mod_cast hn3
    have htn : 0 ≤ tn n := div_nonneg (by linarith) (by positivity)
    have hll : 0 ≤ Real.log (Real.log n) := Real.log_nonneg hlog1
    positivity
  have hmix : tn n - sε / lambdaN n ≤ tmix n ε := by
    refine le_csInf hne fun b ⟨hb0, hbd⟩ => ?_
    by_contra! hlt
    set s := lambdaN n * (tn n - b) with hs
    have hb : tn n - s / lambdaN n = b := by rw [hs]; field_simp; ring
    have hss : sε ≤ s := by rw [hs, ← div_le_iff₀' hlam]; linarith
    have h := hlow n hn3 s (by rw [hb]; exact hb0)
    rw [hb] at h
    have := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (show -2 * s ≤ -2 * sε by linarith)) hK.le
    linarith
  have hinv : sε / lambdaN n ≤ sε / 16 * (n : ℝ) ^ 2 := by
    rw [div_le_iff₀ hlam]
    rw [div_le_iff₀ (by positivity)] at hlam16
    nlinarith
  linarith

end CycleCutoff
