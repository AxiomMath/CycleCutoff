/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.OneCard.Defs
public import CycleCutoff.Generator.SemigroupLower
public import CycleCutoff.Generator.SemigroupRowsum
public import CycleCutoff.OneCard.DeltaInvolution
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Nonnegativity of the integrand of `B_n`

The row `p_t(0, ·)` of the heat kernel is a probability vector for `t ≥ 0`, and consequently
`S₃(t) - S₂(t)/n ≥ 0`.

## Main results

* `CycleCutoff.heatKernel_nonneg`: `0 ≤ p_t(i, x)` for `t ≥ 0`.
* `CycleCutoff.sum_heatKernel`: `∑_x p_t(i, x) = 1`.
* `CycleCutoff.S2_div_le_S3`: `0 ≤ S₃(t) - S₂(t)/n` for `t ≥ 0`.
-/

public section

open Finset

namespace CycleCutoff

variable {n : ℕ} [NeZero n]

/-- The heat kernel is nonnegative in forward time. -/
theorem heatKernel_nonneg {t : ℝ} (ht : 0 ≤ t) (i x : ZMod n) : 0 ≤ heatKernel n t i x := by
  rw [heatKernel_def, Delta_eq_rateMatrix]
  exact (oneCardFamily n).semigroup_apply_nonneg ht i x

/-- Each row of the heat kernel sums to `1`. -/
theorem sum_heatKernel (t : ℝ) (i : ZMod n) : ∑ x, heatKernel n t i x = 1 := by
  simp only [heatKernel_def, Delta_eq_rateMatrix]
  exact (oneCardFamily n).sum_semigroup_apply t i

/-- The integrand of `B_n` is nonnegative: `S₂(t)/n ≤ S₃(t)` for `t ≥ 0`. -/
@[cycle_cutoff "lem_B_integrand_nonneg"]
theorem S2_div_le_S3 {t : ℝ} (ht : 0 ≤ t) : 0 ≤ S3 n t - S2 n t / n := by
  set p : ZMod n → ℝ := heatKernel n t 0 with hp_def
  have hp : ∀ x, 0 ≤ p x := heatKernel_nonneg ht 0
  have hsum : ∑ x, p x = 1 := sum_heatKernel t 0
  have hS2 : S2 n t = ∑ x, p x ^ 2 := rfl
  have hS3 : S3 n t = ∑ x, p x ^ 3 := rfl
  have h1 : S2 n t ^ 2 ≤ S3 n t := by
    have := sum_sq_le_sum_mul_sum_of_sq_le_mul univ (r := fun x => p x ^ 2) (f := p)
      (g := fun x => p x ^ 3) (fun x _ => hp x) (fun x _ => pow_nonneg (hp x) 3)
      (fun x _ => by ring_nf; rfl)
    rwa [hsum, one_mul, ← hS2, ← hS3] at this
  have h2 : 1 ≤ n * S2 n t := by
    have := sq_sum_le_card_mul_sum_sq (s := univ) (f := p)
    rwa [hsum, one_pow, card_univ, ZMod.card, ← hS2] at this
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_neZero n)
  have hS2pos : 0 ≤ S2 n t := sum_nonneg fun x _ => sq_nonneg (p x)
  have h3 : S2 n t / n ≤ S2 n t * S2 n t := by
    rw [div_le_iff₀ hn, mul_assoc]
    exact le_mul_of_one_le_right hS2pos (by linarith)
  nlinarith

end CycleCutoff
