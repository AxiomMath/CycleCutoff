/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.FiniteProbability.PinskerPointwise
public import CycleCutoff.FiniteProbability.Defs
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Pinsker's inequality

For probability vectors `α`, `ν` on a finite set `Ω` with `ν > 0`, the total variation distance
and the relative entropy satisfy `‖α - ν‖_TV ^ 2 ≤ H(α ∣ ν) / 2`.

Write `r = α / ν` and `ψ(x) = x log x - x + 1`. Since `α` and `ν` both have total mass one,
`H(α ∣ ν) = ∑ z, ν z * ψ (r z)`. The pointwise inequality `3 (x - 1)² ≤ (2x + 4) ψ(x)`
(`CycleCutoff.three_mul_sq_sub_one_le`) gives
`|α z - ν z| ^ 2 ≤ ((2 α z + 4 ν z) / 3) * (ν z * ψ (r z))`, and Cauchy–Schwarz yields
`(∑ z, |α z - ν z|) ^ 2 ≤ (∑ z, (2 α z + 4 ν z) / 3) * H(α ∣ ν) = 2 H(α ∣ ν)`.
The left side is `4 ‖α - ν‖_TV ^ 2`.

## Main results

* `CycleCutoff.tvDist_sq_le_relEnt`: Pinsker's inequality `‖α - ν‖_TV ^ 2 ≤ H(α ∣ ν) / 2`.
-/

public section

open Finset Real

namespace CycleCutoff

/-- **Pinsker's inequality**: for probability vectors `α`, `ν` with `ν > 0`,
`‖α - ν‖_TV ^ 2 ≤ H(α ∣ ν) / 2`. -/
@[cycle_cutoff "lem_pinsker"]
theorem tvDist_sq_le_relEnt {Ω : Type*} [Fintype Ω] (α ν : Ω → ℝ) (hα : IsProbVec α)
    (hν : IsProbVec ν) (hνpos : ∀ z, 0 < ν z) :
    tvDist α ν ^ 2 ≤ 1 / 2 * relEnt α ν := by
  set ψ : ℝ → ℝ := fun x => x * log x - x + 1 with hψ
  have hψnn : ∀ x, 0 ≤ x → 0 ≤ ψ x := fun x hx =>
    nonneg_of_mul_nonneg_right
      ((mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (sq_nonneg (x - 1))).trans
        (three_mul_sq_sub_one_le x hx)) (by linarith)
  have hr : ∀ z, ν z * (α z / ν z) = α z := fun z => mul_div_cancel₀ _ (hνpos z).ne'
  have hH : ∑ z, ν z * ψ (α z / ν z) = relEnt α ν := by
    have : ∀ z, ν z * ψ (α z / ν z) = α z * log (α z / ν z) - α z + ν z := fun z => by
      simp only [hψ, mul_add, mul_sub, ← mul_assoc, hr, mul_one]
    simp only [this, sum_add_distrib, sum_sub_distrib, hα.sum_eq_one, hν.sum_eq_one, relEnt]
    ring
  have hf : ∑ z, (2 * α z + 4 * ν z) / 3 = 2 := by
    rw [← sum_div, sum_add_distrib, ← mul_sum, ← mul_sum, hα.sum_eq_one, hν.sum_eq_one]
    norm_num
  have hCS : (∑ z, |α z - ν z|) ^ 2 ≤
      (∑ z, (2 * α z + 4 * ν z) / 3) * ∑ z, ν z * ψ (α z / ν z) := by
    refine sum_sq_le_sum_mul_sum_of_sq_le_mul _
      (fun z _ => by linarith [hα.nonneg z, hν.nonneg z])
      (fun z _ => mul_nonneg (hν.nonneg z)
        (hψnn _ (div_nonneg (hα.nonneg z) (hν.nonneg z)))) fun z _ => ?_
    have hνz := hνpos z
    have key := three_mul_sq_sub_one_le (α z / ν z) (div_nonneg (hα.nonneg z) hνz.le)
    have e1 : |α z - ν z| ^ 2 = ν z ^ 2 * (α z / ν z - 1) ^ 2 := by
      rw [sq_abs, ← mul_pow]
      congr 1
      field_simp
    have e2 : (2 * α z + 4 * ν z) / 3 * (ν z * ψ (α z / ν z)) =
        ν z ^ 2 * ((2 * (α z / ν z) + 4) * ψ (α z / ν z)) / 3 := by
      field_simp
    rw [e1, e2, le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    have := mul_le_mul_of_nonneg_left key (sq_nonneg (ν z))
    linarith
  rw [hf, hH] at hCS
  rw [tvDist, mul_pow]
  linarith

end CycleCutoff
