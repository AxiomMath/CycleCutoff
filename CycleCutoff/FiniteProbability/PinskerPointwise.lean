/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Attr
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# A pointwise inequality behind Pinsker's inequality

For every real `x ≥ 0`, `3 (x - 1)² ≤ (2x + 4)(x log x - x + 1)`. Summed against a
probability vector this is the pointwise form of Pinsker's inequality relating relative entropy
and total variation.

Let `G(x) = (2x + 4)(x log x - x + 1) - 3 (x - 1)²`. Its derivative
`G'(x) = 4((x + 1) log x - 2(x - 1))` has the sign of `x - 1`, by the bound
`2(x - 1)/(x + 1) ≤ log x` for `x ≥ 1` applied at `x` and at `x⁻¹`. Hence `G` is antitone on
`[0, 1]` and monotone on `[1, ∞)`, so `G ≥ G(1) = 0`; at `x = 0`, `x log x = 0` since
`Real.log 0 = 0`.

## Main results

* `CycleCutoff.three_mul_sq_sub_one_le`: `3 (x - 1)² ≤ (2x + 4)(x log x - x + 1)` for `0 ≤ x`.
-/

public section

open Real Set

namespace CycleCutoff

/-- The derivative of `G(x) = (2x + 4)(x log x - x + 1) - 3 (x - 1)²` at a point `x > 0`. -/
private lemma hasDerivAt_pinskerAux {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => (2 * x + 4) * (x * log x - x + 1) - 3 * (x - 1) ^ 2)
      (4 * ((x + 1) * log x - 2 * (x - 1))) x := by
  have h1 : HasDerivAt (fun y : ℝ => y * log y - y + 1) (log x) x := by
    simpa using ((hasDerivAt_mul_log hx.ne').sub (hasDerivAt_id x)).add_const 1
  have h2 : HasDerivAt (fun y : ℝ => 2 * y + 4) 2 x := by
    simpa using ((hasDerivAt_id x).const_mul 2).add_const 4
  have h3 : HasDerivAt (fun y : ℝ => 3 * (y - 1) ^ 2) (6 * (x - 1)) x :=
    ((((hasDerivAt_id x).sub_const 1).pow 2).const_mul 3).congr_deriv (by simp; ring)
  exact ((h2.mul h1).sub h3).congr_deriv (by ring)

/-- For `x ≥ 1`, `2(x - 1) ≤ (x + 1) log x`. -/
private lemma two_mul_sub_one_le_add_one_mul_log {x : ℝ} (hx : 1 ≤ x) :
    2 * (x - 1) ≤ (x + 1) * log x := by
  have := le_log_one_add_of_nonneg (x := x - 1) (by linarith)
  rw [add_sub_cancel, show x - 1 + 2 = x + 1 by ring, div_le_iff₀ (by linarith)] at this
  linarith

/-- For `0 < x ≤ 1`, `(x + 1) log x ≤ 2(x - 1)`. -/
private lemma add_one_mul_log_le_two_mul_sub_one {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1) :
    (x + 1) * log x ≤ 2 * (x - 1) := by
  have h := two_mul_sub_one_le_add_one_mul_log (x := x⁻¹) ((one_le_inv₀ hx0).mpr hx)
  rw [log_inv] at h
  have h' : x * (2 * (x⁻¹ - 1)) ≤ x * ((x⁻¹ + 1) * -log x) :=
    mul_le_mul_of_nonneg_left h hx0.le
  have e1 : x * (2 * (x⁻¹ - 1)) = 2 * (1 - x) := by field_simp
  have e2 : x * ((x⁻¹ + 1) * -log x) = -((x + 1) * log x) := by field_simp; ring
  linarith

/-- **Pointwise Pinsker inequality**: for `x ≥ 0`,
`3 (x - 1)² ≤ (2x + 4)(x log x - x + 1)`. -/
@[cycle_cutoff "lem_pinsker_pointwise"]
theorem three_mul_sq_sub_one_le (x : ℝ) (hx : 0 ≤ x) :
    3 * (x - 1) ^ 2 ≤ (2 * x + 4) * (x * log x - x + 1) := by
  set G : ℝ → ℝ := fun x => (2 * x + 4) * (x * log x - x + 1) - 3 * (x - 1) ^ 2 with hG
  have hcont : Continuous G :=
    (((continuous_const.mul continuous_id).add continuous_const).mul
      ((continuous_mul_log.sub continuous_id).add continuous_const)).sub
      (continuous_const.mul ((continuous_id.sub continuous_const).pow 2))
  have hG1 : G 1 = 0 := by simp [hG]
  suffices 0 ≤ G x by simp only [hG] at this; linarith
  rw [← hG1]
  rcases le_total x 1 with h | h
  · have hanti : AntitoneOn G (Icc 0 1) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hcont.continuousOn ?_ ?_
      · intro y hy
        rw [interior_Icc] at hy
        exact (hasDerivAt_pinskerAux hy.1).differentiableAt.differentiableWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        rw [(hasDerivAt_pinskerAux hy.1).deriv]
        nlinarith [add_one_mul_log_le_two_mul_sub_one hy.1 hy.2.le]
    exact hanti ⟨hx, h⟩ ⟨zero_le_one, le_rfl⟩ h
  · have hmono : MonotoneOn G (Ici 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 1) hcont.continuousOn ?_ ?_
      · intro y hy
        rw [interior_Ici] at hy
        exact (hasDerivAt_pinskerAux (zero_lt_one.trans hy)).differentiableAt.differentiableWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        rw [(hasDerivAt_pinskerAux (zero_lt_one.trans hy)).deriv]
        nlinarith [two_mul_sub_one_le_add_one_mul_log hy.le]
    exact hmono (mem_Ici.mpr le_rfl) h h

end CycleCutoff
