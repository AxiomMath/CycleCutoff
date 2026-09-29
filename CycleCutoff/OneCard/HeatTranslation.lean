/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.OneCard.Defs
public import CycleCutoff.Generator.Lumping

/-!
# Translation invariance of the one-card heat kernel

For `i, x ∈ ℤ/nℤ` and every real `t`, the heat kernel of the one-card generator `Δ` satisfies
`p_t(i, x) = p_t(0, x - i)`.

## Main results

* `CycleCutoff.heatKernel_eq_heatKernel_zero_sub`: `p_t(i, x) = p_t(0, x - i)`.
* `CycleCutoff.sum_comp_heatKernel`: `∑_x f(p_t(i, x)) = ∑_x f(p_t(0, x))`.
-/

public section

open Finset Matrix

namespace CycleCutoff

variable (n : ℕ) [NeZero n]

/-- Translation invariance of the one-card heat kernel: `p_t(i, x) = p_t(0, x - i)`. -/
@[cycle_cutoff "lem_heat_translation"]
theorem heatKernel_eq_heatKernel_zero_sub (t : ℝ) (i x : ZMod n) :
    heatKernel n t i x = heatKernel n t 0 (x - i) := by
  have h : ∀ f : ZMod n → ℝ,
      Delta n *ᵥ (f ∘ fun y => y - i) = (Delta n *ᵥ f) ∘ fun y => y - i := by
    intro f
    rw [Delta_mulVec, Delta_mulVec]
    funext y
    simp only [Function.comp_apply, sub_right_comm y 1 i, add_sub_right_comm y 1 i]
  have key := sum_semigroup_fiber (Delta n) (Delta n) (fun y => y - i) h t i (x - i)
  simp only [sub_left_inj, sub_self, Finset.filter_eq', Finset.mem_univ, if_true,
    Finset.sum_singleton] at key
  simpa only [heatKernel_def] using key

/-- Translation invariance: sums of a function of the row `p_t(i, ·)` do not depend on `i`. -/
theorem sum_comp_heatKernel (t : ℝ) (i : ZMod n) (f : ℝ → ℝ) :
    ∑ x, f (heatKernel n t i x) = ∑ x, f (heatKernel n t 0 x) := by
  simp only [heatKernel_eq_heatKernel_zero_sub n t i]
  exact Fintype.sum_equiv (Equiv.subRight i) _ _ fun _ => rfl

end CycleCutoff
