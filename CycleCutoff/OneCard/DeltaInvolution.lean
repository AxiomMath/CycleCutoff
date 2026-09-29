/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.OneCard.Defs

/-!
# The one-card generator is an involution generator

The one-card generator `Δ` is the rate matrix `Q_{𝒯'}` of the involution family
`𝒯' = (y ↦ τ_x(y))_{x ∈ ℤ/nℤ}`, `τ_x = (x  x+1)`, for every `n ≥ 1`.

## Main results

* `CycleCutoff.oneCardFamily_generator`: `L_{𝒯'} f (y) = f(y - 1) + f(y + 1) - 2 f(y)`.
* `CycleCutoff.Delta_eq_rateMatrix`: `Δ = Q_{𝒯'}`.
-/

public section

open Finset Matrix

namespace CycleCutoff

variable {n : ℕ}

/-- The single-swap increment: `f(τ_x y) - f(y)` is `f(y + 1) - f(y)` at `x = y`,
`f(y - 1) - f(y)` at `x = y - 1`, and `0` otherwise. -/
private lemma swap_sub_eq (f : ZMod n → ℝ) (x y : ZMod n) :
    f (Equiv.swap x (x + 1) y) - f y =
      (if x = y then f (y + 1) - f y else 0) + (if x = y - 1 then f (y - 1) - f y else 0) := by
  by_cases hxy : x = y
  · subst hxy
    rw [Equiv.swap_apply_left, if_pos rfl]
    by_cases h : x = x - 1
    · rw [if_pos h, ← h, sub_self, add_zero]
    · rw [if_neg h, add_zero]
  · rw [if_neg hxy, zero_add]
    by_cases h : x = y - 1
    · subst h
      rw [sub_add_cancel, Equiv.swap_apply_right, if_pos rfl]
    · rw [if_neg h, Equiv.swap_apply_of_ne_of_ne (Ne.symm hxy), sub_self]
      rintro rfl
      exact h (add_sub_cancel_right x 1).symm

variable [NeZero n]

/-- The generator of the one-card involution family is the discrete Laplacian on `ℤ/nℤ`. -/
theorem oneCardFamily_generator (f : ZMod n → ℝ) :
    (oneCardFamily n).generator f = fun y => f (y - 1) + f (y + 1) - 2 * f y := by
  ext y
  simp only [InvFamily.generator, oneCardFamily_T, swap_sub_eq, sum_add_distrib,
    sum_ite_eq', mem_univ, if_true]
  ring

/-- The one-card generator `Δ` is the rate matrix of the involution family
`𝒯' = (y ↦ τ_x(y))_{x ∈ ℤ/nℤ}`. -/
@[cycle_cutoff "lem_Delta_involution"]
theorem Delta_eq_rateMatrix : Delta n = (oneCardFamily n).rateMatrix :=
  Matrix.ext_iff_mulVec.2 fun f => by
    rw [Delta_mulVec, InvFamily.rateMatrix_mulVec, oneCardFamily_generator]

end CycleCutoff
