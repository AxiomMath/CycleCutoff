/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Cycle.Defs
public import CycleCutoff.Cycle.CosineSum
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Wilson's statistic

Wilson's statistic of a permutation `σ` of `ℤ/nℤ` is `F(σ) = ∑_{i ∈ ℤ/nℤ} cos(2π (σ(i) - i) / n)`,
the sum over the cards of the cosine of the angle through which the card `i` has been displaced.
It is maximal at the identity, where it equals `n`.

## Main definitions

* `CycleCutoff.wilsonStat`: Wilson's statistic `F(σ) = ∑_{i ∈ ℤ/nℤ} cos(2π (σ(i) - i) / n)`.

## Main results

* `CycleCutoff.cos_two_pi_val_div`: the summand `cos(2π (σ(i) - i) / n)` is unchanged when
  `σ(i) - i` is replaced by an arbitrary integer representative.
* `CycleCutoff.cos_two_pi_val_add_one`, `CycleCutoff.cos_two_pi_val_sub_one`: shifting the
  difference by `±1` shifts the angle by `±2π/n`.
* `CycleCutoff.wilsonStat_one`: `F(id) = n`.

## Implementation notes

The difference `σ(i) - i` is computed in `ZMod n`, and the summand is taken at its canonical
representative `(σ i - i).val ∈ {0, …, n - 1}`; as `cos` is `2π`-periodic, every integer
representative gives the same value.
-/

@[expose] public section

open Finset Real

namespace CycleCutoff

variable (n : ℕ) [NeZero n]

/-- Wilson's statistic `F(σ) = ∑_{i ∈ ℤ/nℤ} cos(2π (σ(i) - i) / n)`, with the canonical
representative `(σ i - i).val ∈ {0, …, n - 1}` of `σ(i) - i`. -/
@[cycle_cutoff "def_F_stat"]
noncomputable def wilsonStat (σ : Equiv.Perm (ZMod n)) : ℝ :=
  ∑ i : ZMod n, Real.cos (2 * π * ((σ i - i : ZMod n).val : ℝ) / n)

/-- `F(σ)` is the sum over `i ∈ ℤ/nℤ` of `cos(2π (σ(i) - i) / n)`. -/
theorem wilsonStat_def (σ : Equiv.Perm (ZMod n)) :
    wilsonStat n σ = ∑ i : ZMod n, Real.cos (2 * π * ((σ i - i : ZMod n).val : ℝ) / n) := rfl

variable {n}

/-- The summand of Wilson's statistic does not depend on the integer representative: if
`(k : ZMod n) = z` then `cos(2π z.val / n) = cos(2π k / n)`. -/
theorem cos_two_pi_val_div {z : ZMod n} {k : ℤ} (hk : (k : ZMod n) = z) :
    Real.cos (2 * π * (z.val : ℝ) / n) = Real.cos (2 * π * (k : ℝ) / n) := by
  subst hk
  simpa using cos_two_pi_mul_val_div (n := n) 1 k

/-- Shifting the difference by `+1` shifts the angle by `2π/n`. -/
theorem cos_two_pi_val_add_one (z : ZMod n) :
    Real.cos (2 * π * ((z + 1).val : ℝ) / n) =
      Real.cos (2 * π * (z.val : ℝ) / n + 2 * π / n) := by
  rw [cos_two_pi_val_div (k := (z.val : ℤ) + 1) (by simp)]
  congr 1
  push_cast
  ring

/-- Shifting the difference by `-1` shifts the angle by `-2π/n`. -/
theorem cos_two_pi_val_sub_one (z : ZMod n) :
    Real.cos (2 * π * ((z - 1).val : ℝ) / n) =
      Real.cos (2 * π * (z.val : ℝ) / n - 2 * π / n) := by
  rw [cos_two_pi_val_div (k := (z.val : ℤ) - 1) (by simp)]
  congr 1
  push_cast
  ring

variable (n) in
/-- At the identity every card is in place: `F(id) = n`. -/
@[simp] theorem wilsonStat_one : wilsonStat n 1 = n := by
  simp [wilsonStat]

end CycleCutoff
