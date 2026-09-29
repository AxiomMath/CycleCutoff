/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Cutoff.Defs
public import CycleCutoff.OneCard.DeltaInvolution

/-!
# Wilson's statistic is an eigenfunction

Wilson's statistic `F(σ) = ∑_i cos(2π(σ(i) - i)/n)` is an eigenfunction of the generator of the
cycle shuffle, `L_{𝒯_n} F = -λ_n F`.

## Main results

* `CycleCutoff.generator_wilsonStat`: `L_{𝒯_n} F = -λ_n F`.
-/

public section

open Finset Real

namespace CycleCutoff

variable {n : ℕ} [NeZero n]

/-- The discrete Laplacian of `y ↦ cos(2π(y - i)/n)` is `-λ_n` times that function. -/
private lemma laplacian_cos (i y : ZMod n) :
    Real.cos (2 * π * ((y - 1 - i : ZMod n).val : ℝ) / n) +
        Real.cos (2 * π * ((y + 1 - i : ZMod n).val : ℝ) / n) -
        2 * Real.cos (2 * π * ((y - i : ZMod n).val : ℝ) / n) =
      -lambdaN n * Real.cos (2 * π * ((y - i : ZMod n).val : ℝ) / n) := by
  rw [show y - 1 - i = (y - i) - 1 by ring, show y + 1 - i = (y - i) + 1 by ring,
    cos_two_pi_val_sub_one, cos_two_pi_val_add_one, Real.cos_sub, Real.cos_add, lambdaN]
  ring

variable (n) in
/-- Wilson's statistic is an eigenfunction of the cycle-shuffle generator:
`L_{𝒯_n} F = -λ_n F`. -/
@[cycle_cutoff "lem_F_eigenfunction"]
theorem generator_wilsonStat :
    (cycleShuffle n).generator (wilsonStat n) = fun σ => -lambdaN n * wilsonStat n σ := by
  ext σ
  simp only [InvFamily.generator, wilsonStat, cycleShuffle_T, Equiv.Perm.mul_apply,
    ← sum_sub_distrib, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  have h := congrFun (oneCardFamily_generator
    (fun y : ZMod n => Real.cos (2 * π * ((y - i : ZMod n).val : ℝ) / n))) (σ i)
  simp only [InvFamily.generator, oneCardFamily_T] at h
  rw [h, laplacian_cos]

end CycleCutoff
