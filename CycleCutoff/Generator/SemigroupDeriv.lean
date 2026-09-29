/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.Defs
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The derivative of a matrix semigroup

For a real square matrix `Q`, the semigroup `t ↦ P^Q_t = exp(t Q)` is differentiable, with
`d/dt P^Q_t = P^Q_t Q = Q P^Q_t`.

## Main results

* `CycleCutoff.hasDerivAt_semigroup_apply`: `d/dt P^Q_t(z, w) = (P^Q_t Q)(z, w)`.
* `CycleCutoff.hasDerivAt_semigroup_apply'`: `d/dt P^Q_t(z, w) = (Q P^Q_t)(z, w)`.

## Implementation notes

The statements are entrywise: `Matrix` carries no global norm, so a matrix-valued derivative would
depend on a choice of norm.
-/

public section

namespace CycleCutoff

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **Derivative of the semigroup.** The entries of the semigroup satisfy
`d/dt P^Q_t(z, w) = (P^Q_t Q)(z, w)`. -/
@[cycle_cutoff "lem_semigroup_deriv"]
theorem hasDerivAt_semigroup_apply (Q : Matrix Ω Ω ℝ) (t : ℝ) (z w : Ω) :
    HasDerivAt (fun s => semigroup Q s z w) ((semigroup Q t * Q) z w) t := by
  let := Matrix.linftyOpNormedRing (n := Ω) (α := ℝ)
  let := Matrix.linftyOpNormedAlgebra (n := Ω) (R := ℝ) (α := ℝ)
  let L : Matrix Ω Ω ℝ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ z w)
  exact L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const (𝕂 := ℝ) Q t)

/-- **Derivative of the semigroup.** The entries of the semigroup satisfy
`d/dt P^Q_t(z, w) = (Q P^Q_t)(z, w)`. -/
@[cycle_cutoff "lem_semigroup_deriv"]
theorem hasDerivAt_semigroup_apply' (Q : Matrix Ω Ω ℝ) (t : ℝ) (z w : Ω) :
    HasDerivAt (fun s => semigroup Q s z w) ((Q * semigroup Q t) z w) t := by
  let := Matrix.linftyOpNormedRing (n := Ω) (α := ℝ)
  let := Matrix.linftyOpNormedAlgebra (n := Ω) (R := ℝ) (α := ℝ)
  let L : Matrix Ω Ω ℝ →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ z w)
  exact L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const' (𝕂 := ℝ) Q t)

end CycleCutoff
