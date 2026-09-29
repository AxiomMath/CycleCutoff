/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.Defs

/-!
# The inverse-generator norm

For an involution family `𝒯` on a finite type `Ω` and `g : Ω → ℝ`, the squared inverse-generator
norm is `‖g‖²_{-1,𝒯} = ⟨g, u_g⟩_{u_Ω}`, where `u_g` is a solution of the Poisson equation
`-L_𝒯 u = g` fixed by choice, and `‖g‖²_{-1,𝒯} = 0` if the equation has no solution.

## Main definitions

* `CycleCutoff.InvFamily.hMinusOneNormSq`: the squared inverse-generator norm `‖g‖²_{-1,𝒯}`.

## Main results

* `CycleCutoff.InvFamily.innerP_generator_comm`: the generator is self-adjoint in `L²(u_Ω)`.

## Implementation notes

* The Poisson equation `-L_𝒯 u = g` is written `(fun z => -𝒯.generator u z) = g`.
* The solution is chosen with `Exists.choose`; the value does not depend on the choice, by
  `CycleCutoff.InvFamily.hMinusOneNormSq_eq`.
-/

@[expose] public section

namespace CycleCutoff

namespace InvFamily

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] (𝒯 : InvFamily ι Ω)

open Classical in
/-- The squared inverse-generator norm `‖g‖²_{-1,𝒯} = ⟨g, u_g⟩_{u_Ω}`, where `u_g` is a chosen
solution of `-L_𝒯 u = g`; it is `0` when the Poisson equation has no solution. -/
@[cycle_cutoff "def_hminus1"]
noncomputable def hMinusOneNormSq (g : Ω → ℝ) : ℝ :=
  if h : ∃ u : Ω → ℝ, (fun z => -𝒯.generator u z) = g then innerP (unif Ω) g h.choose else 0

/-- The unfolding of `hMinusOneNormSq` when the Poisson equation is solvable. -/
theorem hMinusOneNormSq_of_exists {g : Ω → ℝ}
    (h : ∃ u : Ω → ℝ, (fun z => -𝒯.generator u z) = g) :
    𝒯.hMinusOneNormSq g = innerP (unif Ω) g h.choose := by
  classical
  rw [hMinusOneNormSq, dif_pos h]

omit [Fintype Ω] in
/-- The chosen solution does solve the Poisson equation. -/
theorem neg_generator_choose {g : Ω → ℝ}
    (h : ∃ u : Ω → ℝ, (fun z => -𝒯.generator u z) = g) :
    (fun z => -𝒯.generator h.choose z) = g :=
  h.choose_spec

/-- `hMinusOneNormSq g = 0` when the Poisson equation `-L_𝒯 u = g` has no solution. -/
theorem hMinusOneNormSq_of_not_exists {g : Ω → ℝ}
    (h : ¬ ∃ u : Ω → ℝ, (fun z => -𝒯.generator u z) = g) :
    𝒯.hMinusOneNormSq g = 0 := by
  classical
  rw [hMinusOneNormSq, dif_neg h]

/-- The generator is self-adjoint in `L²(u_Ω)`: `⟨L_𝒯 f, h⟩ = ⟨f, L_𝒯 h⟩`. -/
theorem innerP_generator_comm (f h : Ω → ℝ) :
    innerP (unif Ω) (𝒯.generator f) h = innerP (unif Ω) f (𝒯.generator h) := by
  rw [innerP, innerP, expectation_unif, expectation_unif]
  congr 1
  simp only [generator, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun z e => f z * (h (𝒯.T e z) - h z))]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hs : ∑ z, f (𝒯.T e z) * h z = ∑ z, f z * h (𝒯.T e z) := by
    simpa using Equiv.sum_comp (Equiv.ofBijective _ (𝒯.bijective e))
      (fun z => f z * h (𝒯.T e z))
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, hs]

end InvFamily

end CycleCutoff
