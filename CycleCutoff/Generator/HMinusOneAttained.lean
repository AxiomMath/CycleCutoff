/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.HMinusOne

/-!
# The inverse-generator norm is attained at every solution

If `-L_𝒯 u = g`, then `‖g‖²_{-1,𝒯} = ⟨g, u⟩_{u_Ω}`. In particular the value of
`InvFamily.hMinusOneNormSq` does not depend on which solution of the Poisson equation the
definition chooses.

## Main results

* `CycleCutoff.InvFamily.hMinusOneNormSq_eq`: `‖g‖²_{-1,𝒯} = ⟨g, u⟩` whenever `-L_𝒯 u = g`.
-/

public section

namespace CycleCutoff

namespace InvFamily

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]

/-- **The inverse-generator norm is attained at every solution.** If `-L_𝒯 u = g`, then
`‖g‖²_{-1,𝒯} = ⟨g, u⟩_{u_Ω}`. -/
@[cycle_cutoff "lem_hminus1_attained"]
theorem hMinusOneNormSq_eq (𝒯 : InvFamily ι Ω) {g u : Ω → ℝ}
    (hu : (fun z => -𝒯.generator u z) = g) :
    𝒯.hMinusOneNormSq g = innerP (unif Ω) g u := by
  have hex : ∃ w : Ω → ℝ, (fun z => -𝒯.generator w z) = g := ⟨u, hu⟩
  rw [𝒯.hMinusOneNormSq_of_exists hex]
  calc innerP (unif Ω) g hex.choose
      = innerP (unif Ω) (fun z => -𝒯.generator u z) hex.choose := by rw [hu]
    _ = -innerP (unif Ω) (𝒯.generator u) hex.choose := by simp [innerP, neg_mul]
    _ = -innerP (unif Ω) u (𝒯.generator hex.choose) := by rw [𝒯.innerP_generator_comm]
    _ = innerP (unif Ω) u (fun z => -𝒯.generator hex.choose z) := by simp [innerP, mul_neg]
    _ = innerP (unif Ω) u g := by rw [𝒯.neg_generator_choose hex]
    _ = innerP (unif Ω) g u := by simp only [innerP, mul_comm]

end InvFamily

end CycleCutoff
