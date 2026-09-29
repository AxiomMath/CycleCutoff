/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.HMinusOneAttained
public import CycleCutoff.Generator.DirichletFormula

/-!
# The variational formula for the inverse-generator norm

If `-L_𝒯 u = g`, then `‖g‖²_{-1,𝒯}` is the greatest element of
`{2 ⟨g, f⟩_{u_Ω} - 𝒟_𝒯(f) : f : Ω → ℝ}`.

## Main results

* `CycleCutoff.InvFamily.two_mul_innerP_sub_dirichletForm`: the completed-square identity
  `2 ⟨g, f⟩ - 𝒟_𝒯(f) = ⟨g, u⟩ - 𝒟_𝒯(f - u)` when `-L_𝒯 u = g`.
* `CycleCutoff.InvFamily.isGreatest_hMinusOneNormSq`: the variational formula.
-/

public section

open Finset

namespace CycleCutoff

namespace InvFamily

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]

omit [Fintype Ω] in
/-- The generator is additive on differences: `L_𝒯 (f - h) = L_𝒯 f - L_𝒯 h`. -/
theorem generator_sub (𝒯 : InvFamily ι Ω) (f h : Ω → ℝ) (z : Ω) :
    𝒯.generator (f - h) z = 𝒯.generator f z - 𝒯.generator h z := by
  simp only [generator, Pi.sub_apply, ← sum_sub_distrib]
  exact sum_congr rfl fun _ _ => by ring

/-- Completing the square: if `-L_𝒯 u = g`, then `2 ⟨g, f⟩ - 𝒟_𝒯(f) = ⟨g, u⟩ - 𝒟_𝒯(f - u)` for
every `f`. -/
theorem two_mul_innerP_sub_dirichletForm (𝒯 : InvFamily ι Ω) {g u : Ω → ℝ}
    (hu : (fun z => -𝒯.generator u z) = g) (f : Ω → ℝ) :
    2 * innerP (unif Ω) g f - 𝒯.dirichletForm f =
      innerP (unif Ω) g u - 𝒯.dirichletForm (f - u) := by
  have hcomm := 𝒯.innerP_generator_comm u f
  subst hu
  simp only [dirichletForm, innerP, expectation, 𝒯.generator_sub, Pi.sub_apply] at hcomm ⊢
  have h4 : ∀ z, unif Ω z * ((f z - u z) * -(𝒯.generator f z - 𝒯.generator u z)) =
      unif Ω z * (f z * -𝒯.generator f z) + unif Ω z * (𝒯.generator u z * f z)
        + unif Ω z * (u z * 𝒯.generator f z) + unif Ω z * (-𝒯.generator u z * u z) :=
    fun z => by ring
  have h1 : ∀ z, unif Ω z * (-𝒯.generator u z * f z) =
      -(unif Ω z * (𝒯.generator u z * f z)) :=
    fun z => by ring
  simp only [h4, h1, sum_add_distrib, sum_neg_distrib]
  linear_combination -hcomm

/-- **Variational formula for the inverse-generator norm.** If `-L_𝒯 u = g`, then `‖g‖²_{-1,𝒯}` is
the greatest value of `2 ⟨g, f⟩_{u_Ω} - 𝒟_𝒯(f)` over `f : Ω → ℝ`. -/
@[cycle_cutoff "lem_hminus1_variational"]
theorem isGreatest_hMinusOneNormSq (𝒯 : InvFamily ι Ω) {g u : Ω → ℝ}
    (hu : (fun z => -𝒯.generator u z) = g) :
    IsGreatest (Set.range fun f : Ω → ℝ => 2 * innerP (unif Ω) g f - 𝒯.dirichletForm f)
      (𝒯.hMinusOneNormSq g) := by
  rw [𝒯.hMinusOneNormSq_eq hu]
  refine ⟨⟨u, ?_⟩, ?_⟩
  · simp only [𝒯.two_mul_innerP_sub_dirichletForm hu, sub_self]
    simp [dirichletForm, innerP, expectation, generator]
  · rintro _ ⟨f, rfl⟩
    have : 0 ≤ 𝒯.dirichletForm (f - u) := 𝒯.dirichletForm_nonneg (f - u)
    simp only [𝒯.two_mul_innerP_sub_dirichletForm hu]
    linarith

end InvFamily

end CycleCutoff
