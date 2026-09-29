/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.HMinusOneVariational
public import CycleCutoff.Generator.DirichletFormula

/-!
# A dual bound for the inverse-generator norm

If `A ≥ 0` and `⟨f, g⟩²_{u_Ω} ≤ A 𝒟_𝒯(f)` for every `f : Ω → ℝ`, then `‖g‖²_{-1,𝒯} ≤ A`.

## Main results

* `CycleCutoff.InvFamily.hMinusOneNormSq_le`: the dual bound.
-/

public section

open Finset

namespace CycleCutoff

namespace InvFamily

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]

/-- **Dual bound for the inverse-generator norm.** If `A ≥ 0` and `⟨f, g⟩²_{u_Ω} ≤ A 𝒟_𝒯(f)` for
every `f`, then `‖g‖²_{-1,𝒯} ≤ A`. -/
@[cycle_cutoff "lem_hminus1_dual_bound"]
theorem hMinusOneNormSq_le (𝒯 : InvFamily ι Ω) (A : ℝ) (hA : 0 ≤ A) (g : Ω → ℝ)
    (h : ∀ f : Ω → ℝ, innerP (unif Ω) f g ^ 2 ≤ A * 𝒯.dirichletForm f) :
    𝒯.hMinusOneNormSq g ≤ A := by
  by_cases hex : ∃ u, (fun z => -𝒯.generator u z) = g
  · obtain ⟨u, hu⟩ := hex
    obtain ⟨f, hf⟩ := (𝒯.isGreatest_hMinusOneNormSq hu).1
    rw [← hf]
    have hy : 0 ≤ 𝒯.dirichletForm f := 𝒯.dirichletForm_nonneg f
    have hsymm : innerP (unif Ω) g f = innerP (unif Ω) f g := by
      simp only [innerP, mul_comm (g _)]
    have hfg := h f
    rw [← hsymm] at hfg
    nlinarith [sq_nonneg (A - 𝒯.dirichletForm f),
      sq_nonneg (2 * innerP (unif Ω) g f - A - 𝒯.dirichletForm f)]
  · rw [𝒯.hMinusOneNormSq_of_not_exists hex]
    exact hA

end InvFamily

end CycleCutoff
