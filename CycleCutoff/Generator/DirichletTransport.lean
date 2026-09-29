/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.DirichletFormula
public import CycleCutoff.FiniteProbability.PushforwardExpectation

/-!
# Transport of the Dirichlet form along an intertwining map

Let `𝒯 = (T_e)_{e ∈ ι}` and `𝒯' = (T'_{e'})_{e' ∈ ι'}` be involution families on finite sets `Ω`
and `Ω'`, let `σ : ι ≃ ι'` be a bijection of the index sets, and let `Ψ : Ω → Ω'` push the uniform
measure on `Ω` forward to the uniform measure on `Ω'` and intertwine the families,
`Ψ ∘ T_e = T'_{σ e} ∘ Ψ`. Then `𝒟_𝒯(f ∘ Ψ) = 𝒟_{𝒯'}(f)` for every `f : Ω' → ℝ`.

## Main results

* `CycleCutoff.InvFamily.dirichletForm_comp`: the Dirichlet form is transported along an
  intertwining, uniform-measure-preserving map.
-/

public section

open Finset

namespace CycleCutoff

namespace InvFamily

/-- **Transport of the Dirichlet form.** If `Ψ : Ω → Ω'` pushes `u_Ω` forward to `u_{Ω'}` and
intertwines `𝒯` with `𝒯'` along the index bijection `σ`, then `𝒟_𝒯(f ∘ Ψ) = 𝒟_{𝒯'}(f)`. -/
@[cycle_cutoff "lem_dirichlet_transport"]
theorem dirichletForm_comp {ι ι' Ω Ω' : Type*} [Fintype ι] [Fintype ι'] [Fintype Ω]
    [Fintype Ω'] (𝒯 : InvFamily ι Ω) (𝒯' : InvFamily ι' Ω') (σ : ι ≃ ι') (Ψ : Ω → Ω')
    (hΨ : pushforward Ψ (unif Ω) = unif Ω') (hcomm : ∀ e z, Ψ (𝒯.T e z) = 𝒯'.T (σ e) (Ψ z))
    (f : Ω' → ℝ) :
    𝒯.dirichletForm (f ∘ Ψ) = 𝒯'.dirichletForm f := by
  rw [dirichletForm_eq, dirichletForm_eq,
    ← Equiv.sum_comp σ (fun e' => expectation (unif Ω') fun z => (f (𝒯'.T e' z) - f z) ^ 2)]
  congr 1
  refine sum_congr rfl fun e _ => ?_
  simp only [Function.comp_apply, hcomm]
  rw [expectation_comp (unif Ω) Ψ (fun y => (f (𝒯'.T (σ e) y) - f y) ^ 2), hΨ]

end InvFamily

end CycleCutoff
