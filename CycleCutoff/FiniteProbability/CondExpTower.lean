/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.FiniteProbability.Defs

/-!
# The tower property of conditional expectation

Let `ν` be a strictly positive weight vector on a finite type `Ω`, let `Φ' : Ω → Y'` and
`ψ : Y' → Y`, and put `Φ = ψ ∘ Φ'`, so that `Φ` is coarser than `Φ'`. Conditioning first on
the finer map and then on the coarser one is the same as conditioning on the coarser one:
`𝔼_ν[𝔼_ν[f ∣ Φ'] ∣ Φ] = 𝔼_ν[f ∣ Φ]`.

Each fibre `F` of `Φ` is the disjoint union of the fibres of `Φ'` it meets, each of positive
mass, and on such a fibre `G` the function `𝔼_ν[f ∣ Φ']` is the constant
`ν(G)⁻¹ ∑_{w ∈ G} ν(w) f(w)`; hence the `ν`-weighted sums of `𝔼_ν[f ∣ Φ']` and of `f` over `F`
agree.

## Main results

* `CycleCutoff.condExp_condExp_comp`: the tower property
  `𝔼_ν[𝔼_ν[f ∣ Φ'] ∣ ψ ∘ Φ'] = 𝔼_ν[f ∣ ψ ∘ Φ']`.
-/

public section

open Finset

namespace CycleCutoff

variable {Ω Y Y' : Type*} [Fintype Ω]

/-- **Tower property.** If `Φ = ψ ∘ Φ'` is coarser than `Φ'`, then conditioning on `Φ'` and
then on `Φ` is conditioning on `Φ`: `𝔼_ν[𝔼_ν[f ∣ Φ'] ∣ Φ] = 𝔼_ν[f ∣ Φ]`. -/
@[cycle_cutoff "lem_cond_exp_tower"]
theorem condExp_condExp_comp (ν : Ω → ℝ) (hν : ∀ z, 0 < ν z)
    (Φ' : Ω → Y') (ψ : Y' → Y) (f : Ω → ℝ) :
    condExp ν (ψ ∘ Φ') (condExp ν Φ' f) = condExp ν (ψ ∘ Φ') f := by
  funext z
  rw [condExp_apply, condExp_apply]
  congr 1
  set F := fiber (ψ ∘ Φ') z
  calc ∑ w ∈ F, ν w * condExp ν Φ' f w
      = ∑ w ∈ F, ∑ v ∈ fiber Φ' w, ν w * (ν v * f v / mass ν (fiber Φ' v)) := by
        refine sum_congr rfl fun w _ => ?_
        rw [condExp_apply, sum_div, mul_sum]
        refine sum_congr rfl fun v hv => ?_
        rw [fiber_eq_of_mem hv]
    _ = ∑ v ∈ F, ∑ w ∈ fiber Φ' v, ν w * (ν v * f v / mass ν (fiber Φ' v)) := by
        refine sum_comm' fun w v => ?_
        simp only [F, mem_fiber, Function.comp_apply]
        grind
    _ = ∑ v ∈ F, ν v * f v := by
        refine sum_congr rfl fun v _ => ?_
        rw [← sum_mul]
        exact mul_div_cancel₀ _ (mass_pos_of_pos hν ⟨v, mem_fiber_self Φ' v⟩).ne'

end CycleCutoff
