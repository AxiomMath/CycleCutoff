/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.FiniteProbability.CondExpPullOut

/-!
# Conditional variance restricted to an event measurable for the conditioning map

Let `ν` be a strictly positive weight vector on a finite type `Ω`, `Φ : Ω → Y`, and let
`E = Φ⁻¹(E_Y)` be an event determined by `Φ`. For any `f : Ω → ℝ`,
`𝔼_ν[𝟙_E (f - 𝔼_ν[f ∣ Φ])²] = 𝔼_ν[𝟙_E Var_ν(f ∣ Φ)]`.
Since `𝟙_E = 𝟙_{E_Y} ∘ Φ` and `Var_ν(f ∣ Φ) = 𝔼_ν[(f - 𝔼_ν[f ∣ Φ])² ∣ Φ]`, this is the
pull-out property of conditional expectation applied to `(f - 𝔼_ν[f ∣ Φ])²` with the
function `𝟙_{E_Y}` of the conditioning variable.

## Main results

* `CycleCutoff.expectation_indicator_sq_sub_condExp`: the identity above.
-/

public section

namespace CycleCutoff

/-- **Conditional variance on an event determined by `Φ`.** On an event `Φ⁻¹(E)` determined by
the conditioning map `Φ`, the mean squared deviation of `f` from its conditional expectation
equals the mean conditional variance:
`𝔼_ν[𝟙_{Φ⁻¹ E} (f - 𝔼_ν[f ∣ Φ])²] = 𝔼_ν[𝟙_{Φ⁻¹ E} Var_ν(f ∣ Φ)]`. -/
@[cycle_cutoff "lem_cond_var_on_event"]
theorem expectation_indicator_sq_sub_condExp {Ω Y : Type*} [Fintype Ω] (ν : Ω → ℝ)
    (hν : ∀ z, 0 < ν z) (Φ : Ω → Y) (E : Set Y) (f : Ω → ℝ) :
    expectation ν
        (fun z => (Φ ⁻¹' E).indicator (fun _ => (1 : ℝ)) z * (f z - condExp ν Φ f z) ^ 2) =
      expectation ν (fun z => (Φ ⁻¹' E).indicator (fun _ => (1 : ℝ)) z * condVar ν Φ f z) :=
  expectation_mul_condExp ν hν Φ (E.indicator fun _ => 1) fun z => (f z - condExp ν Φ f z) ^ 2

end CycleCutoff
