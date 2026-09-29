/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.FiniteProbability.CondExpPullOut

/-!
# The chain rule for entropy

Let `ν` be a strictly positive weight vector on a finite type `Ω`, let `Φ : Ω → Y`, and let
`φ : Ω → ℝ`. Writing `φ̄ = 𝔼_ν[φ ∣ Φ]`, the entropy splits as
`Ent_ν(φ) = Ent_ν(φ̄) + 𝔼_ν[Ent_ν(φ ∣ Φ)]`.

The proof rests on the tower property `𝔼_ν[𝔼_ν[g ∣ Φ]] = 𝔼_ν[g]`, obtained by exchanging the
order of summation over pairs of points in a common fibre. Since
`Ent_ν(φ ∣ Φ) = 𝔼_ν[φ log φ ∣ Φ] - φ̄ log φ̄` pointwise, the tower property gives
`𝔼_ν[Ent_ν(φ ∣ Φ)] = 𝔼_ν[φ log φ] - 𝔼_ν[φ̄ log φ̄]`, while `Ent_ν(φ̄)` is
`𝔼_ν[φ̄ log φ̄] - 𝔼_ν[φ] log 𝔼_ν[φ]`; adding the two gives `Ent_ν(φ)`.

## Main results

* `CycleCutoff.ent_eq_ent_condExp_add`: `Ent_ν(φ) = Ent_ν(𝔼_ν[φ ∣ Φ]) + 𝔼_ν[Ent_ν(φ ∣ Φ)]`.

## Implementation notes

The identity is purely algebraic: neither the normalisation `∑ z, ν z = 1` nor the
non-negativity of `φ` is used. Strict positivity of `ν` is used only to make every fibre have
non-zero mass, so that each conditional measure is a genuine average.
-/

public section

open Finset

namespace CycleCutoff

variable {Ω Y : Type*} [Fintype Ω]

/-- **Chain rule for entropy.** For a strictly positive weight vector `ν` and a map `Φ`,
`Ent_ν(φ) = Ent_ν(𝔼_ν[φ ∣ Φ]) + 𝔼_ν[Ent_ν(φ ∣ Φ)]`. -/
@[cycle_cutoff "lem_ent_chain_rule"]
theorem ent_eq_ent_condExp_add (ν : Ω → ℝ) (hν : ∀ z, 0 < ν z) (Φ : Ω → Y) (φ : Ω → ℝ) :
    ent ν φ = ent ν (condExp ν Φ φ) + expectation ν (condEnt ν Φ φ) := by
  have hcond : condEnt ν Φ φ = fun z => condExp ν Φ (fun w => φ w * Real.log (φ w)) z -
      condExp ν Φ φ z * Real.log (condExp ν Φ φ z) := rfl
  rw [hcond, expectation_sub, expectation_condExp ν hν, ent, ent,
    expectation_condExp ν hν]
  ring

end CycleCutoff
