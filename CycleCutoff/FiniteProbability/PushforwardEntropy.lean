/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.FiniteProbability.PushforwardExpectation

/-!
# Entropy against a push-forward

For a real weight vector `ν` on a finite type `Ω`, a map `Φ : Ω → Y` to a finite type and a
function `h : Y → ℝ`, the entropy of `h ∘ Φ` under `ν` equals the entropy of `h` under the
push-forward `Φ_* ν`: `Ent_ν(h ∘ Φ) = Ent_{Φ_* ν}(h)`. Since
`(h ∘ Φ) log (h ∘ Φ) = (h log h) ∘ Φ`, both expectations in the definition of entropy transfer
along `Φ`.

## Main results

* `CycleCutoff.ent_comp`: `Ent_ν(h ∘ Φ) = Ent_{Φ_* ν}(h)`.

## Implementation notes

No sign condition is imposed on `ν` or `h`: `Real.log` is total, and the identity holds for
arbitrary real `ν` and `h`.
-/

public section

namespace CycleCutoff

variable {Ω Y : Type*} [Fintype Ω] [Fintype Y]

/-- **Entropy against a push-forward.** For a function `h ∘ Φ` factoring through `Φ`,
`Ent_ν(h ∘ Φ) = Ent_{Φ_* ν}(h)`. -/
@[cycle_cutoff "lem_pushforward_entropy"]
theorem ent_comp (ν : Ω → ℝ) (Φ : Ω → Y) (h : Y → ℝ) :
    ent ν (fun z => h (Φ z)) = ent (pushforward Φ ν) h := by
  simp only [ent]
  rw [expectation_comp ν Φ h, expectation_comp ν Φ fun y => h y * Real.log (h y)]

end CycleCutoff
