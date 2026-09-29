/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.FiniteProbability.PushforwardExpectation

/-!
# Variance against a push-forward

For a real weight vector `ν` on a finite type `Ω`, a map `Φ : Ω → Y` to a finite type and
`h : Y → ℝ`, the variance of `h ∘ Φ` under `ν` equals the variance of `h` under the
push-forward `Φ_* ν`: `Var_ν(h ∘ Φ) = Var_{Φ_* ν}(h)`. The means agree by
`CycleCutoff.expectation_comp`, and then the centred square `(h ∘ Φ - c)²` is itself
`(h - c)² ∘ Φ`, so a second application of the same identity gives the result.

## Main results

* `CycleCutoff.variance_comp`: `Var_ν(h ∘ Φ) = Var_{Φ_* ν}(h)`.
-/

public section

namespace CycleCutoff

variable {Ω Y : Type*} [Fintype Ω] [Fintype Y]

/-- **Variance against a push-forward.** For a function `h ∘ Φ` factoring through `Φ`,
`Var_ν(h ∘ Φ) = Var_{Φ_* ν}(h)`. -/
@[cycle_cutoff "lem_pushforward_variance"]
theorem variance_comp (ν : Ω → ℝ) (Φ : Ω → Y) (h : Y → ℝ) :
    variance ν (fun z => h (Φ z)) = variance (pushforward Φ ν) h := by
  simp only [variance, expectation_comp ν Φ h]
  exact expectation_comp ν Φ fun y => (h y - expectation (pushforward Φ ν) h) ^ 2

end CycleCutoff
