/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.FiniteProbability.CondExpPullOut

/-!
# The residual of a conditional expectation has smaller second moment

Let `ν` be a strictly positive weight vector on a finite type `Ω`, `Φ : Ω → Y` and
`W : Ω → ℝ`, and put `Ŵ = 𝔼_ν[W ∣ Φ]`. Then `𝔼_ν[(W - Ŵ)²] ≤ 𝔼_ν[W²]`.
Since `Ŵ` is constant on the fibres of `Φ`, it is of the form `h ∘ Φ`, so the pull-out
property gives `𝔼_ν[Ŵ W] = 𝔼_ν[Ŵ²]`, and hence `𝔼_ν[(W - Ŵ)²] = 𝔼_ν[W²] - 𝔼_ν[Ŵ²]`.

## Main results

* `CycleCutoff.expectation_sq_sub_condExp_le`: `𝔼_ν[(W - 𝔼_ν[W ∣ Φ])²] ≤ 𝔼_ν[W²]`.
-/

public section

open Finset

namespace CycleCutoff

variable {Ω Y : Type*} [Fintype Ω]

/-- **Residual bound for conditional expectation**: subtracting `𝔼_ν[W ∣ Φ]` does not
increase the second moment, `𝔼_ν[(W - 𝔼_ν[W ∣ Φ])²] ≤ 𝔼_ν[W²]`. -/
@[cycle_cutoff "lem_cond_exp_residual_bound"]
theorem expectation_sq_sub_condExp_le (ν : Ω → ℝ) (hν : ∀ z, 0 < ν z)
    (Φ : Ω → Y) (W : Ω → ℝ) :
    expectation ν (fun z => (W z - condExp ν Φ W z) ^ 2) ≤ expectation ν (fun z => W z ^ 2) := by
  set g := condExp ν Φ W with hg
  obtain ⟨h, hh⟩ := exists_condExp_eq_comp ν Φ W
  have hcross : expectation ν (fun z => g z * W z) = expectation ν (fun z => g z ^ 2) := by
    have := expectation_mul_condExp ν hν Φ h W
    simp only [← hh, ← hg] at this
    rw [this]
    simp only [sq]
  have hexp : expectation ν (fun z => (W z - g z) ^ 2) =
      expectation ν (fun z => W z ^ 2) - expectation ν (fun z => g z ^ 2) := by
    have : (fun z => (W z - g z) ^ 2) =
        fun z => W z ^ 2 - 2 * (g z * W z) + g z ^ 2 := by
      funext z; ring
    rw [this, expectation_add, expectation_sub, expectation_const_mul, hcross]
    ring
  rw [hexp, sub_le_self_iff]
  exact expectation_nonneg (fun z => (hν z).le) fun z => sq_nonneg _

end CycleCutoff
