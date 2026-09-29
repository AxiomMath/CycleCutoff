/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.FiniteProbability.CondExpPullOut

/-!
# The law of total variance

Let `ν` be a strictly positive weight vector on a finite type `Ω`, let `Φ : Ω → Y` and
`f : Ω → ℝ`. The variance of `f` splits into the mean conditional variance and the variance of
the conditional expectation:
`Var_ν(f) = 𝔼_ν[Var_ν(f ∣ Φ)] + Var_ν(𝔼_ν[f ∣ Φ])`. This is the finite, real-weighted analogue
of `ProbabilityTheory.integral_condVar_add_variance_condExp`.

Writing `f̄ = 𝔼_ν[f ∣ Φ]`, one expands
`(f - 𝔼_ν f)² = (f - f̄)² + 2 (f̄ - 𝔼_ν f)(f - f̄) + (f̄ - 𝔼_ν f)²`.
The cross term has mean zero because `f̄ - 𝔼_ν f` is constant on each fibre of `Φ`, and
`𝔼_ν f̄ = 𝔼_ν f`; both facts are instances of the identity
`𝔼_ν[h · 𝔼_ν[g ∣ Φ]] = 𝔼_ν[h · g]` for `h` constant on the fibres of `Φ`.

## Main results

* `CycleCutoff.variance_eq_expectation_condVar_add`: the law of total variance.
-/

public section

open Finset

namespace CycleCutoff

variable {Ω Y : Type*} [Fintype Ω]

/-- **Law of total variance.** For a strictly positive weight vector `ν`,
`Var_ν(f) = 𝔼_ν[Var_ν(f ∣ Φ)] + Var_ν(𝔼_ν[f ∣ Φ])`. -/
@[cycle_cutoff "lem_var_decomposition"]
theorem variance_eq_expectation_condVar_add (ν : Ω → ℝ) (hν : ∀ z, 0 < ν z)
    (Φ : Ω → Y) (f : Ω → ℝ) :
    variance ν f = expectation ν (condVar ν Φ f) + variance ν (condExp ν Φ f) := by
  obtain ⟨h, hh⟩ := exists_condExp_eq_comp ν Φ f
  set fb := condExp ν Φ f with hfb
  have hEfb : expectation ν fb = expectation ν f := expectation_condExp ν hν Φ f
  set m := expectation ν f
  have hcross : expectation ν (fun z => (fb z - m) * (f z - fb z)) = 0 := by
    have := expectation_mul_condExp ν hν Φ (fun y => h y - m) f
    simp only [← hh, ← hfb] at this
    have h1 : (fun z => (fb z - m) * (f z - fb z)) =
        fun z => (fb z - m) * f z - (fb z - m) * fb z := by
      funext z; ring
    rw [h1, expectation_sub, this, sub_self]
  have hcv : expectation ν (condVar ν Φ f) = expectation ν (fun z => (f z - fb z) ^ 2) :=
    expectation_condExp ν hν Φ _
  have hexp : (fun z => (f z - m) ^ 2) = fun z =>
      ((f z - fb z) ^ 2 + 2 * ((fb z - m) * (f z - fb z))) + (fb z - m) ^ 2 := by
    funext z; ring
  rw [variance, variance, hEfb, hcv, hexp, expectation_add, expectation_add,
    expectation_const_mul, hcross]
  ring

end CycleCutoff
