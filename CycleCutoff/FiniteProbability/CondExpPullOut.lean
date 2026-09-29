/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.FiniteProbability.Defs

/-!
# Pulling a function of the conditioning variable out of a conditional expectation

Let `ν` be a strictly positive weight vector on a finite type `Ω` and `Φ : Ω → Y`. For any
`h : Y → ℝ` and `f : Ω → ℝ`,
`𝔼_ν[(h ∘ Φ) f] = 𝔼_ν[(h ∘ Φ) 𝔼_ν[f ∣ Φ]]`.
Both sides split over the fibres of `Φ`; on the fibre `F` through `w` the conditional
expectation is the constant `ν(F)⁻¹ ∑_{v ∈ F} ν(v) f(v)`, and `ν(F) > 0`, so the fibre
contributes `h(Φ w) ∑_{v ∈ F} ν(v) f(v)` to either side.

## Main results

* `CycleCutoff.expectation_mul_condExp`: the pull-out property of `condExp`.
* `CycleCutoff.expectation_condExp`: the tower property `𝔼_ν[𝔼_ν[f ∣ Φ]] = 𝔼_ν[f]`.
-/

public section

open Finset

namespace CycleCutoff

/-- **Pull-out property of conditional expectation**: a function of the conditioning
variable `Φ` factors through `𝔼_ν[· ∣ Φ]`, i.e.
`𝔼_ν[(h ∘ Φ) f] = 𝔼_ν[(h ∘ Φ) 𝔼_ν[f ∣ Φ]]`. -/
@[cycle_cutoff "lem_cond_exp_pull_out"]
theorem expectation_mul_condExp {Ω Y : Type*} [Fintype Ω] (ν : Ω → ℝ) (hν : ∀ z, 0 < ν z)
    (Φ : Ω → Y) (h : Y → ℝ) (f : Ω → ℝ) :
    expectation ν (fun z => h (Φ z) * f z) =
      expectation ν (fun z => h (Φ z) * condExp ν Φ f z) := by
  classical
  have key : ∀ z, ν z * (h (Φ z) * condExp ν Φ f z) =
      ∑ w, if z ∈ fiber Φ w then
        ν z * h (Φ w) * (ν w * f w) / mass ν (fiber Φ w) else 0 := by
    intro z
    have hfil : (univ.filter fun w => z ∈ fiber Φ w) = fiber Φ z := by
      ext w; simp [mem_fiber, eq_comm]
    simp only [condExp_apply, sum_ite, sum_const_zero, add_zero]
    rw [hfil, mul_div_assoc', mul_div_assoc', mul_sum, mul_sum, sum_div]
    refine sum_congr rfl fun w hw => ?_
    rw [fiber_eq_of_mem hw, mem_fiber.1 hw]
    ring
  simp only [expectation, key]
  rw [sum_comm]
  refine sum_congr rfl fun w _ => ?_
  simp only [sum_ite, sum_const_zero, add_zero, filter_mem_eq_inter, univ_inter]
  rw [← sum_div, ← sum_mul, ← sum_mul]
  have hM : mass ν (fiber Φ w) ≠ 0 := (mass_pos_of_pos hν ⟨w, mem_fiber_self Φ w⟩).ne'
  rw [show ∑ z ∈ fiber Φ w, ν z = mass ν (fiber Φ w) from rfl]
  field_simp

/-- **Tower property**: `𝔼_ν[𝔼_ν[f ∣ Φ]] = 𝔼_ν[f]` for a strictly positive weight vector. -/
theorem expectation_condExp {Ω Y : Type*} [Fintype Ω] (ν : Ω → ℝ) (hν : ∀ z, 0 < ν z)
    (Φ : Ω → Y) (f : Ω → ℝ) : expectation ν (condExp ν Φ f) = expectation ν f := by
  simpa using (expectation_mul_condExp ν hν Φ (fun _ => 1) f).symm

end CycleCutoff
