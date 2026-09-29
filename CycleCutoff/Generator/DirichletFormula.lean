/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.Defs

/-!
# The Dirichlet form of an involution family as a sum of squared increments

For an involution family `𝒯 = (T_e)_{e ∈ ι}` on a finite set `Ω` and `f : Ω → ℝ`, the Dirichlet
form `𝒟_𝒯(f) = ⟨f, -L_𝒯 f⟩_{u_Ω}` equals `½ ∑_e 𝔼_{u_Ω}[(f ∘ T_e - f)²]`.

## Main results

* `CycleCutoff.InvFamily.sum_sq_sub_T`: `∑_z (f(T_e z) - f z)² = 2 ∑_z f z (f z - f(T_e z))`.
* `CycleCutoff.InvFamily.dirichletForm_eq`: the Dirichlet formula.
* `CycleCutoff.InvFamily.dirichletForm_nonneg`: `0 ≤ 𝒟_𝒯(f)`.
-/

public section

open Finset

namespace CycleCutoff

namespace InvFamily

variable {ι Ω : Type*} [Fintype Ω] (𝒯 : InvFamily ι Ω)

/-- The squared increments of `f` along an involution `T_e` sum to twice
`∑_z f(z) (f(z) - f(T_e z))`. -/
theorem sum_sq_sub_T (e : ι) (f : Ω → ℝ) :
    ∑ z, (f (𝒯.T e z) - f z) ^ 2 = 2 * ∑ z, f z * (f z - f (𝒯.T e z)) := by
  have h : ∑ z, f (𝒯.T e z) ^ 2 = ∑ z, f z ^ 2 :=
    Equiv.sum_comp (Equiv.ofBijective _ (𝒯.bijective e)) (fun z => f z ^ 2)
  calc ∑ z, (f (𝒯.T e z) - f z) ^ 2
      = ∑ z, (f (𝒯.T e z) ^ 2 - f z ^ 2 + 2 * (f z * (f z - f (𝒯.T e z)))) :=
        sum_congr rfl fun z _ => by ring
    _ = 2 * ∑ z, f z * (f z - f (𝒯.T e z)) := by
        rw [sum_add_distrib, sum_sub_distrib, h, ← mul_sum]
        ring

variable [Fintype ι]

/-- **Dirichlet formula.** `𝒟_𝒯(f) = ½ ∑_e 𝔼_{u_Ω}[(f ∘ T_e - f)²]`. -/
@[cycle_cutoff "lem_dirichlet_formula"]
theorem dirichletForm_eq (f : Ω → ℝ) :
    𝒯.dirichletForm f =
      (1 / 2) * ∑ e, expectation (unif Ω) (fun z => (f (𝒯.T e z) - f z) ^ 2) := by
  simp only [dirichletForm, innerP, expectation, unif, generator, ← mul_sum,
    𝒯.sum_sq_sub_T]
  rw [sum_comm (f := fun e z => f z * (f z - f (𝒯.T e z)))]
  simp only [mul_neg, mul_sum, ← sum_neg_distrib]
  exact sum_congr rfl fun z _ => sum_congr rfl fun e _ => by ring

/-- The Dirichlet form is non-negative: `0 ≤ 𝒟_𝒯(f)`. -/
theorem dirichletForm_nonneg (f : Ω → ℝ) : 0 ≤ 𝒯.dirichletForm f := by
  rw [𝒯.dirichletForm_eq]
  exact mul_nonneg (by norm_num) (sum_nonneg fun e _ =>
    expectation_nonneg (fun _ => inv_nonneg.2 (Nat.cast_nonneg _)) fun _ => sq_nonneg _)

end InvFamily

end CycleCutoff
