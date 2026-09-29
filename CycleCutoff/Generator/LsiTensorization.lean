/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.FiniteProbability.EntChainRule
public import CycleCutoff.Generator.DirichletFormula

/-!
# Tensorization of the log-Sobolev inequality

Let `𝒯₁` and `𝒯₂` be involution families on finite sets `Ω₁` and `Ω₂`, and let `𝒯₁.prod 𝒯₂` be the
family on `Ω₁ × Ω₂` made of the maps `T¹_e × id` and `id × T²_e`. If
`Ent_{u_{Ω_i}}(f²) ≤ A 𝒟_{𝒯_i}(f)` for `i = 1, 2` and every `f`, then
`Ent_{u_{Ω₁ × Ω₂}}(F²) ≤ A 𝒟_{𝒯₁.prod 𝒯₂}(F)` for every `F : Ω₁ × Ω₂ → ℝ`.

## Main results

* `CycleCutoff.expectation_unif_prod`: the uniform expectation on `Ω₁ × Ω₂` is an iterated uniform
  expectation.
* `CycleCutoff.condExp_unif_prod_fst`, `CycleCutoff.condEnt_unif_prod_fst`: conditioning the
  uniform measure on the first coordinate.
* `CycleCutoff.sq_sqrt_sub_sqrt_le`: the reverse triangle inequality in `L²(ν)`.
* `CycleCutoff.InvFamily.dirichletForm_prod`: the Dirichlet form of a product family.
* `CycleCutoff.InvFamily.ent_sq_le_prod`: tensorization of the log-Sobolev inequality.
-/

public section

open Finset

namespace CycleCutoff

section Expectation

variable {Ω Ω₁ Ω₂ : Type*} [Fintype Ω] [Fintype Ω₁] [Fintype Ω₂]

/-- The uniform expectation on `Ω₁ × Ω₂` is the iterated expectation, first coordinate
outermost. -/
theorem expectation_unif_prod (h : Ω₁ × Ω₂ → ℝ) :
    expectation (unif (Ω₁ × Ω₂)) h =
      expectation (unif Ω₁) (fun a => expectation (unif Ω₂) (fun b => h (a, b))) := by
  simp only [expectation_unif, Fintype.card_prod, Nat.cast_mul, mul_inv, mul_sum,
    Fintype.sum_prod_type, mul_assoc]

/-- The uniform expectation on `Ω₁ × Ω₂` is the iterated expectation, second coordinate
outermost. -/
theorem expectation_unif_prod_right (h : Ω₁ × Ω₂ → ℝ) :
    expectation (unif (Ω₁ × Ω₂)) h =
      expectation (unif Ω₂) (fun b => expectation (unif Ω₁) (fun a => h (a, b))) := by
  simp only [expectation_unif, Fintype.card_prod, Nat.cast_mul, mul_inv, mul_sum,
    Fintype.sum_prod_type_right]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

/-- The uniform expectation on `Ω₁ × Ω₂` of a function of the first coordinate. -/
theorem expectation_unif_prod_fst [Nonempty Ω₂] (h : Ω₁ → ℝ) :
    expectation (unif (Ω₁ × Ω₂)) (fun z => h z.1) = expectation (unif Ω₁) h := by
  simp only [expectation_unif_prod, isProbVec_unif.expectation_const]

/-- The uniform entropy on `Ω₁ × Ω₂` of a function of the first coordinate. -/
theorem ent_unif_prod_fst [Nonempty Ω₂] (h : Ω₁ → ℝ) :
    ent (unif (Ω₁ × Ω₂)) (fun z => h z.1) = ent (unif Ω₁) h := by
  rw [ent, ent, expectation_unif_prod_fst h,
    expectation_unif_prod_fst (fun a => h a * Real.log (h a))]

/-- A sum over the fibre of `Prod.fst` through `z` is a sum over the slice `{z.1} × Ω₂`. -/
theorem sum_fiber_fst (z : Ω₁ × Ω₂) (f : Ω₁ × Ω₂ → ℝ) :
    ∑ w ∈ fiber Prod.fst z, f w = ∑ b, f (z.1, b) := by
  classical
  simp only [fiber, sum_filter, Fintype.sum_prod_type]
  rw [sum_comm]
  simp

/-- Conditioning the uniform measure on `Ω₁ × Ω₂` on the first coordinate: the conditional
expectation at `z` is the uniform mean over the slice `{z.1} × Ω₂`. -/
theorem condExp_unif_prod_fst (f : Ω₁ × Ω₂ → ℝ) (z : Ω₁ × Ω₂) :
    condExp (unif (Ω₁ × Ω₂)) Prod.fst f z = expectation (unif Ω₂) (fun b => f (z.1, b)) := by
  have : Nonempty Ω₁ := ⟨z.1⟩
  have : Nonempty Ω₂ := ⟨z.2⟩
  have h₁ : (Fintype.card Ω₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h₂ : (Fintype.card Ω₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [condExp_apply, mass, sum_fiber_fst, sum_fiber_fst, expectation_unif]
  simp only [unif_apply, ← mul_sum, sum_const, card_univ, nsmul_eq_mul, Fintype.card_prod,
    Nat.cast_mul]
  field_simp

/-- Conditioning the uniform measure on `Ω₁ × Ω₂` on the first coordinate: the conditional entropy
at `z` is the uniform entropy over the slice `{z.1} × Ω₂`. -/
theorem condEnt_unif_prod_fst (φ : Ω₁ × Ω₂ → ℝ) (z : Ω₁ × Ω₂) :
    condEnt (unif (Ω₁ × Ω₂)) Prod.fst φ z = ent (unif Ω₂) (fun b => φ (z.1, b)) := by
  change condExp _ Prod.fst (fun w => φ w * Real.log (φ w)) z -
    condExp _ Prod.fst φ z * Real.log (condExp _ Prod.fst φ z) = _
  rw [condExp_unif_prod_fst, condExp_unif_prod_fst]
  rfl

/-- The reverse triangle inequality in `L²(ν)`: `(‖f‖_{L²(ν)} - ‖g‖_{L²(ν)})² ≤ ‖f - g‖²_{L²(ν)}`
for a non-negative weight vector `ν`. -/
theorem sq_sqrt_sub_sqrt_le {ν : Ω → ℝ} (hν : ∀ z, 0 ≤ ν z) (f g : Ω → ℝ) :
    (√(expectation ν (fun z => f z ^ 2)) - √(expectation ν (fun z => g z ^ 2))) ^ 2 ≤
      expectation ν (fun z => (f z - g z) ^ 2) := by
  have hP : 0 ≤ expectation ν (fun z => f z ^ 2) := expectation_nonneg hν fun _ => sq_nonneg _
  have hQ : 0 ≤ expectation ν (fun z => g z ^ 2) := expectation_nonneg hν fun _ => sq_nonneg _
  have hexp : expectation ν (fun z => (f z - g z) ^ 2) = expectation ν (fun z => f z ^ 2) +
      expectation ν (fun z => g z ^ 2) - 2 * expectation ν (fun z => f z * g z) := by
    simp only [expectation, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun z _ => by ring
  have hCS : expectation ν (fun z => f z * g z) ^ 2 ≤
      expectation ν (fun z => f z ^ 2) * expectation ν (fun z => g z ^ 2) := by
    have key := sum_mul_sq_le_sq_mul_sq univ (fun z => √(ν z) * f z) (fun z => √(ν z) * g z)
    have e₁ : ∀ z, √(ν z) * f z * (√(ν z) * g z) = ν z * (f z * g z) := fun z => by
      rw [mul_mul_mul_comm, Real.mul_self_sqrt (hν z)]
    have e₂ : ∀ z (u : ℝ), (√(ν z) * u) ^ 2 = ν z * u ^ 2 := fun z u => by
      rw [mul_pow, Real.sq_sqrt (hν z)]
    simpa only [expectation, e₁, e₂] using key
  have hR : expectation ν (fun z => f z * g z) ≤
      √(expectation ν (fun z => f z ^ 2)) * √(expectation ν (fun z => g z ^ 2)) := by
    rw [← Real.sqrt_mul hP]
    exact (le_abs_self _).trans (Real.abs_le_sqrt hCS)
  rw [hexp, sub_sq, Real.sq_sqrt hP, Real.sq_sqrt hQ]
  linarith

end Expectation

namespace InvFamily

variable {ι₁ ι₂ Ω₁ Ω₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype Ω₁] [Fintype Ω₂]

/-- The Dirichlet form of a product family is the sum of the averaged Dirichlet forms of the
factors along the slices: `𝒟_{𝒯₁ × 𝒯₂}(F) = 𝔼_{ω₂} 𝒟_{𝒯₁}(F(·, ω₂)) + 𝔼_{ω₁} 𝒟_{𝒯₂}(F(ω₁, ·))`. -/
theorem dirichletForm_prod (𝒯₁ : InvFamily ι₁ Ω₁) (𝒯₂ : InvFamily ι₂ Ω₂)
    (F : Ω₁ × Ω₂ → ℝ) :
    (𝒯₁.prod 𝒯₂).dirichletForm F =
      expectation (unif Ω₂) (fun b => 𝒯₁.dirichletForm (fun a => F (a, b))) +
      expectation (unif Ω₁) (fun a => 𝒯₂.dirichletForm (fun b => F (a, b))) := by
  simp only [dirichletForm_eq, Fintype.sum_sum_type, mul_add, expectation_const_mul,
    expectation_sum]
  congr 2 <;> refine sum_congr rfl fun e _ => ?_
  · exact expectation_unif_prod_right _
  · exact expectation_unif_prod _

/-- **Tensorization of the log-Sobolev inequality.** If `Ent_{u_{Ω_i}}(f²) ≤ A 𝒟_{𝒯_i}(f)` for
`i = 1, 2` and all `f`, then `Ent_{u_{Ω₁ × Ω₂}}(F²) ≤ A 𝒟_{𝒯₁.prod 𝒯₂}(F)` for all
`F : Ω₁ × Ω₂ → ℝ`. -/
@[cycle_cutoff "lem_lsi_tensorization"]
theorem ent_sq_le_prod (𝒯₁ : InvFamily ι₁ Ω₁) (𝒯₂ : InvFamily ι₂ Ω₂) (A : ℝ) (hA : 0 ≤ A)
    (h₁ : ∀ f : Ω₁ → ℝ, ent (unif Ω₁) (fun z => f z ^ 2) ≤ A * 𝒯₁.dirichletForm f)
    (h₂ : ∀ f : Ω₂ → ℝ, ent (unif Ω₂) (fun z => f z ^ 2) ≤ A * 𝒯₂.dirichletForm f)
    (F : Ω₁ × Ω₂ → ℝ) :
    ent (unif (Ω₁ × Ω₂)) (fun z => F z ^ 2) ≤ A * (𝒯₁.prod 𝒯₂).dirichletForm F := by
  rcases isEmpty_or_nonempty Ω₂ with hΩ₂ | hΩ₂
  · simp [ent, expectation, dirichletForm, innerP]
  have hu₁ : ∀ a, 0 ≤ unif Ω₁ a := fun _ => inv_nonneg.2 (Nat.cast_nonneg _)
  have hu₂ : ∀ b, 0 ≤ unif Ω₂ b := fun _ => inv_nonneg.2 (Nat.cast_nonneg _)
  have hν : ∀ z, 0 < unif (Ω₁ × Ω₂) z := unif_pos
  set η : Ω₁ → ℝ := fun a => √(expectation (unif Ω₂) (fun b => F (a, b) ^ 2)) with hη
  have hcondExp : condExp (unif (Ω₁ × Ω₂)) Prod.fst (fun z => F z ^ 2) = fun z => η z.1 ^ 2 := by
    funext z
    rw [condExp_unif_prod_fst, hη,
      Real.sq_sqrt (expectation_nonneg hu₂ fun _ => sq_nonneg _)]
  have hmarg : ent (unif (Ω₁ × Ω₂)) (condExp (unif (Ω₁ × Ω₂)) Prod.fst (fun z => F z ^ 2)) ≤
      A * expectation (unif Ω₂) (fun b => 𝒯₁.dirichletForm (fun a => F (a, b))) := by
    rw [hcondExp, ent_unif_prod_fst (fun a => η a ^ 2)]
    refine (h₁ η).trans (mul_le_mul_of_nonneg_left ?_ hA)
    simp only [dirichletForm_eq, expectation_const_mul, expectation_sum]
    refine mul_le_mul_of_nonneg_left (sum_le_sum fun e _ => ?_) (by norm_num)
    calc expectation (unif Ω₁) (fun a => (η (𝒯₁.T e a) - η a) ^ 2)
        ≤ expectation (unif Ω₁)
            (fun a => expectation (unif Ω₂) (fun b => (F (𝒯₁.T e a, b) - F (a, b)) ^ 2)) :=
          expectation_mono hu₁ fun a => sq_sqrt_sub_sqrt_le hu₂ _ _
      _ = _ := (expectation_unif_prod (fun z => (F (𝒯₁.T e z.1, z.2) - F z) ^ 2)).symm.trans
          (expectation_unif_prod_right _)
  have hcond : expectation (unif (Ω₁ × Ω₂)) (condEnt (unif (Ω₁ × Ω₂)) Prod.fst
      (fun z => F z ^ 2)) ≤
      A * expectation (unif Ω₁) (fun a => 𝒯₂.dirichletForm (fun b => F (a, b))) := by
    have hce : condEnt (unif (Ω₁ × Ω₂)) Prod.fst (fun z => F z ^ 2) =
        fun z => ent (unif Ω₂) (fun b => F (z.1, b) ^ 2) :=
      funext fun z => condEnt_unif_prod_fst _ z
    rw [hce, expectation_unif_prod_fst (fun a => ent (unif Ω₂) (fun b => F (a, b) ^ 2)),
      ← expectation_const_mul]
    exact expectation_mono hu₁ fun a => h₂ _
  rw [ent_eq_ent_condExp_add _ hν Prod.fst, dirichletForm_prod, mul_add]
  exact add_le_add hmarg hcond

end InvFamily

end CycleCutoff
