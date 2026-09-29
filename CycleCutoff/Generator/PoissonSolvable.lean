/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.HMinusOne
public import CycleCutoff.Generator.SemigroupSymmetric
public import CycleCutoff.Generator.PoincareVarianceDecay
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Solvability of the Poisson equation

Let `𝒯` be an involution family on a finite type `Ω` satisfying a Poincaré inequality
`Var_{u_Ω}(f) ≤ A 𝒟_𝒯(f)`. Then for every `g` of uniform mean zero the Poisson equation
`-L_𝒯 u = g` has a solution.

## Main results

* `CycleCutoff.InvFamily.exists_neg_generator_eq`: under a Poincaré inequality, every mean-zero `g`
  is `-L_𝒯 u` for some `u`.
-/

public section

open Finset Matrix

namespace CycleCutoff

/-- **Solvability of the Poisson equation.** If `Var_{u_Ω}(f) ≤ A 𝒟_𝒯(f)` for all `f`, then for
every `g` with `𝔼_{u_Ω}[g] = 0` there is `u` with `-L_𝒯 u = g`. -/
@[cycle_cutoff "lem_poisson_solvable"]
theorem InvFamily.exists_neg_generator_eq {ι Ω : Type*} [Fintype ι] [Fintype Ω]
    (𝒯 : InvFamily ι Ω) (A : ℝ)
    (hP : ∀ f : Ω → ℝ, variance (unif Ω) f ≤ A * 𝒯.dirichletForm f)
    (g : Ω → ℝ) (hg : expectation (unif Ω) g = 0) :
    ∃ u : Ω → ℝ, (fun z => -𝒯.generator u z) = g := by
  classical
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · exact ⟨0, funext fun z => isEmptyElim z⟩
  set L := Matrix.mulVecLin 𝒯.rateMatrix with hL
  have hLf : ∀ f, L f = 𝒯.generator f := fun f => by
    rw [hL, Matrix.mulVecLin_apply, rateMatrix_mulVec]
  set φ : (Ω → ℝ) →ₗ[ℝ] ℝ := ∑ z, LinearMap.proj z with hφ
  have hφf : ∀ f, φ f = ∑ z, f z := fun f => by simp [hφ]
  have hn : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hker : LinearMap.ker L ≤ ℝ ∙ (fun _ => (1 : ℝ)) := by
    intro f hf
    rw [LinearMap.mem_ker, hLf] at hf
    have hD : 𝒯.dirichletForm f = 0 := by
      simp [dirichletForm, innerP, expectation, hf]
    have hV := hP f
    rw [hD, mul_zero] at hV
    rw [Submodule.mem_span_singleton]
    refine ⟨expectation (unif Ω) f, funext fun z => ?_⟩
    have hterm : ∀ w ∈ Finset.univ, 0 ≤ unif Ω w * (f w - expectation (unif Ω) f) ^ 2 :=
      fun w _ => mul_nonneg (by simp [unif]) (sq_nonneg _)
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hterm).1
      (le_antisymm hV (Finset.sum_nonneg hterm)) z (Finset.mem_univ z)
    have hu : unif Ω z ≠ 0 := by simp [unif]
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hu
    · simp only [Pi.smul_apply, smul_eq_mul, mul_one]
      linarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.1 h]
  have hrange : LinearMap.range L ≤ LinearMap.ker φ := by
    rintro _ ⟨f, rfl⟩
    rw [LinearMap.mem_ker, hφf, hLf, 𝒯.sum_generator]
  have hφsurj : LinearMap.range φ = ⊤ := by
    refine LinearMap.range_eq_top.2 fun c => ⟨fun _ => c / Fintype.card Ω, ?_⟩
    rw [hφf, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have heq : LinearMap.range L = LinearMap.ker φ := by
    refine Submodule.eq_of_le_of_finrank_le hrange ?_
    have h1 := LinearMap.finrank_range_add_finrank_ker L
    have h2 := LinearMap.finrank_range_add_finrank_ker φ
    rw [hφsurj, finrank_top, Module.finrank_self] at h2
    have h3 : Module.finrank ℝ (LinearMap.ker L) ≤ 1 :=
      (Submodule.finrank_mono hker).trans ((finrank_span_le_card _).trans (by simp))
    omega
  have hgmem : g ∈ LinearMap.range L := by
    rw [heq, LinearMap.mem_ker, hφf]
    rw [expectation_unif] at hg
    exact (mul_eq_zero.1 hg).resolve_left (inv_ne_zero hn)
  obtain ⟨v, hv⟩ := hgmem
  refine ⟨-v, funext fun z => ?_⟩
  rw [← hLf, map_neg, Pi.neg_apply, neg_neg, hv]

end CycleCutoff
