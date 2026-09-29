/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.SemigroupRowsum
public import CycleCutoff.Generator.SemigroupSymmetric
public import CycleCutoff.Generator.SemigroupDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exponential decay of variance under a Poincaré inequality

Let `𝒯` be an involution family on `Ω` and `A > 0` with `Var_u(f) ≤ A 𝒟_𝒯(f)` for all `f`. Then for
all `f` and `t ≥ 0`, `Var_u(P^𝒯_t f) ≤ e^{-2t/A} Var_u(f)`.

## Main results

* `CycleCutoff.hasDerivAt_semigroup_mulVec_apply`: `d/dt (P^Q_t f)(z) = (Q P^Q_t f)(z)`.
* `CycleCutoff.InvFamily.sum_generator`: `∑_z (L_𝒯 g)(z) = 0`.
* `CycleCutoff.InvFamily.expectation_semigroup_mulVec`: `𝔼_u[P^𝒯_t f] = 𝔼_u[f]`.
* `CycleCutoff.InvFamily.variance_semigroup_le`: the variance decay.
-/

public section

open Finset Matrix

namespace CycleCutoff

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The semigroup applied to a vector solves the forward equation entrywise:
`d/dt (P^Q_t f)(z) = (Q P^Q_t f)(z)`. -/
theorem hasDerivAt_semigroup_mulVec_apply (Q : Matrix Ω Ω ℝ) (f : Ω → ℝ) (t : ℝ) (z : Ω) :
    HasDerivAt (fun s => (semigroup Q s *ᵥ f) z) ((Q *ᵥ (semigroup Q t *ᵥ f)) z) t := by
  rw [mulVec_mulVec]
  exact HasDerivAt.fun_sum fun w _ => (hasDerivAt_semigroup_apply' Q t z w).mul_const (f w)

namespace InvFamily

variable {ι : Type*} [Fintype ι] (𝒯 : InvFamily ι Ω)

omit [DecidableEq Ω] in
/-- The values of the generator sum to zero: `∑_z (L_𝒯 g)(z) = 0`. -/
theorem sum_generator (g : Ω → ℝ) : ∑ z, 𝒯.generator g z = 0 := by
  simp only [generator]
  rw [sum_comm]
  refine sum_eq_zero fun e _ => ?_
  rw [sum_sub_distrib, sub_eq_zero]
  exact Equiv.sum_comp (Equiv.ofBijective _ (𝒯.bijective e)) g

/-- The semigroup preserves the uniform mean: `𝔼_u[P^𝒯_t f] = 𝔼_u[f]`. -/
theorem expectation_semigroup_mulVec (t : ℝ) (f : Ω → ℝ) :
    expectation (unif Ω) (𝒯.semigroup t *ᵥ f) = expectation (unif Ω) f := by
  simp only [expectation_unif, mulVec, dotProduct]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun w _ => ?_
  rw [← sum_mul, show ∑ z, 𝒯.semigroup t z w = ∑ z, 𝒯.semigroup t w z from
    sum_congr rfl fun z _ => 𝒯.semigroup_apply_comm t z w, 𝒯.sum_semigroup_apply, one_mul]

/-- **Variance decay under a Poincaré inequality.** If `Var_u(f) ≤ A 𝒟_𝒯(f)` for all `f`, then
`Var_u(P^𝒯_t f) ≤ e^{-2t/A} Var_u(f)` for `t ≥ 0`. -/
@[cycle_cutoff "lem_poincare_variance_decay"]
theorem variance_semigroup_le (A : ℝ) (hA : 0 < A)
    (hP : ∀ f : Ω → ℝ, variance (unif Ω) f ≤ A * 𝒯.dirichletForm f) (f : Ω → ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    variance (unif Ω) (𝒯.semigroup t *ᵥ f) ≤ Real.exp (-2 * t / A) * variance (unif Ω) f := by
  set m := expectation (unif Ω) f
  set g : ℝ → Ω → ℝ := fun s => 𝒯.semigroup s *ᵥ f
  set V : ℝ → ℝ := fun s => expectation (unif Ω) (fun z => (g s z - m) ^ 2)
  have hV : ∀ s, V s = variance (unif Ω) (g s) := fun s => by
    simp only [V, variance, g, 𝒯.expectation_semigroup_mulVec, m]
  have hVd : ∀ s, HasDerivAt V (-2 * 𝒯.dirichletForm (g s)) s := by
    intro s
    have hg : ∀ z, HasDerivAt (fun r => g r z) (𝒯.generator (g s) z) s := fun z => by
      have := hasDerivAt_semigroup_mulVec_apply 𝒯.rateMatrix f s z
      rw [rateMatrix_mulVec] at this
      exact this
    have h := HasDerivAt.fun_sum fun z (_ : z ∈ univ) =>
      (((hg z).sub_const m).fun_pow 2).const_mul (unif Ω z)
    refine h.congr_deriv ?_
    have hL := 𝒯.sum_generator (g s)
    simp only [dirichletForm, innerP, expectation, unif]
    rw [← mul_sum, ← mul_sum]
    have : ∑ z, ((2 : ℕ) : ℝ) * (g s z - m) ^ (2 - 1) * 𝒯.generator (g s) z
        = 2 * ∑ z, g s z * 𝒯.generator (g s) z - 2 * m * ∑ z, 𝒯.generator (g s) z := by
      rw [mul_sum, mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun z _ => by push_cast; ring
    rw [this, hL]
    simp only [mul_neg, sum_neg_distrib]
    ring
  have hψ : Antitone fun s => Real.exp (2 * s / A) * V s := by
    refine antitone_of_hasDerivAt_nonpos (f' := fun s =>
      Real.exp (2 * s / A) * (2 / A) * V s + Real.exp (2 * s / A) * (-2 * 𝒯.dirichletForm (g s)))
      (fun s => ?_) (fun s => ?_)
    · have he : HasDerivAt (fun s => Real.exp (2 * s / A)) (Real.exp (2 * s / A) * (2 / A)) s := by
        have := ((hasDerivAt_id s).const_mul 2).div_const A
        simpa using this.exp
      exact he.mul (hVd s)
    · have hPs := hP (g s)
      rw [← hV] at hPs
      have hVle : 2 / A * V s ≤ 2 * 𝒯.dirichletForm (g s) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hA]
        linarith
      have : Real.exp (2 * s / A) * (2 / A * V s - 2 * 𝒯.dirichletForm (g s)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)
      simp only [Pi.zero_apply]
      linarith
  have h0 := hψ ht
  simp only [mul_zero, zero_div, Real.exp_zero, one_mul] at h0
  have hV0 : V 0 = variance (unif Ω) f := by
    rw [hV]; simp [g, InvFamily.semigroup, semigroup_zero]
  rw [hV0] at h0
  rw [← hV t]
  calc V t = Real.exp (-2 * t / A) * (Real.exp (2 * t / A) * V t) := by
        rw [← mul_assoc, ← Real.exp_add]; ring_nf; simp
    _ ≤ Real.exp (-2 * t / A) * variance (unif Ω) f :=
        mul_le_mul_of_nonneg_left h0 (Real.exp_pos _).le

end InvFamily

end CycleCutoff
