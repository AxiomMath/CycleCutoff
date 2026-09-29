/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.CorrelationIntegrable
public import CycleCutoff.Generator.PoissonSolvable
public import CycleCutoff.Generator.HMinusOneAttained
public import CycleCutoff.Generator.PoincareVarianceDecay
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The integrated correlation is the inverse-generator norm

Let `𝒯` be an involution family on `Ω` and `A > 0` with `Var_u(f) ≤ A 𝒟_𝒯(f)` for all `f`. If
`𝔼_u[g] = 0`, then `∫_0^∞ ⟨g, P^𝒯_t g⟩_u dt = ‖g‖²_{-1,𝒯}`.

## Main results

* `CycleCutoff.InvFamily.hasDerivAt_innerP_semigroup`: `d/dt ⟨f, P^𝒯_t k⟩_u = ⟨f, P^𝒯_t L_𝒯 k⟩_u`.
* `CycleCutoff.InvFamily.tendsto_semigroup_mulVec_apply`: under a Poincaré inequality,
  `(P^𝒯_t f)(z) → 𝔼_u[f]` as `t → ∞`.
* `CycleCutoff.InvFamily.integral_innerP_semigroup`: the integrated correlation is the
  inverse-generator norm.

## Implementation notes

The integral over `[0, ∞)` is taken over `Set.Ioi 0`, which differs from `Set.Ici 0` by a null set.
-/

public section

open Finset Matrix MeasureTheory Filter Topology

namespace CycleCutoff

/-- A single deviation is controlled by the uniform variance: `(f z - 𝔼_u[f])² ≤ |Ω| Var_u(f)`. -/
theorem sq_sub_expectation_le_card_mul_variance {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (z : Ω) :
    (f z - expectation (unif Ω) f) ^ 2 ≤ Fintype.card Ω * variance (unif Ω) f := by
  have hn : (0 : ℝ) < Fintype.card Ω := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨z⟩)
  unfold variance
  set m := expectation (unif Ω) f
  rw [expectation_unif, ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
  exact Finset.single_le_sum (f := fun w => (f w - m) ^ 2)
    (fun w _ => sq_nonneg _) (Finset.mem_univ z)

namespace InvFamily

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [DecidableEq Ω] (𝒯 : InvFamily ι Ω)

/-- The correlation `t ↦ ⟨f, P^𝒯_t k⟩_u` has derivative `⟨f, P^𝒯_t L_𝒯 k⟩_u`. -/
theorem hasDerivAt_innerP_semigroup (f k : Ω → ℝ) (t : ℝ) :
    HasDerivAt (fun s => innerP (unif Ω) f (𝒯.semigroup s *ᵥ k))
      (innerP (unif Ω) f (𝒯.semigroup t *ᵥ 𝒯.generator k)) t := by
  have hentry : ∀ z, HasDerivAt (fun s => (𝒯.semigroup s *ᵥ k) z)
      ((𝒯.semigroup t *ᵥ 𝒯.generator k) z) t := fun z => by
    rw [← rateMatrix_mulVec, mulVec_mulVec]
    exact HasDerivAt.fun_sum fun w _ =>
      (hasDerivAt_semigroup_apply 𝒯.rateMatrix t z w).mul_const (k w)
  simp only [innerP, expectation]
  exact HasDerivAt.fun_sum fun z _ => ((hentry z).const_mul (f z)).const_mul (unif Ω z)

/-- Under a Poincaré inequality `Var_u(f) ≤ A 𝒟_𝒯(f)` with `A > 0`, the semigroup drives every
function to its uniform mean: `(P^𝒯_t f)(z) → 𝔼_u[f]` as `t → ∞`. -/
theorem tendsto_semigroup_mulVec_apply (A : ℝ) (hA : 0 < A)
    (hP : ∀ f : Ω → ℝ, variance (unif Ω) f ≤ A * 𝒯.dirichletForm f) (f : Ω → ℝ) (z : Ω) :
    Tendsto (fun t => (𝒯.semigroup t *ᵥ f) z) atTop (𝓝 (expectation (unif Ω) f)) := by
  have hexp : Tendsto (fun t : ℝ => Real.exp (-2 * t / A)) atTop (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => 2 * t / A) atTop atTop :=
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).atTop_div_const hA
    refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp h).congr fun t => ?_
    simp only [Function.comp_apply, neg_div, neg_mul]
  have hbound : Tendsto (fun t : ℝ =>
      Real.sqrt (Fintype.card Ω * (Real.exp (-2 * t / A) * variance (unif Ω) f)))
      atTop (𝓝 0) := by
    simpa using ((hexp.mul_const (variance (unif Ω) f)).const_mul
      (Fintype.card Ω : ℝ)).sqrt
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [Real.norm_eq_abs]
  refine Real.abs_le_sqrt ?_
  have h1 := sq_sub_expectation_le_card_mul_variance (𝒯.semigroup t *ᵥ f) z
  rw [𝒯.expectation_semigroup_mulVec] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (𝒯.variance_semigroup_le A hA hP f ht)
    (Nat.cast_nonneg _))

/-- **The integrated correlation is the inverse-generator norm.** If `Var_u(f) ≤ A 𝒟_𝒯(f)` for all
`f` with `A > 0`, and `𝔼_u[g] = 0`, then `∫_0^∞ ⟨g, P^𝒯_t g⟩_u dt = ‖g‖²_{-1,𝒯}`. -/
@[cycle_cutoff "lem_correlation_representation"]
theorem integral_innerP_semigroup (A : ℝ) (hA : 0 < A)
    (hP : ∀ f : Ω → ℝ, variance (unif Ω) f ≤ A * 𝒯.dirichletForm f)
    (g : Ω → ℝ) (hg : expectation (unif Ω) g = 0) :
    ∫ t in Set.Ioi 0, innerP (unif Ω) g (𝒯.semigroup t *ᵥ g) = 𝒯.hMinusOneNormSq g := by
  obtain ⟨u, hu⟩ := 𝒯.exists_neg_generator_eq A hP g hg
  have hLu : 𝒯.generator u = -g := by rw [← hu]; ext z; simp
  set F : ℝ → ℝ := fun t => -innerP (unif Ω) g (𝒯.semigroup t *ᵥ u)
  have hderiv : ∀ t, HasDerivAt F (innerP (unif Ω) g (𝒯.semigroup t *ᵥ g)) t := fun t => by
    have h := (𝒯.hasDerivAt_innerP_semigroup g u t).fun_neg
    rw [hLu, mulVec_neg] at h
    refine h.congr_deriv ?_
    simp [innerP, expectation]
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h : Tendsto (fun t => innerP (unif Ω) g (𝒯.semigroup t *ᵥ u)) atTop
        (𝓝 (innerP (unif Ω) g fun _ => expectation (unif Ω) u)) := by
      simp only [innerP, expectation]
      exact tendsto_finsetSum _ fun z _ =>
        ((𝒯.tendsto_semigroup_mulVec_apply A hA hP u z).const_mul (g z)).const_mul _
    have h0 : innerP (unif Ω) g (fun _ => expectation (unif Ω) u) = 0 := by
      rw [innerP, expectation_mul_const, hg, zero_mul]
    rw [h0] at h
    simpa using h.neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hderiv 0).continuousAt.continuousWithinAt
    (fun t _ => hderiv t) (𝒯.integrableOn_innerP_semigroup A hA hP g hg) hlim,
    𝒯.hMinusOneNormSq_eq hu]
  simp [F, semigroup, semigroup_zero]

end InvFamily

end CycleCutoff
