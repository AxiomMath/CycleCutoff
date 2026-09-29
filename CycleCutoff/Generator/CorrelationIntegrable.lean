/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.CorrelationDecay
public import CycleCutoff.Generator.SemigroupDeriv
public import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Integrability of correlations under a Poincaré inequality

Let `𝒯` be an involution family on `Ω` and `A > 0` with `Var_u(f) ≤ A 𝒟_𝒯(f)` for all `f`. If
`𝔼_u[g] = 0`, then `t ↦ ⟨g, P^𝒯_t g⟩_u` is integrable on `[0, ∞)`.

## Main results

* `CycleCutoff.InvFamily.continuous_innerP_semigroup`: `t ↦ ⟨f, P^𝒯_t k⟩_u` is continuous.
* `CycleCutoff.InvFamily.integrableOn_innerP_semigroup`: the integrability of correlations.

## Implementation notes

Integrability on `[0, ∞)` is stated on `Set.Ioi 0`, which differs from `Set.Ici 0` by a null set.
-/

public section

open Finset Matrix MeasureTheory

namespace CycleCutoff

namespace InvFamily

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [DecidableEq Ω] (𝒯 : InvFamily ι Ω)

/-- The correlation `t ↦ ⟨f, P^𝒯_t k⟩_u` is continuous. -/
theorem continuous_innerP_semigroup (f k : Ω → ℝ) :
    Continuous fun t => innerP (unif Ω) f (𝒯.semigroup t *ᵥ k) := by
  have hentry : ∀ z w : Ω, Continuous fun t => 𝒯.semigroup t z w := fun z w =>
    continuous_iff_continuousAt.2 fun t =>
      (hasDerivAt_semigroup_apply 𝒯.rateMatrix t z w).continuousAt
  simp only [innerP, expectation, mulVec, dotProduct]
  fun_prop

/-- **Integrability of correlations under a Poincaré inequality.** If `Var_u(f) ≤ A 𝒟_𝒯(f)` for all
`f` and `𝔼_u[g] = 0`, then `t ↦ ⟨g, P^𝒯_t g⟩_u` is integrable on `[0, ∞)`. -/
@[cycle_cutoff "lem_correlation_integrable"]
theorem integrableOn_innerP_semigroup (A : ℝ) (hA : 0 < A)
    (hP : ∀ f : Ω → ℝ, variance (unif Ω) f ≤ A * 𝒯.dirichletForm f)
    (g : Ω → ℝ) (hg : expectation (unif Ω) g = 0) :
    IntegrableOn (fun t => innerP (unif Ω) g (𝒯.semigroup t *ᵥ g)) (Set.Ioi 0) := by
  have hdom : IntegrableOn (fun t => Real.exp (-(1 / A) * t) * innerP (unif Ω) g g)
      (Set.Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (b := 1 / A) (by positivity)).mul_const _
  refine hdom.mono' (𝒯.continuous_innerP_semigroup g g).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, show -(1 / A) * t = -t / A by ring]
  exact 𝒯.abs_innerP_semigroup_le A hA hP g hg (le_of_lt ht)

end InvFamily

end CycleCutoff
