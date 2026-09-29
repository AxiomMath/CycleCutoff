/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.PoincareVarianceDecay
public import CycleCutoff.Generator.SemigroupSymmetric
public import CycleCutoff.Generator.SemigroupRowsum

/-!
# Decay of correlations under a Poincaré inequality

Let `𝒯` be an involution family on `Ω` and `A > 0` with `Var_u(f) ≤ A 𝒟_𝒯(f)` for all `f`. If
`𝔼_u[g] = 0`, then `|⟨g, P^𝒯_t g⟩_u| ≤ e^{-t/A} ⟨g, g⟩_u` for all `t ≥ 0`.

## Main results

* `CycleCutoff.variance_eq_innerP_self_of_expectation_eq_zero`: `Var_ν(h) = ⟨h, h⟩_ν` when
  `𝔼_ν[h] = 0`.
* `CycleCutoff.InvFamily.innerP_semigroup_mulVec_comm`: `⟨f, P_s k⟩_u = ⟨P_s f, k⟩_u`.
* `CycleCutoff.InvFamily.abs_innerP_semigroup_le`: the decay of correlations.
-/

public section

open Finset Matrix

namespace CycleCutoff

variable {Ω : Type*} [Fintype Ω]

/-- For a mean-zero function the variance is the squared norm: `Var_ν(h) = ⟨h, h⟩_ν`. -/
theorem variance_eq_innerP_self_of_expectation_eq_zero {ν : Ω → ℝ} {h : Ω → ℝ}
    (hh : expectation ν h = 0) : variance ν h = innerP ν h h := by
  simp only [variance, hh, sub_zero, innerP, sq]

variable [DecidableEq Ω]

namespace InvFamily

variable {ι : Type*} [Fintype ι] (𝒯 : InvFamily ι Ω)

/-- The semigroup is self-adjoint for the uniform inner product:
`⟨f, P^𝒯_s k⟩_u = ⟨P^𝒯_s f, k⟩_u`. -/
theorem innerP_semigroup_mulVec_comm (s : ℝ) (f k : Ω → ℝ) :
    innerP (unif Ω) f (𝒯.semigroup s *ᵥ k) = innerP (unif Ω) (𝒯.semigroup s *ᵥ f) k := by
  have key : f ⬝ᵥ (𝒯.semigroup s *ᵥ k) = (𝒯.semigroup s *ᵥ f) ⬝ᵥ k := by
    rw [dotProduct_mulVec, ← mulVec_transpose, (𝒯.isSymm_semigroup s).eq]
  simp only [innerP, expectation_unif]
  exact congrArg _ key

/-- **Decay of correlations under a Poincaré inequality.** If `Var_u(f) ≤ A 𝒟_𝒯(f)` for all `f` and
`𝔼_u[g] = 0`, then `|⟨g, P^𝒯_t g⟩_u| ≤ e^{-t/A} ⟨g, g⟩_u` for `t ≥ 0`. -/
@[cycle_cutoff "lem_correlation_decay"]
theorem abs_innerP_semigroup_le (A : ℝ) (hA : 0 < A)
    (hP : ∀ f : Ω → ℝ, variance (unif Ω) f ≤ A * 𝒯.dirichletForm f)
    (g : Ω → ℝ) (hg : expectation (unif Ω) g = 0) {t : ℝ} (ht : 0 ≤ t) :
    |innerP (unif Ω) g (𝒯.semigroup t *ᵥ g)| ≤ Real.exp (-t / A) * innerP (unif Ω) g g := by
  set h := 𝒯.semigroup (t / 2) *ᵥ g
  have hh : expectation (unif Ω) h = 0 := by
    rw [𝒯.expectation_semigroup_mulVec, hg]
  have hsplit : innerP (unif Ω) g (𝒯.semigroup t *ᵥ g) = variance (unif Ω) h := by
    rw [variance_eq_innerP_self_of_expectation_eq_zero hh, ← 𝒯.innerP_semigroup_mulVec_comm,
      mulVec_mulVec, InvFamily.semigroup, InvFamily.semigroup, ← semigroup_add, add_halves]
  have hdecay := 𝒯.variance_semigroup_le A hA hP g (t := t / 2) (by positivity)
  rw [variance_eq_innerP_self_of_expectation_eq_zero hg,
    show -2 * (t / 2) / A = -t / A by ring] at hdecay
  rw [hsplit, abs_of_nonneg (by
    simp only [variance]
    exact sum_nonneg fun z _ => mul_nonneg (by simp [unif]) (sq_nonneg _))]
  exact hdecay

end InvFamily

end CycleCutoff
