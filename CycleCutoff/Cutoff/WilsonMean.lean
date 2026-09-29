/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Cutoff.Defs
public import CycleCutoff.Generator.SemigroupDeriv
public import CycleCutoff.Cutoff.WilsonEigenfunction
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The mean of Wilson's statistic

Under the law `μ_t` of the cycle shuffle started at the identity, Wilson's statistic has mean
`𝔼_{μ_t}[F] = n e^{-λ_n t}`.

## Main results

* `CycleCutoff.hasDerivAt_expectation_muT`: `d/dt 𝔼_{μ_t}[G] = 𝔼_{μ_t}[L G]` for every `G`.
* `CycleCutoff.expectation_muT_wilsonStat`: `𝔼_{μ_t}[F] = n e^{-λ_n t}`.
-/

public section

open Finset Real Matrix

namespace CycleCutoff

variable {n : ℕ} [NeZero n]

/-- For every observable `G`, `d/dt 𝔼_{μ_t}[G] = 𝔼_{μ_t}[L G]`. -/
theorem hasDerivAt_expectation_muT (G : Equiv.Perm (ZMod n) → ℝ) (t : ℝ) :
    HasDerivAt (fun s => expectation (muT n s) G)
      (expectation (muT n t) ((cycleShuffle n).generator G)) t := by
  set Q := (cycleShuffle n).rateMatrix
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ =>
    (hasDerivAt_semigroup_apply Q t 1 σ).mul_const (G σ))
  refine h.congr_deriv ?_
  have hmul := congrFun (Matrix.mulVec_mulVec G (semigroup Q t) Q) 1
  rw [InvFamily.rateMatrix_mulVec] at hmul
  simp only [Matrix.mulVec, dotProduct] at hmul
  rw [← hmul]
  rfl

/-- The mean `m(t) = 𝔼_{μ_t}[F]` satisfies `m'(t) = -λ_n m(t)`. -/
private lemma hasDerivAt_expectation_muT_wilsonStat (t : ℝ) :
    HasDerivAt (fun s => expectation (muT n s) (wilsonStat n))
      (-lambdaN n * expectation (muT n t) (wilsonStat n)) t :=
  (hasDerivAt_expectation_muT (wilsonStat n) t).congr_deriv (by
    rw [generator_wilsonStat, expectation_const_mul])

variable (n) in
/-- The mean of Wilson's statistic under `μ_t` is `𝔼_{μ_t}[F] = n e^{-λ_n t}`. -/
@[cycle_cutoff "lem_F_mean"]
theorem expectation_muT_wilsonStat (t : ℝ) :
    expectation (muT n t) (wilsonStat n) = n * Real.exp (-lambdaN n * t) := by
  set m := fun s => expectation (muT n s) (wilsonStat n)
  set g := fun s => Real.exp (lambdaN n * s) * m s
  have hg : ∀ s, HasDerivAt g 0 s := fun s => by
    have h1 : HasDerivAt (fun s => lambdaN n * s) (lambdaN n) s := by
      simpa using (hasDerivAt_id s).const_mul (lambdaN n)
    exact (h1.exp.fun_mul (hasDerivAt_expectation_muT_wilsonStat (n := n) s)).congr_deriv
      (by ring)
  have hconst := is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt)
    (fun s => (hg s).deriv) t 0
  have h0 : m 0 = n := by
    simp [m, expectation, muT, InvFamily.semigroup, semigroup_zero, Matrix.one_apply]
  rw [neg_mul, Real.exp_neg, eq_mul_inv_iff_mul_eq₀ (Real.exp_ne_zero _), mul_comm]
  simpa [g, h0] using hconst

end CycleCutoff
