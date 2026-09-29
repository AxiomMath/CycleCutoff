/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Cutoff.Defs
public import CycleCutoff.Cutoff.WilsonMean
public import CycleCutoff.Cycle.MuPositive
public import CycleCutoff.Generator.SemigroupDeriv
public import CycleCutoff.Cutoff.WilsonEigenfunction
public import CycleCutoff.Cutoff.WilsonIncrement
public import CycleCutoff.Generator.SemigroupLower
public import CycleCutoff.Generator.SemigroupRowsum
public import CycleCutoff.Cycle.LambdaLower
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The variance of Wilson's statistic

Under the law `μ_t` of the cycle shuffle started at the identity, Wilson's statistic `F`
satisfies `Var_{μ_t}(F) ≤ π² n / 2` for every `t ≥ 0` and `n ≥ 2`.

## Main results

* `CycleCutoff.variance_muT_wilsonStat_le`: `Var_{μ_t}(F) ≤ π² n / 2` for `t ≥ 0`.
-/

public section

open Finset Real

namespace CycleCutoff

variable {n : ℕ} [NeZero n]

/-- The carré du champ identity `L(F²) = Γ - 2λ_n F²` for Wilson's statistic. -/
private lemma generator_wilsonStat_sq (σ : Equiv.Perm (ZMod n)) :
    (cycleShuffle n).generator (fun τ => wilsonStat n τ ^ 2) σ =
      ∑ x : ZMod n, (wilsonStat n ((cycleShuffle n).T x σ) - wilsonStat n σ) ^ 2 +
        -2 * lambdaN n * wilsonStat n σ ^ 2 := by
  have h := congrFun (generator_wilsonStat (n := n)) σ
  simp only [InvFamily.generator] at h ⊢
  have : ∀ x : ZMod n, wilsonStat n ((cycleShuffle n).T x σ) ^ 2 - wilsonStat n σ ^ 2 =
      (wilsonStat n ((cycleShuffle n).T x σ) - wilsonStat n σ) ^ 2 +
        2 * wilsonStat n σ * (wilsonStat n ((cycleShuffle n).T x σ) - wilsonStat n σ) :=
    fun x => by ring
  rw [sum_congr rfl fun x _ => this x, sum_add_distrib, ← mul_sum, h]
  ring

/-- **Variance of Wilson's statistic.** For `n ≥ 2` and `t ≥ 0`, the variance of Wilson's
statistic under `μ_t` is at most `π² n / 2`. -/
@[cycle_cutoff "lem_F_variance_bound"]
theorem variance_muT_wilsonStat_le (hn : 2 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    variance (muT n t) (wilsonStat n) ≤ Real.pi ^ 2 * n / 2 := by
  set F := wilsonStat n
  set l := lambdaN n
  set ε : ℝ := 16 * Real.pi ^ 2 / n
  set Γ : Equiv.Perm (ZMod n) → ℝ :=
    fun σ => ∑ x : ZMod n, (F ((cycleShuffle n).T x σ) - F σ) ^ 2
  set m : ℝ → ℝ := fun s => expectation (muT n s) F
  set E : ℝ → ℝ := fun s => expectation (muT n s) (fun σ => F σ ^ 2)
  set V : ℝ → ℝ := fun s => E s - m s ^ 2
  have hl16 : 16 / (n : ℝ) ^ 2 ≤ l := sixteen_div_sq_le_lambdaN hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (NeZero.pos n)
  have hl : 0 < l := lt_of_lt_of_le (by positivity) hl16
  have hsum : ∀ s, ∑ σ, muT n s σ = 1 := sum_muT
  have hvar : variance (muT n t) F = V t := variance_eq_of_isProbVec (isProbVec_muT ht) F
  have hV : ∀ s, HasDerivAt V (expectation (muT n s) Γ - 2 * l * V s) s := by
    intro s
    have hE : HasDerivAt E (expectation (muT n s) Γ + -2 * l * E s) s := by
      refine (hasDerivAt_expectation_muT (fun σ => F σ ^ 2) s).congr_deriv ?_
      rw [funext (generator_wilsonStat_sq (n := n)), expectation_add, expectation_const_mul]
    have hm : HasDerivAt m (-l * m s) s := by
      refine (hasDerivAt_expectation_muT F s).congr_deriv ?_
      rw [generator_wilsonStat, expectation_const_mul]
    exact (hE.sub (hm.pow 2)).congr_deriv (by simp only [V]; push_cast; ring)
  set W : ℝ → ℝ := fun s => Real.exp (2 * l * s) * (V s - ε / (2 * l))
  have hW : ∀ s, HasDerivAt W
      (Real.exp (2 * l * s) * (expectation (muT n s) Γ - ε)) s := by
    intro s
    have h1 : HasDerivAt (fun s => 2 * l * s) (2 * l) s := by
      simpa using (hasDerivAt_id s).const_mul (2 * l)
    refine (h1.exp.mul ((hV s).sub_const (ε / (2 * l)))).congr_deriv ?_
    field_simp
    ring
  have hΓ : ∀ s, 0 ≤ s → expectation (muT n s) Γ ≤ ε := by
    intro s hs
    calc expectation (muT n s) Γ ≤ expectation (muT n s) (fun _ => ε) :=
          expectation_mono (fun σ => (cycleShuffle n).semigroup_apply_nonneg hs 1 σ)
            (fun σ => sum_sq_wilsonStat_T_sub_le n σ)
      _ = ε := by rw [expectation_const, hsum, one_mul]
  have hanti : AntitoneOn W (Set.Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun x _ => (hW x).continuousAt.continuousWithinAt) (fun x _ => (hW x).hasDerivWithinAt)
      (fun x hx => ?_)
    rw [interior_Ici] at hx
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (sub_nonpos.2 (hΓ x (le_of_lt hx)))
  have hV0 : V 0 = 0 := by
    simp [V, E, m, F, expectation, muT, InvFamily.semigroup, semigroup_zero, Matrix.one_apply]
  have hWt : W t ≤ W 0 := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  have hVt : V t ≤ ε / (2 * l) := by
    have hW0 : W 0 = -(ε / (2 * l)) := by simp [W, hV0]
    have hpos := Real.exp_pos (2 * l * t)
    have : Real.exp (2 * l * t) * (V t - ε / (2 * l)) ≤ 0 := by
      have : 0 ≤ ε / (2 * l) := by positivity
      simp only [W] at hWt
      linarith
    nlinarith
  have hfin : ε / (2 * l) ≤ Real.pi ^ 2 * n / 2 := by
    have h16 : 16 ≤ l * (n : ℝ) ^ 2 := (div_le_iff₀ (by positivity)).1 hl16
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    simp only [ε]
    rw [div_mul_eq_mul_div, div_le_iff₀ hn0]
    nlinarith [mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.2 h16)]
  rw [hvar]
  exact hVt.trans hfin

end CycleCutoff
