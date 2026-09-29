/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Cutoff.Defs
public import CycleCutoff.Cutoff.WilsonMean
public import CycleCutoff.Cutoff.WilsonVarianceBound
public import CycleCutoff.Cutoff.WilsonStationaryMean
public import CycleCutoff.Cutoff.WilsonStationaryVariance
public import CycleCutoff.Cycle.DnSymmetry
public import CycleCutoff.Cycle.LambdaLower
public import CycleCutoff.Generator.SemigroupLower
public import CycleCutoff.Generator.SemigroupRowsum

/-!
# The lower bound on the distance before the cutoff

There is an absolute constant `K > 0` such that for all `n ≥ 3` and all `s` with
`t = t_n - s/λ_n ≥ 0`, `d_n(t) ≥ 1 - K e^{-2s}`; one may take `K = 2π² + 4`.

## Main results

* `CycleCutoff.exists_one_sub_le_dn`: `d_n(t_n - s/λ_n) ≥ 1 - K e^{-2s}`.
-/

public section

open Finset Real

namespace CycleCutoff

variable {Ω : Type*} [Fintype Ω]

/-- Markov's inequality: if `ν ≥ 0`, `h ≥ 0` and `a ≤ h` on `B`, then `a ν(B) ≤ 𝔼_ν[h]`. -/
private lemma mul_sum_le_expectation {ν h : Ω → ℝ} (hν : ∀ z, 0 ≤ ν z) (hh : ∀ z, 0 ≤ h z)
    {B : Finset Ω} {a : ℝ} (ha : ∀ z ∈ B, a ≤ h z) :
    a * ∑ z ∈ B, ν z ≤ expectation ν h := by
  rw [mul_sum, expectation_def]
  calc ∑ z ∈ B, a * ν z ≤ ∑ z ∈ B, ν z * h z :=
        sum_le_sum fun z hz => by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (ha z hz) (hν z)
    _ ≤ ∑ z, ν z * h z :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun z _ _ => mul_nonneg (hν z) (hh z)

/-- For weight vectors of equal total mass, `α(B) - β(B) ≤ ‖α - β‖_TV`. -/
private lemma sum_sub_sum_le_tvDist {α β : Ω → ℝ} (h : ∑ z, α z = ∑ z, β z) (B : Finset Ω) :
    ∑ z ∈ B, α z - ∑ z ∈ B, β z ≤ tvDist α β := by
  classical
  have h1 : ∑ z ∈ B, (α z - β z) ≤ ∑ z ∈ B, |α z - β z| :=
    sum_le_sum fun z _ => le_abs_self _
  have h2 : ∑ z ∈ Bᶜ, (β z - α z) ≤ ∑ z ∈ Bᶜ, |α z - β z| :=
    sum_le_sum fun z _ => by rw [abs_sub_comm]; exact le_abs_self _
  have e1 := sum_add_sum_compl B (fun z => |α z - β z|)
  have e2 := sum_add_sum_compl B α
  have e3 := sum_add_sum_compl B β
  rw [sum_sub_distrib] at h1 h2
  unfold tvDist
  linarith

/-- **Lower bound on the distance before the cutoff.** There is an absolute constant `K > 0` such
that `d_n(t_n - s/λ_n) ≥ 1 - K e^{-2s}` for all `n ≥ 3` and all `s` with `t_n - s/λ_n ≥ 0`. -/
@[cycle_cutoff "lem_lower_tv"]
theorem exists_one_sub_le_dn :
    ∃ K > (0 : ℝ), ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ s : ℝ, 0 ≤ tn n - s / lambdaN n →
      1 - K * Real.exp (-2 * s) ≤ dn n (tn n - s / lambdaN n) := by
  refine ⟨2 * π ^ 2 + 4, by positivity, fun n _ hn s ht => ?_⟩
  set t := tn n - s / lambdaN n with ht_def
  set F := wilsonStat n
  set μ := muT n t
  set π' := unif (Equiv.Perm (ZMod n))
  have hn2 : 2 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlam : 0 < lambdaN n :=
    lt_of_lt_of_le (by positivity) (sixteen_div_sq_le_lambdaN hn2)
  set E := expectation μ F with hE_def
  have hE : E = n * Real.exp (-lambdaN n * t) := expectation_muT_wilsonStat n t
  have hexp : -lambdaN n * t = -Real.log n / 2 + s := by
    rw [ht_def, tn]; field_simp; ring
  have hE2 : E ^ 2 = n * Real.exp (2 * s) := by
    rw [hE, mul_pow, sq (Real.exp _), ← Real.exp_add, hexp,
      show -Real.log n / 2 + s + (-Real.log n / 2 + s) = -Real.log n + 2 * s by ring,
      Real.exp_add, Real.exp_neg, Real.exp_log hnR]
    field_simp
  have hEpos : 0 < E := by rw [hE]; positivity
  set c := E / 2 with hc
  have hc2 : c ^ 2 = n * Real.exp (2 * s) / 4 := by rw [hc, div_pow, hE2]; norm_num
  have hcpos : 0 < c := by positivity
  classical
  set A := (univ : Finset (Equiv.Perm (ZMod n))).filter (fun σ => c ≤ F σ)
  have hμnn : ∀ σ, 0 ≤ μ σ := fun σ => (cycleShuffle n).semigroup_apply_nonneg ht 1 σ
  have hμsum : ∑ σ, μ σ = 1 := (cycleShuffle n).sum_semigroup_apply t 1
  have hπ : IsProbVec π' := isProbVec_unif
  have hAc : c ^ 2 * ∑ σ ∈ Aᶜ, μ σ ≤ π ^ 2 * n / 2 := by
    refine le_trans (mul_sum_le_expectation hμnn (fun σ => sq_nonneg (F σ - E)) ?_)
      (variance_muT_wilsonStat_le hn2 ht)
    intro σ hσ
    have hlt : F σ < c := by simpa [A] using hσ
    have h1 : c ≤ E - F σ := by rw [hc]; linarith
    nlinarith
  have hA : c ^ 2 * ∑ σ ∈ A, π' σ ≤ n := by
    have hvar := variance_unif_wilsonStat_le hn
    simp only [variance, expectation_unif_wilsonStat hn2, sub_zero] at hvar
    refine le_trans (mul_sum_le_expectation hπ.nonneg (fun σ => sq_nonneg (F σ)) ?_) hvar
    intro σ hσ
    have hle : c ≤ F σ := by simpa [A] using hσ
    nlinarith
  have htv : ∑ σ ∈ A, μ σ - ∑ σ ∈ A, π' σ ≤ dn n t := by
    rw [dn_eq_tvDist_muT]
    exact sum_sub_sum_le_tvDist (hμsum.trans hπ.sum_eq_one.symm) A
  have hsplit := sum_add_sum_compl A μ
  rw [hμsum] at hsplit
  set x := ∑ σ ∈ Aᶜ, μ σ
  set y := ∑ σ ∈ A, π' σ
  have he : Real.exp (2 * s) * Real.exp (-2 * s) = 1 := by
    rw [← Real.exp_add]; simp
  have hepos := Real.exp_pos (2 * s)
  rw [hc2] at hAc hA
  have hx : Real.exp (2 * s) * x ≤ 2 * π ^ 2 := by
    have : n * (Real.exp (2 * s) * x) ≤ n * (2 * π ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left this hnR
  have hy : Real.exp (2 * s) * y ≤ 4 := by
    have : n * (Real.exp (2 * s) * y) ≤ n * 4 := by nlinarith
    exact le_of_mul_le_mul_left this hnR
  have hx' : x ≤ 2 * π ^ 2 * Real.exp (-2 * s) := by
    calc x = Real.exp (-2 * s) * (Real.exp (2 * s) * x) := by
          rw [← mul_assoc, mul_comm (Real.exp _), he, one_mul]
      _ ≤ Real.exp (-2 * s) * (2 * π ^ 2) :=
          mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le
      _ = _ := mul_comm _ _
  have hy' : y ≤ 4 * Real.exp (-2 * s) := by
    calc y = Real.exp (-2 * s) * (Real.exp (2 * s) * y) := by
          rw [← mul_assoc, mul_comm (Real.exp _), he, one_mul]
      _ ≤ Real.exp (-2 * s) * 4 :=
          mul_le_mul_of_nonneg_left hy (Real.exp_pos _).le
      _ = _ := mul_comm _ _
  linarith

end CycleCutoff
