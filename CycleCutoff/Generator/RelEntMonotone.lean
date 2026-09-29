/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.SemigroupLower
public import CycleCutoff.Generator.SemigroupRowsum
public import CycleCutoff.Generator.SemigroupSymmetric
public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Relative entropy to the uniform measure decreases along the semigroup

For an involution family `𝒯` on `Ω` and a probability vector `α`, the map `t ↦ H(α P^𝒯_t ∣ u_Ω)` is
non-increasing on `[0, ∞)`. More generally, a doubly stochastic matrix does not increase relative
entropy to the uniform measure.

## Main results

* `CycleCutoff.relEnt_unif_eq`: relative entropy to the uniform measure in terms of the density
  against it.
* `CycleCutoff.relEnt_vecMul_unif_le`: a doubly stochastic matrix does not increase relative
  entropy to the uniform measure.
* `CycleCutoff.InvFamily.semigroup_mem_doublyStochastic`: `P^𝒯_t` is doubly stochastic for `t ≥ 0`.
* `CycleCutoff.InvFamily.antitoneOn_relEnt_semigroup`: the relative entropy to the uniform measure
  is non-increasing along the semigroup.
-/

public section

open Finset Matrix

namespace CycleCutoff

variable {Ω : Type*} [Fintype Ω]

/-- Relative entropy to the uniform measure in terms of the density `r = |Ω| γ`:
`H(γ ∣ u_Ω) = |Ω|⁻¹ ∑_z r(z) log r(z)`. -/
theorem relEnt_unif_eq (γ : Ω → ℝ) :
    relEnt γ (unif Ω) = (Fintype.card Ω : ℝ)⁻¹ *
      ∑ z, (Fintype.card Ω * γ z) * Real.log (Fintype.card Ω * γ z) := by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · simp [relEnt]
  have hn : (Fintype.card Ω : ℝ) ≠ 0 := by positivity
  simp only [relEnt, unif, mul_sum]
  refine sum_congr rfl fun z _ => ?_
  field_simp [div_inv_eq_mul, mul_comm]

variable [DecidableEq Ω]

/-- A doubly stochastic matrix does not increase relative entropy to the uniform measure:
`H(β K ∣ u_Ω) ≤ H(β ∣ u_Ω)` for `β ≥ 0`. -/
theorem relEnt_vecMul_unif_le {K : Matrix Ω Ω ℝ} (hK : K ∈ doublyStochastic ℝ Ω)
    {β : Ω → ℝ} (hβ : ∀ z, 0 ≤ β z) :
    relEnt (β ᵥ* K) (unif Ω) ≤ relEnt β (unif Ω) := by
  simp only [relEnt_unif_eq]
  set n : ℝ := (Fintype.card Ω : ℝ)
  have hn : 0 ≤ n := by positivity
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hn)
  calc ∑ w, n * (β ᵥ* K) w * Real.log (n * (β ᵥ* K) w)
      ≤ ∑ w, ∑ z, K z w * (n * β z * Real.log (n * β z)) := by
        refine sum_le_sum fun w _ => ?_
        have hsum : n * (β ᵥ* K) w = ∑ z, K z w * (n * β z) := by
          simp only [vecMul, dotProduct, mul_sum, mul_comm, mul_assoc]
        simpa only [hsum, smul_eq_mul] using Real.convexOn_mul_log.map_sum_le (t := univ)
          (w := fun z => K z w) (p := fun z => n * β z)
          (fun z _ => nonneg_of_mem_doublyStochastic hK)
          (sum_col_of_mem_doublyStochastic hK w)
          (fun z _ => Set.mem_Ici.2 (mul_nonneg hn (hβ z)))
    _ = ∑ z, n * β z * Real.log (n * β z) := by
        rw [sum_comm]
        simp only [← sum_mul, sum_row_of_mem_doublyStochastic hK, one_mul]

namespace InvFamily

variable {ι : Type*} [Fintype ι] (𝒯 : InvFamily ι Ω)

/-- For `t ≥ 0` the semigroup `P^𝒯_t` of an involution family is doubly stochastic. -/
theorem semigroup_mem_doublyStochastic {t : ℝ} (ht : 0 ≤ t) :
    𝒯.semigroup t ∈ doublyStochastic ℝ Ω := by
  refine mem_doublyStochastic_iff_sum.2
    ⟨𝒯.semigroup_apply_nonneg ht, 𝒯.sum_semigroup_apply t, fun w => ?_⟩
  simpa only [𝒯.semigroup_apply_comm t _ w] using 𝒯.sum_semigroup_apply t w

/-- **Monotonicity of relative entropy along the semigroup.** For an involution family `𝒯` and a
probability vector `α`, the relative entropy `t ↦ H(α P^𝒯_t ∣ u_Ω)` is non-increasing on
`[0, ∞)`. -/
@[cycle_cutoff "lem_relent_monotone"]
theorem antitoneOn_relEnt_semigroup (α : Ω → ℝ) (hα : IsProbVec α) :
    AntitoneOn (fun t => relEnt (α ᵥ* 𝒯.semigroup t) (unif Ω)) (Set.Ici 0) := by
  intro s hs t _ hst
  have hsplit : 𝒯.semigroup t = 𝒯.semigroup s * 𝒯.semigroup (t - s) := by
    simp only [InvFamily.semigroup, ← semigroup_add, add_sub_cancel]
  simp only [hsplit, ← vecMul_vecMul]
  exact relEnt_vecMul_unif_le (𝒯.semigroup_mem_doublyStochastic (sub_nonneg.2 hst))
    fun w => sum_nonneg fun z _ => mul_nonneg (hα.nonneg z) (𝒯.semigroup_apply_nonneg hs z w)

end InvFamily

end CycleCutoff
