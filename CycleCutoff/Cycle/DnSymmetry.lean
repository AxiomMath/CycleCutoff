/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Cycle.Defs
public import CycleCutoff.Generator.Lumping

/-!
# The worst-case distance is the distance from the identity

The heat kernel of the cycle shuffle is invariant under right multiplication,
`P_t(σ, y) = μ_t(y σ⁻¹)`, so the worst-case total variation distance is attained from every
starting point: `d_n(t) = ‖μ_t - π_n‖_TV`.

## Main results

* `CycleCutoff.cycleShuffle_rateMatrix_mulVec_comp_mul_right`: right multiplication by a fixed
  permutation intertwines the generator with itself.
* `CycleCutoff.cycleShuffle_semigroup_apply`: `P_t(σ, y) = μ_t(y σ⁻¹)`.
* `CycleCutoff.tvDist_semigroup_unif`: `‖P_t(σ, ·) - π_n‖_TV = ‖μ_t - π_n‖_TV`.
* `CycleCutoff.dn_eq_tvDist_muT`: `d_n(t) = ‖μ_t - π_n‖_TV`.
-/

public section

open Finset Matrix

namespace CycleCutoff

variable (n : ℕ) [NeZero n]

/-- Right multiplication by a fixed permutation intertwines the generator of the cycle
shuffle with itself. -/
theorem cycleShuffle_rateMatrix_mulVec_comp_mul_right (σ : Equiv.Perm (ZMod n))
    (f : Equiv.Perm (ZMod n) → ℝ) :
    (cycleShuffle n).rateMatrix *ᵥ (f ∘ (· * σ)) =
      ((cycleShuffle n).rateMatrix *ᵥ f) ∘ (· * σ) := by
  ext ρ
  simp only [InvFamily.rateMatrix_mulVec, InvFamily.generator, Function.comp_apply,
    cycleShuffle_T, mul_assoc]

/-- The heat kernel of the cycle shuffle is translation invariant: `P_t(σ, y) = μ_t(y σ⁻¹)`. -/
theorem cycleShuffle_semigroup_apply (t : ℝ) (σ y : Equiv.Perm (ZMod n)) :
    (cycleShuffle n).semigroup t σ y = muT n t (y * σ⁻¹) := by
  have h := sum_semigroup_fiber _ _ _ (cycleShuffle_rateMatrix_mulVec_comp_mul_right n σ) t 1 y
  have hfil : (univ.filter fun w : Equiv.Perm (ZMod n) => w * σ = y) = {y * σ⁻¹} := by
    ext w
    simp [eq_mul_inv_iff_mul_eq]
  rw [hfil, sum_singleton, one_mul] at h
  rw [muT_def, InvFamily.semigroup, h]

/-- The distance to uniformity from any starting point equals the distance from the identity. -/
theorem tvDist_semigroup_unif (t : ℝ) (σ : Equiv.Perm (ZMod n)) :
    tvDist (fun y => (cycleShuffle n).semigroup t σ y) (unif (Equiv.Perm (ZMod n))) =
      tvDist (muT n t) (unif (Equiv.Perm (ZMod n))) := by
  simp only [tvDist, cycleShuffle_semigroup_apply, unif]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight σ⁻¹) fun ρ => |muT n t ρ - (Fintype.card _ : ℝ)⁻¹|

/-- **Symmetry of the worst case.** The worst-case total variation distance of the cycle
shuffle is the distance from the identity, `d_n(t) = ‖μ_t - π_n‖_TV`. -/
@[cycle_cutoff "lem_dn_symmetry"]
theorem dn_eq_tvDist_muT (t : ℝ) :
    dn n t = tvDist (muT n t) (unif (Equiv.Perm (ZMod n))) := by
  simp only [dn, tvDist_semigroup_unif, ciSup_const]

end CycleCutoff
