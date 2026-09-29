/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.Defs

/-!
# The semigroup of an involution family is row-stochastic

For an involution family `𝒯` on `Ω`, every row of the semigroup `P^𝒯_t = exp(t Q_𝒯)` sums to one,
for every real `t`.

## Main results

* `CycleCutoff.semigroup_mulVec_of_mulVec_eq_zero`: if `Q v = 0` then `P^Q_t v = v`.
* `CycleCutoff.InvFamily.rateMatrix_mulVec_const`: `Q_𝒯` annihilates constant functions.
* `CycleCutoff.InvFamily.sum_semigroup_apply`: `∑_w P^𝒯_t(z, w) = 1`.
-/

public section

open Finset Matrix

namespace CycleCutoff

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- A vector killed by `Q` is fixed by the semigroup: if `Q v = 0` then `P^Q_t v = v`. -/
theorem semigroup_mulVec_of_mulVec_eq_zero (Q : Matrix Ω Ω ℝ) {v : Ω → ℝ} (h : Q *ᵥ v = 0)
    (t : ℝ) : semigroup Q t *ᵥ v = v := by
  let : NormedRing (Matrix Ω Ω ℝ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Matrix Ω Ω ℝ) := Matrix.linftyOpNormedAlgebra
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Q)).map
    (Matrix.mulVec.addMonoidHomLeft v) (continuous_id.matrix_mulVec continuous_const)
  refine hs.unique ?_
  have hv : ∀ n ≠ 0, ((n.factorial : ℝ)⁻¹ • (t • Q) ^ n) *ᵥ v = 0 := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simp [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.smul_mulVec]
  convert hasSum_single 0 hv
  · rfl
  · simp

namespace InvFamily

variable {ι : Type*} [Fintype ι] (𝒯 : InvFamily ι Ω)

/-- The rate matrix of an involution family annihilates constant functions. -/
theorem rateMatrix_mulVec_const (c : ℝ) : 𝒯.rateMatrix *ᵥ (fun _ => c) = 0 := by
  ext z
  simp [rateMatrix_mulVec, generator]

/-- **Row sums of the semigroup.** The semigroup of an involution family is row-stochastic:
`∑_w P^𝒯_t(z, w) = 1`. -/
@[cycle_cutoff "lem_semigroup_rowsum"]
theorem sum_semigroup_apply (t : ℝ) (z : Ω) : ∑ w, 𝒯.semigroup t z w = 1 := by
  have h := congrFun (semigroup_mulVec_of_mulVec_eq_zero _ (𝒯.rateMatrix_mulVec_const 1) t) z
  simpa [InvFamily.semigroup, mulVec, dotProduct] using h

end InvFamily

end CycleCutoff
