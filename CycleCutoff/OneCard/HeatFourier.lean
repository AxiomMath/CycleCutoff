/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.OneCard.Defs
public import CycleCutoff.Cycle.CosineSum
public import CycleCutoff.Generator.SemigroupSymmetric
public import CycleCutoff.OneCard.DeltaInvolution
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Fourier expansion of the heat kernel

For every real `t` and every integer `x`,
`p_t(0, x mod n) = (1/n) ∑_{j=0}^{n-1} e^{-λ_{n,j} t} cos(2πjx/n)`.

## Main definitions

* `CycleCutoff.cosMode n j`: the cosine mode `y ↦ cos(2πjy/n)` on `ℤ/nℤ`.

## Main results

* `CycleCutoff.semigroup_mulVec_of_mulVec_eq_smul`: if `Q v = μ v` then `P^Q_t v = e^{tμ} v`.
* `CycleCutoff.cosMode_intCast`: `c_j(x mod n) = cos(2πjx/n)` for `x ∈ ℤ`.
* `CycleCutoff.Delta_mulVec_cosMode`: `Δ c_j = -λ_{n,j} c_j`.
* `CycleCutoff.heatKernel_zero_intCast_eq`: the Fourier expansion of `p_t(0, ·)`.
-/

public section

open Finset Matrix Real

namespace CycleCutoff

section Eigenvector

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- An eigenvector of `Q` is an eigenvector of the semigroup: if `Q v = μ v` then
`P^Q_t v = e^{tμ} v`. -/
theorem semigroup_mulVec_of_mulVec_eq_smul (Q : Matrix Ω Ω ℝ) {μ : ℝ} {v : Ω → ℝ}
    (h : Q *ᵥ v = μ • v) (t : ℝ) : semigroup Q t *ᵥ v = Real.exp (t * μ) • v := by
  let : NormedRing (Matrix Ω Ω ℝ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Matrix Ω Ω ℝ) := Matrix.linftyOpNormedAlgebra
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Q)).map
    (Matrix.mulVec.addMonoidHomLeft v) (continuous_id.matrix_mulVec continuous_const)
  refine hs.unique ?_
  have hpow : ∀ k : ℕ, (t • Q) ^ k *ᵥ v = (t * μ) ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, Matrix.smul_mulVec, h,
        smul_smul, smul_smul, pow_succ']
      ring_nf
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t * μ)).smul_const v
  rw [← Real.exp_eq_exp_ℝ] at h2
  convert h2 using 1
  ext k : 1
  change ((k.factorial : ℝ)⁻¹ • (t • Q) ^ k) *ᵥ v = _
  rw [Matrix.smul_mulVec, hpow, smul_smul, smul_eq_mul]

end Eigenvector

variable (n : ℕ)

/-- The `j`-th cosine mode `c_j(y) = cos(2πjy/n)` on `ℤ/nℤ`, evaluated at the representative
`y.val ∈ [0, n)`; by periodicity any integer representative gives the same value
(`cosMode_intCast`). -/
noncomputable def cosMode (j : ℕ) (y : ZMod n) : ℝ :=
  Real.cos (2 * π * j * y.val / n)

variable {n} [NeZero n]

/-- The cosine mode at the class of an integer `x` is `cos(2πjx/n)`. -/
theorem cosMode_intCast (j : ℕ) (x : ℤ) :
    cosMode n j x = Real.cos (2 * π * j * x / n) :=
  cos_two_pi_mul_val_div j x

/-- The cosine modes are eigenvectors of the one-card generator: `Δ c_j = -λ_{n,j} c_j`. -/
theorem Delta_mulVec_cosMode (j : ℕ) :
    Delta n *ᵥ cosMode n j = -lambdaNJ n j • cosMode n j := by
  rw [Delta_mulVec]
  ext y
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective y
  have h1 : (m : ZMod n) - 1 = ((m - 1 : ℤ) : ZMod n) := by push_cast; ring
  have h2 : (m : ZMod n) + 1 = ((m + 1 : ℤ) : ZMod n) := by push_cast; ring
  rw [h1, h2, Pi.smul_apply, smul_eq_mul, cosMode_intCast, cosMode_intCast, cosMode_intCast,
    lambdaNJ]
  have ha : 2 * π * j * ((m - 1 : ℤ) : ℝ) / n = 2 * π * j * m / n - 2 * π * j / n := by
    push_cast; ring
  have hb : 2 * π * j * ((m + 1 : ℤ) : ℝ) / n = 2 * π * j * m / n + 2 * π * j / n := by
    push_cast; ring
  rw [ha, hb, Real.cos_sub, Real.cos_add]
  ring

/-- **Fourier expansion of the heat kernel**: for every integer `x`,
`p_t(0, x mod n) = (1/n) ∑_{j=0}^{n-1} e^{-λ_{n,j} t} cos(2πjx/n)`. -/
@[cycle_cutoff "lem_heat_fourier"]
theorem heatKernel_zero_intCast_eq (t : ℝ) (x : ℤ) :
    heatKernel n t 0 (x : ZMod n) =
      (1 / n) * ∑ j ∈ Finset.range n,
        Real.exp (-lambdaNJ n j * t) * Real.cos (2 * π * j * x / n) := by
  have hn : n ≠ 0 := NeZero.ne n
  have hsymm : (semigroup (Delta n) t).IsSymm := by
    rw [Delta_eq_rateMatrix]
    exact (oneCardFamily n).isSymm_rateMatrix.semigroup t
  have hδ : (Pi.single 0 1 : ZMod n → ℝ) = ∑ j ∈ range n, (1 / (n : ℝ)) • cosMode n j := by
    ext y
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← mul_sum, cosMode_intCast,
      sum_range_cos_two_pi_mul_div hn, Pi.single_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]
    split_ifs <;> simp [hn]
  have hcol : heatKernel n t 0 (x : ZMod n) = (semigroup (Delta n) t *ᵥ Pi.single 0 1) x := by
    rw [Matrix.mulVec_single_one, heatKernel_def, ← hsymm.apply]
    rfl
  rw [hcol, hδ, Matrix.mulVec_sum, Finset.sum_apply, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [Matrix.mulVec_smul, semigroup_mulVec_of_mulVec_eq_smul _ (Delta_mulVec_cosMode j),
    Pi.smul_apply, Pi.smul_apply, cosMode_intCast, smul_eq_mul, smul_eq_mul]
  ring_nf

end CycleCutoff
