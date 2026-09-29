/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.Defs
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The Lie product formula

For linear operators `X, Y` on a finite-dimensional real vector space,
`(exp(X/k) exp(Y/k))^k → exp(X + Y)` as `k → ∞`. The same holds in any real Banach algebra with
`‖1‖ = 1`.

## Main results

* `CycleCutoff.norm_pow_sub_pow_le`: `‖a^n - b^n‖ ≤ n M^(n-1) ‖a - b‖` when `‖a‖, ‖b‖ ≤ M`.
* `CycleCutoff.norm_exp_le_exp_norm`: `‖exp x‖ ≤ exp ‖x‖` in a Banach algebra with `‖1‖ = 1`.
* `CycleCutoff.tendsto_smul_exp_mul_exp_sub_exp`: `k (exp(X/k) exp(Y/k) - exp((X + Y)/k)) → 0`.
* `CycleCutoff.tendsto_exp_mul_exp_pow_of_normOneClass`: the Lie product formula in a real Banach
  algebra with `‖1‖ = 1`.
* `CycleCutoff.tendsto_exp_mul_exp_pow`: the Lie product formula for real square matrices.

## Implementation notes

Linear operators on a finite-dimensional real space are represented by square matrices, whose
topology is the product topology, so the matrix statement involves no norm.

## References

* B. C. Hall, *Lie groups, Lie algebras, and representations*, 2nd ed., Theorem 2.11
-/

public section

open NormedSpace Filter Topology

namespace CycleCutoff

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- Telescoping bound for powers in a normed ring: if `‖a‖, ‖b‖ ≤ M`, then
`‖a ^ n - b ^ n‖ ≤ n M ^ (n - 1) ‖a - b‖`. -/
theorem norm_pow_sub_pow_le {a b : 𝔸} {M : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ n * M ^ (n - 1) * ‖a - b‖ := by
  have hM : 0 ≤ M := (norm_nonneg a).trans ha
  suffices h : ∀ m : ℕ, ‖a ^ (m + 1) - b ^ (m + 1)‖ ≤ (m + 1) * M ^ m * ‖a - b‖ by
    rcases n with _ | m
    · simp
    · simpa using h m
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have hb' : ‖b ^ (m + 1)‖ ≤ M ^ (m + 1) :=
      (norm_pow_le' b m.succ_pos).trans (pow_le_pow_left₀ (norm_nonneg b) hb _)
    calc ‖a ^ (m + 1 + 1) - b ^ (m + 1 + 1)‖
        = ‖a * (a ^ (m + 1) - b ^ (m + 1)) + (a - b) * b ^ (m + 1)‖ := by
          rw [pow_succ' a (m + 1), pow_succ' b (m + 1), mul_sub, sub_mul]
          abel_nf
      _ ≤ ‖a‖ * ‖a ^ (m + 1) - b ^ (m + 1)‖ + ‖a - b‖ * ‖b ^ (m + 1)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ M * ((m + 1) * M ^ m * ‖a - b‖) + ‖a - b‖ * M ^ (m + 1) := by
          gcongr
      _ = ((m + 1 : ℕ) + 1 : ℝ) * M ^ (m + 1) * ‖a - b‖ := by push_cast; ring

variable [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- In a real Banach algebra with `‖1‖ = 1`, `‖exp x‖ ≤ exp ‖x‖`. -/
theorem norm_exp_le_exp_norm [NormOneClass 𝔸] (x : 𝔸) : ‖exp x‖ ≤ Real.exp ‖x‖ := by
  have h₂ := exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖
  rw [← Real.exp_eq_exp_ℝ] at h₂
  refine (exp_series_hasSum_exp' (𝕂 := ℝ) x).norm_le_of_bounded h₂ fun k => ?_
  rw [norm_smul, smul_eq_mul, Real.norm_of_nonneg (by positivity)]
  gcongr
  exact norm_pow_le x k

/-- `exp(X/k) exp(Y/k) - exp((X + Y)/k) = o(1/k)`: after scaling by `k` it tends to `0`. -/
theorem tendsto_smul_exp_mul_exp_sub_exp (X Y : 𝔸) :
    Tendsto (fun k : ℕ => (k : ℝ) • (exp ((k : ℝ)⁻¹ • X) * exp ((k : ℝ)⁻¹ • Y) -
      exp ((k : ℝ)⁻¹ • (X + Y)))) atTop (𝓝 0) := by
  let f : ℝ → 𝔸 := fun t => exp (t • X) * exp (t • Y) - exp (t • (X + Y))
  have hd : HasDerivAt f 0 0 :=
    (((hasDerivAt_exp_smul_const' (𝕂 := ℝ) X 0).mul
      (hasDerivAt_exp_smul_const' (𝕂 := ℝ) Y 0)).sub
      (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (X + Y) 0)).congr_deriv (by simp)
  have hs := (hasDerivAt_iff_tendsto_slope.1 hd).comp
    ((tendsto_inv_atTop_nhdsGT_zero.mono_right (nhdsWithin_mono _ (by simp))).comp
      tendsto_natCast_atTop_atTop)
  refine hs.congr fun k => ?_
  simp [slope, f]

/-- **Lie product formula** in a real Banach algebra with `‖1‖ = 1`:
`(exp(X/k) exp(Y/k))^k → exp(X + Y)`. -/
theorem tendsto_exp_mul_exp_pow_of_normOneClass [NormOneClass 𝔸] (X Y : 𝔸) :
    Tendsto (fun k : ℕ => (exp ((k : ℝ)⁻¹ • X) * exp ((k : ℝ)⁻¹ • Y)) ^ k) atTop
      (𝓝 (exp (X + Y))) := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hD := (tendsto_norm_zero.comp (tendsto_smul_exp_mul_exp_sub_exp X Y)).const_mul
    (Real.exp (‖X‖ + ‖Y‖))
  rw [mul_zero] at hD
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hD
  filter_upwards [eventually_ge_atTop 1] with k hk
  set M := Real.exp ((k : ℝ)⁻¹ * (‖X‖ + ‖Y‖))
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hinv : 0 ≤ (k : ℝ)⁻¹ := by positivity
  have hE : exp ((k : ℝ)⁻¹ • (X + Y)) ^ k = exp (X + Y) := by
    rw [← exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hk0, one_smul]
  have hS : ‖exp ((k : ℝ)⁻¹ • X) * exp ((k : ℝ)⁻¹ • Y)‖ ≤ M := by
    refine (norm_mul_le _ _).trans ?_
    rw [show M = Real.exp ‖(k : ℝ)⁻¹ • X‖ * Real.exp ‖(k : ℝ)⁻¹ • Y‖ by
      simp only [M, norm_smul, Real.norm_of_nonneg hinv, ← Real.exp_add, mul_add]]
    gcongr <;> exact norm_exp_le_exp_norm _
  have hE' : ‖exp ((k : ℝ)⁻¹ • (X + Y))‖ ≤ M := by
    refine (norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
    rw [norm_smul, Real.norm_of_nonneg hinv]
    gcongr
    exact norm_add_le X Y
  have hMk : M ^ (k - 1) ≤ Real.exp (‖X‖ + ‖Y‖) := by
    refine (pow_le_pow_right₀ (Real.one_le_exp (by positivity)) (Nat.sub_le k 1)).trans_eq ?_
    rw [← Real.exp_nat_mul, ← mul_assoc, mul_inv_cancel₀ hk0, one_mul]
  rw [← hE]
  refine (norm_pow_sub_pow_le hS hE' k).trans ?_
  rw [Function.comp_apply, norm_smul, Real.norm_natCast]
  calc (k : ℝ) * M ^ (k - 1) * ‖_‖ = M ^ (k - 1) * ((k : ℝ) * ‖_‖) := by ring
    _ ≤ _ := by gcongr

/-- **Lie product formula** for real square matrices: `(exp(X/k) exp(Y/k))^k → exp(X + Y)` as
`k → ∞`. -/
@[cycle_cutoff "lem_lie_trotter"]
theorem tendsto_exp_mul_exp_pow {n : Type*} [Fintype n] [DecidableEq n] (X Y : Matrix n n ℝ) :
    Tendsto (fun k : ℕ => (exp ((k : ℝ)⁻¹ • X) * exp ((k : ℝ)⁻¹ • Y)) ^ k) atTop
      (𝓝 (exp (X + Y))) := by
  cases isEmpty_or_nonempty n
  · exact tendsto_const_nhds.congr fun _ => Subsingleton.elim _ _
  · let _ : NormedRing (Matrix n n ℝ) := Matrix.linftyOpNormedRing
    let _ : NormedAlgebra ℝ (Matrix n n ℝ) := Matrix.linftyOpNormedAlgebra
    have := Matrix.linfty_opNormOneClass (n := n) (α := ℝ)
    exact tendsto_exp_mul_exp_pow_of_normOneClass X Y

end CycleCutoff
