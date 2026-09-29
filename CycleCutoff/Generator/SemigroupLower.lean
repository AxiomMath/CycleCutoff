/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.Defs
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# A termwise lower bound for the semigroup of an involution family

Let `Q` be a real square matrix and `c` a real number such that `Q + c I` has non-negative entries.
Then for `t ≥ 0` and every `k`, `P^Q_t(z, w) ≥ e^{-ct} t^k / k! ((Q + c I)^k)(z, w)`, and in
particular `P^Q_t(z, w) ≥ 0`. For an involution family `𝒯 = (T_e)_{e ∈ ι}` one may take `c = |ι|`:
the entries of `Q_𝒯 + |ι| I` are `#{e : T_e z = w} ≥ 0`.

## Main results

* `CycleCutoff.exp_mul_pow_le_semigroup`: the termwise lower bound for a general `Q`.
* `CycleCutoff.InvFamily.rateMatrix_add_card_smul_one_apply`: the entries of `Q_𝒯 + |ι| I` count
  the maps sending `z` to `w`.
* `CycleCutoff.InvFamily.exp_mul_pow_le_semigroup`: the termwise lower bound for an involution
  family.
* `CycleCutoff.InvFamily.semigroup_apply_nonneg`: `P^𝒯_t` has non-negative entries for `t ≥ 0`.
-/

public section

open Finset Matrix

namespace CycleCutoff

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- If `Q + c I` has non-negative entries and `t ≥ 0`, then
`P^Q_t(z, w) ≥ e^{-ct} t^k / k! ((Q + c I)^k)(z, w)` for every `k`. -/
theorem exp_mul_pow_le_semigroup {Q : Matrix Ω Ω ℝ} {c : ℝ}
    (hQ : ∀ z w, 0 ≤ (Q + c • (1 : Matrix Ω Ω ℝ)) z w) {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    (z w : Ω) :
    Real.exp (-c * t) * (t ^ k / k.factorial) * ((Q + c • (1 : Matrix Ω Ω ℝ)) ^ k) z w ≤
      semigroup Q t z w := by
  set A := Q + c • (1 : Matrix Ω Ω ℝ)
  have hsplit : t • Q = (-c * t) • (1 : Matrix Ω Ω ℝ) + t • A := by
    simp only [A, smul_add, smul_smul]; module
  have hcomm : Commute ((-c * t) • (1 : Matrix Ω Ω ℝ)) (t • A) :=
    ((Commute.one_left A).smul_left _).smul_right _
  have hexp : NormedSpace.exp ((-c * t) • (1 : Matrix Ω Ω ℝ)) =
      Real.exp (-c * t) • (1 : Matrix Ω Ω ℝ) := by
    rw [smul_one_eq_diagonal, exp_diagonal, smul_one_eq_diagonal]
    congr 1
    ext
    simp [Real.exp_eq_exp_ℝ]
  rw [semigroup, hsplit, exp_add_of_commute _ _ hcomm, hexp, smul_mul_assoc, one_mul,
    Matrix.smul_apply, smul_eq_mul, mul_assoc]
  gcongr
  have hs : HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ • (t • A) ^ n)
      (NormedSpace.exp (t • A)) := by
    let : NormedRing (Matrix Ω Ω ℝ) := Matrix.linftyOpNormedRing
    let : NormedAlgebra ℝ (Matrix Ω Ω ℝ) := Matrix.linftyOpNormedAlgebra
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • A)
  have hzw := Pi.hasSum.mp (Pi.hasSum.mp hs z) w
  convert le_hasSum hzw k fun j _ => ?_ using 1
  · simp [smul_pow, div_eq_inv_mul, mul_assoc]
  · simp only [smul_pow, Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (pow_apply_nonneg hQ j z w))

/-- If `Q + c I` has non-negative entries for some `c`, then `P^Q_t` has non-negative entries for
`t ≥ 0`. -/
theorem semigroup_apply_nonneg {Q : Matrix Ω Ω ℝ} {c : ℝ}
    (hQ : ∀ z w, 0 ≤ (Q + c • (1 : Matrix Ω Ω ℝ)) z w) {t : ℝ} (ht : 0 ≤ t) (z w : Ω) :
    0 ≤ semigroup Q t z w :=
  le_trans (mul_nonneg (mul_nonneg (Real.exp_pos _).le (by positivity))
    (pow_apply_nonneg hQ 0 z w)) (exp_mul_pow_le_semigroup hQ ht 0 z w)

namespace InvFamily

variable {ι : Type*} [Fintype ι] (𝒯 : InvFamily ι Ω)

omit [Fintype Ω] in
/-- The entries of `Q_𝒯 + |ι| I` count the maps of the family sending `z` to `w`. -/
theorem rateMatrix_add_card_smul_one_apply (z w : Ω) :
    (𝒯.rateMatrix + (Fintype.card ι : ℝ) • (1 : Matrix Ω Ω ℝ)) z w =
      (#{e | 𝒯.T e z = w} : ℝ) := by
  simp [rateMatrix, one_apply, sum_sub_distrib, sum_boole]

omit [Fintype Ω] in
/-- The matrix `Q_𝒯 + |ι| I` has non-negative entries. -/
theorem rateMatrix_add_card_smul_one_apply_nonneg (z w : Ω) :
    0 ≤ (𝒯.rateMatrix + (Fintype.card ι : ℝ) • (1 : Matrix Ω Ω ℝ)) z w := by
  rw [rateMatrix_add_card_smul_one_apply]
  positivity

/-- **Termwise lower bound for the semigroup.** For an involution family `𝒯` indexed by `ι`,
`t ≥ 0` and `k ≥ 0`, `P^𝒯_t(z, w) ≥ e^{-|ι| t} t^k / k! ((Q_𝒯 + |ι| I)^k)(z, w)`. -/
@[cycle_cutoff "lem_semigroup_lower"]
theorem exp_mul_pow_le_semigroup {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (z w : Ω) :
    Real.exp (-(Fintype.card ι) * t) * (t ^ k / k.factorial) *
        ((𝒯.rateMatrix + (Fintype.card ι : ℝ) • (1 : Matrix Ω Ω ℝ)) ^ k) z w ≤
      𝒯.semigroup t z w :=
  CycleCutoff.exp_mul_pow_le_semigroup 𝒯.rateMatrix_add_card_smul_one_apply_nonneg ht k z w

/-- The semigroup of an involution family has non-negative entries for `t ≥ 0`. -/
theorem semigroup_apply_nonneg {t : ℝ} (ht : 0 ≤ t) (z w : Ω) : 0 ≤ 𝒯.semigroup t z w :=
  CycleCutoff.semigroup_apply_nonneg 𝒯.rateMatrix_add_card_smul_one_apply_nonneg ht z w

end InvFamily

end CycleCutoff
