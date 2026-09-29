/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.OneCard.Defs
public import CycleCutoff.OneCard.HeatFourier
public import CycleCutoff.OneCard.EigenvalueRatio
public import CycleCutoff.Cycle.LambdaLower
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Uniform deviation of the heat kernel from uniform

There is an absolute constant `c₉ > 0` such that for all `n ≥ 3`, `t ≥ a₀/λ_n` and
`x ∈ ℤ/nℤ`, `|n p_t(0, x) - 1| ≤ c₉ e^{-λ_n t}`; one may take `c₉ = 4`.

## Main results

* `CycleCutoff.exp_neg_lambdaNJ_mul_le`: `e^{-λ_{n,j} t} ≤ e^{-λ_n t} · e · e^{-j_*}` when
  `λ_n t ≥ a₀`, with `j_* = min(j, n - j)`.
* `CycleCutoff.exists_abs_mul_heatKernel_sub_one_le`: the uniform deviation bound.
-/

public section

open Finset Real

namespace CycleCutoff

/-- For `1 ≤ j ≤ n - 1` and `λ_n t ≥ a₀`, writing `j_* = min(j, n - j)`,
`e^{-λ_{n,j} t} ≤ e^{-λ_n t} · e · (e^{-1})^{j_*}`. -/
theorem exp_neg_lambdaNJ_mul_le {n j : ℕ} (hj₁ : 1 ≤ j) (hj₂ : j ≤ n - 1) {t : ℝ}
    (ht : a0 ≤ lambdaN n * t) :
    Real.exp (-lambdaNJ n j * t) ≤
      Real.exp (-lambdaN n * t) * Real.exp 1 * Real.exp (-1) ^ min j (n - j) := by
  have hratio := max_mul_lambdaN_le_lambdaNJ hj₁ hj₂
  set k : ℕ := min j (n - j) with hk
  set m : ℝ := max 1 (4 * (k : ℝ) ^ 2 / π ^ 2) with hm
  have ha0 : a0 = 5 := rfl
  have hs : (5 : ℝ) ≤ lambdaN n * t := ha0 ▸ ht
  have hl := lambdaN_nonneg n
  have ht0 : 0 ≤ t := by
    by_contra h
    push Not at h
    nlinarith
  have hm1 : 1 ≤ m := le_max_left _ _
  have hkey : (k : ℝ) - 1 ≤ (m - 1) * (lambdaN n * t) := by
    have hk1 : 1 ≤ k := by omega
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have : k = 1 := by omega
      rw [this, Nat.cast_one, sub_self]
      exact mul_nonneg (by linarith) (by linarith)
    · have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      have hpi : π ^ 2 < 10 := by nlinarith [pi_lt_d2, pi_pos]
      have hm' : 4 * (k : ℝ) ^ 2 / 10 ≤ m := by
        refine le_trans ?_ (le_max_right _ _)
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hpi.le
      nlinarith
  calc Real.exp (-lambdaNJ n j * t) ≤ Real.exp (-lambdaN n * t + 1 + k * (-1)) :=
        Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_right hratio ht0])
    _ = Real.exp (-lambdaN n * t) * Real.exp 1 * Real.exp (-1) ^ k := by
        rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul]

/-- **Uniform deviation of the heat kernel**: for `n ≥ 3`, `t ≥ a₀/λ_n` and every
`x ∈ ℤ/nℤ`, `|n p_t(0, x) - 1| ≤ c₉ e^{-λ_n t}` for an absolute constant `c₉ > 0`. -/
@[cycle_cutoff "lem_heat_deviation"]
theorem exists_abs_mul_heatKernel_sub_one_le :
    ∃ c₉ > (0 : ℝ), ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ t : ℝ, a0 / lambdaN n ≤ t →
      ∀ x : ZMod n, |(n : ℝ) * heatKernel n t 0 x - 1| ≤ c₉ * Real.exp (-lambdaN n * t) := by
  refine ⟨4, by norm_num, fun n _ hn t ht x => ?_⟩
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  have hlpos : 0 < lambdaN n :=
    lt_of_lt_of_le (by positivity) (sixteen_div_sq_le_lambdaN (by omega : 2 ≤ n))
  have hlt : a0 ≤ lambdaN n * t := by
    rw [div_le_iff₀ hlpos] at ht
    linarith
  set r : ℝ := Real.exp (-1) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr2 : r ≤ 1 / 2 := by
    rw [hr, Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hr1 : r < 1 := by linarith
  have hx : ((((x.val : ℕ) : ℤ)) : ZMod n) = x := by simp
  rw [← hx, heatKernel_zero_intCast_eq, ← mul_assoc, mul_one_div_cancel hn0, one_mul,
    range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega : 0 < n)]
  have h0 : lambdaNJ n 0 = 0 := by simp [lambdaNJ]
  simp only [h0, CharP.cast_eq_zero, mul_zero, zero_mul, zero_div, neg_zero, Real.exp_zero,
    Real.cos_zero, mul_one, add_sub_cancel_left]
  calc |∑ j ∈ Ico 1 n, Real.exp (-lambdaNJ n j * t) *
          Real.cos (2 * π * j * ((x.val : ℕ) : ℤ) / n)|
      ≤ ∑ j ∈ Ico 1 n, Real.exp (-lambdaNJ n j * t) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
        rw [abs_mul, Real.abs_exp]
        exact mul_le_of_le_one_right (Real.exp_pos _).le (abs_cos_le_one _)
    _ ≤ ∑ j ∈ Ico 1 n, Real.exp (-lambdaN n * t) * Real.exp 1 * (r ^ j + r ^ (n - j)) := by
        refine sum_le_sum fun j hj => ?_
        rw [mem_Ico] at hj
        refine (exp_neg_lambdaNJ_mul_le hj.1 (by omega) hlt).trans ?_
        gcongr
        rcases min_choice j (n - j) with h | h <;> rw [h] <;> linarith [pow_nonneg hr0 j,
          pow_nonneg hr0 (n - j)]
    _ = Real.exp (-lambdaN n * t) * Real.exp 1 *
          (∑ j ∈ Ico 1 n, r ^ j + ∑ j ∈ Ico 1 n, r ^ (n - j)) := by
        rw [← mul_sum, sum_add_distrib]
    _ = Real.exp (-lambdaN n * t) * Real.exp 1 * (2 * ∑ j ∈ Ico 1 n, r ^ j) := by
        rw [sum_Ico_reflect (fun j => r ^ j) 1 (by omega : n ≤ n + 1),
          show n + 1 - n = 1 by omega, show n + 1 - 1 = n by omega]
        ring
    _ ≤ Real.exp (-lambdaN n * t) * Real.exp 1 * (2 * (r ^ 1 / (1 - r))) := by
        gcongr
        exact geom_sum_Ico_le_of_lt_one hr0 hr1
    _ = Real.exp (-lambdaN n * t) * (2 / (1 - r)) := by
        have he : Real.exp 1 * r = 1 := by rw [hr, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
        rw [show Real.exp (-lambdaN n * t) * Real.exp 1 * (2 * (r ^ 1 / (1 - r))) =
          Real.exp (-lambdaN n * t) * (Real.exp 1 * r * 2 / (1 - r)) by ring, he, one_mul]
    _ ≤ 4 * Real.exp (-lambdaN n * t) := by
        rw [mul_comm 4]
        gcongr
        rw [div_le_iff₀ (by linarith)]
        linarith

end CycleCutoff
