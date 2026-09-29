/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.OneCard.Defs
public import CycleCutoff.OneCard.HeatTranslation
public import CycleCutoff.OneCard.HeatFourier
public import CycleCutoff.OneCard.EigenvalueRatio
public import CycleCutoff.Cycle.LambdaLower
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The one-card heat kernel is uniformly close to uniform after time `a₀ / λ_n`

For `t ≥ a₀ / λ_n` and `i, x ∈ ℤ/nℤ`, `1/2 ≤ n p_t(i, x) ≤ 3/2`.

## Main results

* `CycleCutoff.one_half_le_mul_heatKernel_and_le`: `1/2 ≤ n p_t(i, x) ≤ 3/2`.
-/

public section

open Finset Real

namespace CycleCutoff

/-- **Uniformity of the one-card heat kernel**: for `t ≥ a₀ / λ_n`,
`1/2 ≤ n p_t(i, x) ≤ 3/2`. -/
@[cycle_cutoff "lem_heat_uniform"]
theorem one_half_le_mul_heatKernel_and_le {n : ℕ} [NeZero n] {t : ℝ}
    (ht : a0 / lambdaN n ≤ t) (i x : ZMod n) :
    1 / 2 ≤ (n : ℝ) * heatKernel n t i x ∧ (n : ℝ) * heatKernel n t i x ≤ 3 / 2 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  set m : ℤ := ((x - i).val : ℤ) with hm_def
  have hm : ((m : ℤ) : ZMod n) = x - i := by
    rw [hm_def, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hsum : (n : ℝ) * heatKernel n t i x =
      1 + ∑ j ∈ Ico 1 n, exp (-lambdaNJ n j * t) * cos (2 * π * j * m / n) := by
    rw [heatKernel_eq_heatKernel_zero_sub, ← hm, heatKernel_zero_intCast_eq, ← mul_assoc,
      mul_one_div_cancel hn0, one_mul, range_eq_Ico,
      sum_eq_sum_Ico_succ_bot (NeZero.pos n)]
    simp [lambdaNJ]
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rw [hsum, Ico_eq_empty (by omega), sum_empty]
    norm_num
  have hlam : 0 < lambdaN n :=
    lt_of_lt_of_le (by positivity) (sixteen_div_sq_le_lambdaN hn)
  have hlt : 5 ≤ lambdaN n * t := by
    rw [div_le_iff₀ hlam, a0] at ht
    linarith
  have ht0 : 0 ≤ t := le_trans (div_nonneg (by norm_num [a0]) hlam.le) ht
  set q : ℝ := exp (-2) with hq_def
  have hq0 : 0 ≤ q := (exp_pos _).le
  have hq : q ≤ 1 / 5 := by
    have h5 : (5 : ℝ) ≤ exp 2 := by
      have := quadratic_le_exp_of_nonneg (x := (2 : ℝ)) (by norm_num)
      norm_num at this
      linarith
    rw [hq_def, exp_neg]
    exact inv_le_of_inv_le₀ (by norm_num) (by norm_num; linarith)
  have hq1 : q < 1 := by linarith
  have hterm : ∀ j ∈ Ico 1 n,
      |exp (-lambdaNJ n j * t) * cos (2 * π * j * m / n)| ≤ q ^ j + q ^ (n - j) := by
    intro j hj
    rw [mem_Ico] at hj
    set k := min j (n - j) with hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    have hratio := max_mul_lambdaN_le_lambdaNJ (n := n) (j := j) hj.1 (by omega)
    rw [← hk] at hratio
    have hpi : π ^ 2 ≤ 10 := by nlinarith [pi_lt_d2, pi_pos]
    have hpi0 : 0 < π ^ 2 := by positivity
    have hlow : 2 * (k : ℝ) ≤ lambdaNJ n j * t := by
      have h1 : 4 * (k : ℝ) ^ 2 / π ^ 2 * lambdaN n ≤ lambdaNJ n j :=
        le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hlam.le) hratio
      have h2 : 4 * (k : ℝ) ^ 2 / π ^ 2 * (lambdaN n * t) ≤ lambdaNJ n j * t := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h1 ht0
      have h3 : 4 * (k : ℝ) ^ 2 / π ^ 2 * 5 ≤ 4 * (k : ℝ) ^ 2 / π ^ 2 * (lambdaN n * t) :=
        mul_le_mul_of_nonneg_left hlt (by positivity)
      have h4 : 2 * (k : ℝ) ≤ 4 * (k : ℝ) ^ 2 / π ^ 2 * 5 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hpi0]
        nlinarith
      linarith
    rw [abs_mul, abs_of_pos (exp_pos _)]
    calc exp (-lambdaNJ n j * t) * |cos (2 * π * j * m / n)|
        ≤ exp (-lambdaNJ n j * t) * 1 :=
          mul_le_mul_of_nonneg_left (abs_cos_le_one _) (exp_pos _).le
      _ ≤ exp ((k : ℝ) * (-2)) := by
          rw [mul_one]; exact exp_le_exp.2 (by linarith)
      _ = q ^ k := exp_nat_mul _ _
      _ ≤ q ^ j + q ^ (n - j) := by
          rcases min_choice j (n - j) with h | h
          · rw [hk, h]; exact le_add_of_nonneg_right (pow_nonneg hq0 _)
          · rw [hk, h]; exact le_add_of_nonneg_left (pow_nonneg hq0 _)
  have hgeom1 : ∑ j ∈ Ico 1 n, q ^ j ≤ q / (1 - q) := by
    simpa using geom_sum_Ico_le_of_lt_one (m := 1) (n := n) hq0 hq1
  have hgeom2 : ∑ j ∈ Ico 1 n, q ^ (n - j) ≤ q / (1 - q) := by
    rw [sum_Ico_reflect (fun j => q ^ j) 1 (by omega : n ≤ n + 1),
      show n + 1 - n = 1 by omega, show n + 1 - 1 = n by omega]
    exact hgeom1
  have hfin : q / (1 - q) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have habs : |(n : ℝ) * heatKernel n t i x - 1| ≤ 1 / 2 := by
    rw [hsum, add_sub_cancel_left]
    calc |∑ j ∈ Ico 1 n, exp (-lambdaNJ n j * t) * cos (2 * π * j * m / n)|
        ≤ ∑ j ∈ Ico 1 n, |exp (-lambdaNJ n j * t) * cos (2 * π * j * m / n)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Ico 1 n, (q ^ j + q ^ (n - j)) := sum_le_sum hterm
      _ = ∑ j ∈ Ico 1 n, q ^ j + ∑ j ∈ Ico 1 n, q ^ (n - j) := sum_add_distrib
      _ ≤ 1 / 2 := by linarith
  rw [abs_sub_le_iff] at habs
  constructor <;> linarith [habs.1, habs.2]

end CycleCutoff
