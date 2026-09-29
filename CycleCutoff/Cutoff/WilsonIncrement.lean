/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Cutoff.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The increments of Wilson's statistic

For every permutation `σ` of `ℤ/nℤ`, `∑_{x ∈ ℤ/nℤ} (F(τ_x ∘ σ) - F(σ))² ≤ 16π²/n`, where
`F = wilsonStat n` and `τ_x = Equiv.swap x (x + 1)`.

## Main results

* `CycleCutoff.sum_sq_wilsonStat_T_sub_le`: `∑_x (F(τ_x σ) - F(σ))² ≤ 16π²/n`.
-/

public section

open Finset Real

namespace CycleCutoff

variable {n : ℕ}

/-- The adjacent transposition `τ_x` moves a point by at most one step. -/
private lemma swap_add_one_apply_cases (x y : ZMod n) :
    Equiv.swap x (x + 1) y = y ∨ Equiv.swap x (x + 1) y = y + 1 ∨
      Equiv.swap x (x + 1) y = y - 1 := by
  by_cases hx : y = x
  · subst hx
    simp
  by_cases hx1 : y = x + 1
  · subst hx1
    simp
  · exact Or.inl (Equiv.swap_apply_of_ne_of_ne hx hx1)

variable [NeZero n]

/-- Each summand of Wilson's statistic changes by at most `2π/n` under `τ_x`. -/
private lemma abs_cos_swap_sub_le (x : ZMod n) (σ : Equiv.Perm (ZMod n)) (i : ZMod n) :
    |Real.cos (2 * π * ((Equiv.swap x (x + 1) (σ i) - i : ZMod n).val : ℝ) / n) -
        Real.cos (2 * π * ((σ i - i : ZMod n).val : ℝ) / n)| ≤ 2 * π / n := by
  have hpos : 0 ≤ 2 * π / n := by positivity
  rcases swap_add_one_apply_cases x (σ i) with h | h | h
  · simp [h, hpos]
  · rw [h, add_sub_right_comm, cos_two_pi_val_add_one]
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    simp [abs_of_nonneg hpos]
  · rw [h, sub_right_comm, cos_two_pi_val_sub_one]
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    simp [abs_of_nonneg hpos]

/-- A single move changes Wilson's statistic by at most `4π/n`. -/
private lemma abs_wilsonStat_T_sub_le (x : ZMod n) (σ : Equiv.Perm (ZMod n)) :
    |wilsonStat n ((cycleShuffle n).T x σ) - wilsonStat n σ| ≤ 4 * π / n := by
  set S : Finset (ZMod n) := {σ.symm x, σ.symm (x + 1)}
  set d : ZMod n → ℝ := fun i =>
    Real.cos (2 * π * ((Equiv.swap x (x + 1) (σ i) - i : ZMod n).val : ℝ) / n) -
      Real.cos (2 * π * ((σ i - i : ZMod n).val : ℝ) / n)
  have hsum : wilsonStat n ((cycleShuffle n).T x σ) - wilsonStat n σ = ∑ i ∈ S, d i := by
    rw [wilsonStat, wilsonStat, ← Finset.sum_sub_distrib]
    refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
    intro i _ hi
    have h1 : σ i ≠ x := fun h => hi (by simp [S, ← h])
    have h2 : σ i ≠ x + 1 := fun h => hi (by simp [S, ← h])
    simp [Equiv.swap_apply_of_ne_of_ne h1 h2]
  rw [hsum]
  calc |∑ i ∈ S, d i| ≤ ∑ i ∈ S, |d i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ S.card • (2 * π / n) := Finset.sum_le_card_nsmul _ _ _ fun i _ =>
        abs_cos_swap_sub_le x σ i
    _ ≤ 2 • (2 * π / n) := by
        gcongr
        exact Finset.card_le_two
    _ = 4 * π / n := by rw [nsmul_eq_mul]; ring

variable (n) in
/-- **Increments of Wilson's statistic.** For every `σ ∈ S_n`,
`∑_{x ∈ ℤ/nℤ} (F(τ_x ∘ σ) - F(σ))² ≤ 16π²/n`, where `F` is Wilson's statistic. -/
@[cycle_cutoff "lem_F_increment"]
theorem sum_sq_wilsonStat_T_sub_le (σ : Equiv.Perm (ZMod n)) :
    ∑ x : ZMod n, (wilsonStat n ((cycleShuffle n).T x σ) - wilsonStat n σ) ^ 2 ≤
      16 * Real.pi ^ 2 / n := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  calc ∑ x : ZMod n, (wilsonStat n ((cycleShuffle n).T x σ) - wilsonStat n σ) ^ 2
      ≤ (Finset.univ : Finset (ZMod n)).card • (4 * π / n) ^ 2 := by
        refine Finset.sum_le_card_nsmul _ _ _ fun x _ => ?_
        exact sq_le_sq' (abs_le.1 (abs_wilsonStat_T_sub_le x σ)).1
          (abs_le.1 (abs_wilsonStat_T_sub_le x σ)).2
    _ = 16 * Real.pi ^ 2 / n := by
        rw [Finset.card_univ, ZMod.card, nsmul_eq_mul]
        field_simp
        ring

end CycleCutoff
