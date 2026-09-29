/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.FiniteProbability.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr

/-!
# Relative entropy against a normalised positive vector

Let `Λ` be a finite set, `u` a probability vector on `Λ` and `v : Λ → (0, ∞)` an arbitrary
positive weight vector with total mass `r = ∑ y, v y`. Then the relative entropy of `u`
against the normalisation `v / r` is bounded by the unnormalised `χ²`-type quantity
`∑ x, (u x - v x) ^ 2 / v x`.

With `r = ∑ y, v y`, one has `H(u ∣ v / r) = ∑ x, u x log (u x / v x) + log r`, and two
applications of `log z ≤ z - 1` (termwise, for `u x > 0`) bound this by
`∑ x, u x ^ 2 / v x - 2 + r = ∑ x, (u x - v x) ^ 2 / v x`.

## Main results

* `CycleCutoff.relEnt_div_sum_le`: `H(u ∣ v / ∑ v) ≤ ∑ x, (u x - v x) ^ 2 / v x`.
-/

public section

open Finset

namespace CycleCutoff

/-- **Relative entropy against a normalised positive vector.** The relative entropy of a
probability vector `u` against the normalisation of a positive vector `v` is at most
`∑ x, (u x - v x) ^ 2 / v x`. -/
@[cycle_cutoff "lem_unnormalized_kl"]
theorem relEnt_div_sum_le {Λ : Type*} [Fintype Λ] (u : Λ → ℝ) (hu : IsProbVec u) (v : Λ → ℝ)
    (hv : ∀ x, 0 < v x) :
    relEnt u (fun x => v x / ∑ y, v y) ≤ ∑ x, (u x - v x) ^ 2 / v x := by
  unfold relEnt
  set r := ∑ y, v y with hr
  have hr0 : 0 < r := by
    rcases isEmpty_or_nonempty Λ with h | h
    · have := hu.sum_eq_one
      simp at this
    · exact sum_pos (fun x _ => hv x) univ_nonempty
  have key : ∀ x, u x * Real.log (u x / (v x / r)) ≤
      u x * (u x / v x - 1) + u x * Real.log r := by
    intro x
    rcases (hu.nonneg x).eq_or_lt with h | h
    · simp [← h]
    · have hv' := hv x
      rw [div_div_eq_mul_div, mul_div_right_comm, Real.log_mul (by positivity) hr0.ne', mul_add]
      gcongr
      exact Real.log_le_sub_one_of_pos (by positivity)
  calc ∑ z, u z * Real.log (u z / (v z / r))
      ≤ ∑ x, (u x * (u x / v x - 1) + u x * Real.log r) := sum_le_sum fun x _ => key x
    _ = ∑ x, u x ^ 2 / v x - 1 + Real.log r := by
        rw [sum_add_distrib, ← sum_mul, hu.sum_eq_one, one_mul]
        simp only [mul_sub, mul_one, sum_sub_distrib, hu.sum_eq_one]
        congr 2
        exact sum_congr rfl fun x _ => by ring
    _ ≤ ∑ x, u x ^ 2 / v x - 1 + (r - 1) := by
        gcongr
        exact Real.log_le_sub_one_of_pos hr0
    _ = ∑ x, (u x - v x) ^ 2 / v x := by
        have h : ∀ x, (u x - v x) ^ 2 / v x = u x ^ 2 / v x - 2 * u x + v x := fun x => by
          have := (hv x).ne'
          field_simp
          ring
        simp only [h, sum_add_distrib, sum_sub_distrib, ← mul_sum, hu.sum_eq_one, ← hr]
        ring

end CycleCutoff
