/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Integrated.Defs
public import CycleCutoff.Integrated.SeparationLaw

/-!
# Orthogonality of the source

Under the uniform measure `ϖ_{n,m}` on the two-copy state space `Ω_{n,m}`, the source
`b(R, X, Y) = 1[X = Y] (w(R, X, Y) - 2(m-1)/(n-1))` is orthogonal to every function of the
separation `X - Y`: `⟨b, ψ(X - Y)⟩_ϖ = 0` for all `ψ : ℤ/nℤ → ℝ`.

## Main results

* `CycleCutoff.innerP_twoCopySource_comp_sub_eq_zero`: `⟨b, ψ(X - Y)⟩_{ϖ_{n,m}} = 0`.

## Implementation notes

The hypotheses are `2 ≤ n` (so that `±1 ≠ 0` in `ℤ/nℤ`) and `m ≤ n`; for `m = 0` the state space is
empty and both sides vanish.
-/

public section

open Finset

namespace CycleCutoff

variable {n : ℕ} [NeZero n] {m : ℕ}

/-- **Orthogonality of the source.** The source `b` is orthogonal under `ϖ_{n,m}` to every function
`ψ(X - Y)` of the separation. -/
@[cycle_cutoff "lem_b_orthogonal"]
theorem innerP_twoCopySource_comp_sub_eq_zero (hn : 2 ≤ n) (hm : m ≤ n) (ψ : ZMod n → ℝ) :
    innerP (unif (TwoCopyState (ZMod n) m)) (twoCopySource n m) (fun w => ψ (w.x - w.y)) = 0 := by
  have hsub : ∀ x y r : ZMod n, x - y = r ↔ y = x - r := fun x y r => by
    constructor <;> rintro rfl <;> abel
  set c : ℝ := 2 * ((m : ℝ) - 1) / ((n : ℝ) - 1)
  have hb : expectation (unif (TwoCopyState (ZMod n) m)) (twoCopySource n m) =
      expectation (unif (TwoCopyState (ZMod n) m)) (fun w =>
        ((if w.x - w.y = 1 then 1 else 0) + (if w.x - w.y = -1 then 1 else 0)) -
          c * (if w.x - w.y = 0 then 1 else 0)) := by
    rw [expectation_unif, expectation_unif]
    congr 1
    have h1 := TwoCopyState.sum_eq (V := ZMod n) (M := ℝ) (m := m) (fun R x y => if x = y then
      ((if x - 1 ∈ R then 1 else 0) + (if x + 1 ∈ R then 1 else 0)) - c else 0)
    have h2 := TwoCopyState.sum_eq (V := ZMod n) (M := ℝ) (m := m) (fun R x y =>
      ((if x - y = 1 then 1 else 0) + (if x - y = -1 then 1 else 0)) -
        c * (if x - y = 0 then 1 else 0))
    simp only [twoCopySource, redNeighbourCount]
    rw [h1, h2]
    refine sum_congr rfl fun R _ => sum_congr rfl fun x hx => ?_
    simp only [hsub, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_ite_eq, sum_ite_eq', hx,
      if_true, sub_neg_eq_add, sub_zero, mul_one]
  have hψ : innerP (unif (TwoCopyState (ZMod n) m)) (twoCopySource n m)
      (fun w => ψ (w.x - w.y)) =
      ψ 0 * expectation (unif (TwoCopyState (ZMod n) m)) (twoCopySource n m) := by
    rw [innerP, ← expectation_const_mul]
    congr 1
    funext w
    by_cases h : w.x = w.y
    · rw [h, sub_self, mul_comm]
    · rw [twoCopySource_of_ne h, zero_mul, mul_zero]
  have h1 : (1 : ZMod n) ≠ 0 := by
    have : Fact (1 < n) := ⟨hn⟩
    exact one_ne_zero
  rw [hψ, hb, expectation_sub, expectation_add, expectation_const_mul,
    expectation_indicator_x_sub_y_eq hm, expectation_indicator_x_sub_y_eq hm,
    expectation_indicator_x_sub_y_eq hm, if_neg h1, if_neg (neg_ne_zero.2 h1), if_pos rfl,
    mul_eq_zero]
  right
  simp only [c, div_eq_mul_inv, mul_inv]
  ring

end CycleCutoff
