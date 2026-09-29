/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Integrated.Defs

/-!
# The law of the separation

Under the uniform measure `ϖ_{n,m}` on the two-copy state space
`Ω_{n,m} = {(R, X, Y) : |R| = m, X, Y ∈ R}` over `ℤ/nℤ`, the separation `X - Y` equals `0` with
probability `1/m`, and equals any fixed `r ≠ 0` with probability `(m - 1)/(m(n - 1))`.

## Main results

* `CycleCutoff.expectation_indicator_x_sub_y_eq`: the law of `X - Y` under `ϖ_{n,m}`.

## Implementation notes

The only hypothesis is `m ≤ n`. For `m = 0` the state space is empty and both sides vanish (real
division by zero is zero).
-/

public section

open Finset

namespace CycleCutoff

variable {n : ℕ} [NeZero n] {m : ℕ}

/-- **Law of the separation.** Under `ϖ_{n,m}`, `X - Y = 0` with probability `1/m` and `X - Y = r`
with probability `(m - 1)/(m(n - 1))` for each `r ≠ 0`. -/
@[cycle_cutoff "lem_separation_law"]
theorem expectation_indicator_x_sub_y_eq (hm : m ≤ n) (r : ZMod n) :
    expectation (unif (TwoCopyState (ZMod n) m)) (fun w => if w.x - w.y = r then 1 else 0) =
      if r = 0 then 1 / (m : ℝ) else ((m : ℝ) - 1) / ((m : ℝ) * ((n : ℝ) - 1)) := by
  have hcard : (Fintype.card (TwoCopyState (ZMod n) m) : ℝ) = (n.choose m : ℝ) * m * m := by
    rw [TwoCopyState.card_eq, ZMod.card]; push_cast; ring
  rw [expectation_unif, hcard,
    TwoCopyState.sum_eq (fun _ x y => if x - y = r then (1 : ℝ) else 0)]
  obtain rfl | hm₁ := Nat.eq_zero_or_pos m
  · simp
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hC : (n.choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hm).ne'
  split_ifs with hr
  · subst hr
    simp only [sub_eq_zero, sum_ite_eq]
    rw [sum_congr rfl fun R hR => by
      rw [sum_congr rfl fun x hx => if_pos hx, sum_const, mem_powersetCard_univ.1 hR],
      sum_const, card_powersetCard, card_univ, ZMod.card]
    field_simp
    simp
  · have key : ∑ R ∈ univ.powersetCard m, ∑ x ∈ R, ∑ y ∈ R,
        (if x - y = r then (1 : ℝ) else 0) =
        ∑ y : ZMod n, (#((univ.powersetCard m).filter ({y, y + r} ⊆ ·)) : ℝ) := by
      calc _ = ∑ R ∈ univ.powersetCard m, ∑ y : ZMod n,
            if {y, y + r} ⊆ R then (1 : ℝ) else 0 := by
            refine sum_congr rfl fun R _ => ?_
            rw [sum_comm]
            simp_rw [sub_eq_iff_eq_add, sum_ite_eq']
            simp [insert_subset_iff, ite_and, Finset.sum_ite_mem, add_comm r]
        _ = _ := by rw [sum_comm]; simp [sum_boole]
    rw [key]
    have hpair : ∀ y : ZMod n, #({y, y + r} : Finset (ZMod n)) = 2 := fun y =>
      card_pair fun h => hr (by simpa using h)
    obtain rfl | hm₂ : m = 1 ∨ 2 ≤ m := by omega
    · have h0 : ∀ y : ZMod n, (univ.powersetCard 1).filter ({y, y + r} ⊆ ·) = ∅ := by
        refine fun y => filter_eq_empty_iff.2 fun R hR hsub => ?_
        have := card_le_card hsub
        rw [hpair, mem_powersetCard_univ.1 hR] at this
        omega
      simp [h0]
    have hcount : ∀ y : ZMod n, #((univ.powersetCard m).filter ({y, y + r} ⊆ ·)) =
        (n - 2).choose (m - 2) := fun y => by
      rw [card_filter_powersetCard_subset _ _ _ (subset_univ _) (by rw [hpair]; omega), hpair,
        card_univ, ZMod.card]
    simp only [hcount, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by omega⟩
    simp only [Nat.add_sub_cancel]
    have h1 : ((N : ℝ) + 1 + 1) * ((N + 1).choose (k + 1) : ℝ) =
        ((N + 2).choose (k + 2) : ℝ) * ((k : ℝ) + 1 + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq (N + 1) (k + 1)
    have h2 : ((N : ℝ) + 1) * (N.choose k : ℝ) =
        ((N + 1).choose (k + 1) : ℝ) * ((k : ℝ) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq N k
    have hN : ((N : ℝ) + 2) - 1 ≠ 0 := by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]
    push_cast at hm0 ⊢
    rw [inv_mul_eq_div, div_eq_div_iff (by positivity) (mul_ne_zero hm0 hN)]
    linear_combination ((k : ℝ) + 2) * ((N : ℝ) + 2) * h2 + ((k : ℝ) + 2) * ((k : ℝ) + 1) * h1

end CycleCutoff
