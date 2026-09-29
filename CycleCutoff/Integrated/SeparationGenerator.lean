/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Integrated.Defs

/-!
# The generator on functions of the separation

For every `ψ : ℤ/nℤ → ℝ`, the generator `L_{n,m}` of the cycle two-copy process `𝒯_{n,m}` acts on
the function `(R, X, Y) ↦ ψ(X - Y)` by
`L_{n,m}[ψ(X - Y)] = 2 (Δψ)(X - Y) + (w - 2) 1[X = Y] (Δψ)(0)`,
where `w = 1[X - 1 ∈ R] + 1[X + 1 ∈ R]` is the red-neighbour count.

## Main results

* `CycleCutoff.twoCopy_generator_comp_sub`: the formula for `L_{n,m}[ψ(X - Y)]`.

## Implementation notes

The only hypothesis is `3 ≤ n`, which makes `X - 1, X, X + 1` distinct; no condition on `m` is
assumed.
-/

public section

open Finset Matrix

namespace CycleCutoff

variable {n : ℕ} [NeZero n] {m : ℕ}

omit [NeZero n] in
private theorem one_ne_zero_of_three_le (hn : 3 ≤ n) : (1 : ZMod n) ≠ 0 :=
  haveI : Fact (1 < n) := ⟨by omega⟩
  one_ne_zero

omit [NeZero n] in
private theorem card_inter_pair_eq_one_iff {R : Finset (ZMod n)} {a b : ZMod n} (hab : a ≠ b) :
    (R ∩ {a, b}).card = 1 ↔ ¬(a ∈ R ↔ b ∈ R) := by
  by_cases ha : a ∈ R <;> by_cases hb : b ∈ R <;>
    simp [Finset.inter_insert_of_mem, Finset.inter_insert_of_notMem, ha, hb, hab]

omit [NeZero n] in
private theorem oneMove_cycle_x (w : TwoCopyState (ZMod n) m) (z : ZMod n) :
    (oneMove (cycleEdge n) m z w).x =
      if ({z, z + 1} : Finset _) ⊆ w.R then Equiv.swap z (z + 1) w.x else w.x := by
  unfold oneMove
  by_cases h : ({z, z + 1} : Finset (ZMod n)) ⊆ w.R
  · rw [dif_pos (show edgeSet (cycleEdge n) z ⊆ w.R from h), if_pos h]; rfl
  · rw [dif_neg (show ¬ edgeSet (cycleEdge n) z ⊆ w.R from h), if_neg h]

omit [NeZero n] in
private theorem oneMove_cycle_y (w : TwoCopyState (ZMod n) m) (z : ZMod n) :
    (oneMove (cycleEdge n) m z w).y = w.y := by
  unfold oneMove
  split_ifs <;> rfl

omit [NeZero n] in
private theorem twoMove_cycle_x (w : TwoCopyState (ZMod n) m) (z : ZMod n) :
    (twoMove (cycleEdge n) m z w).x = w.x := by
  unfold twoMove
  split_ifs <;> rfl

omit [NeZero n] in
private theorem twoMove_cycle_y (w : TwoCopyState (ZMod n) m) (z : ZMod n) :
    (twoMove (cycleEdge n) m z w).y =
      if ({z, z + 1} : Finset _) ⊆ w.R then Equiv.swap z (z + 1) w.y else w.y := by
  unfold twoMove
  by_cases h : ({z, z + 1} : Finset (ZMod n)) ⊆ w.R
  · rw [dif_pos (show edgeSet (cycleEdge n) z ⊆ w.R from h), if_pos h]; rfl
  · rw [dif_neg (show ¬ edgeSet (cycleEdge n) z ⊆ w.R from h), if_neg h]

omit [NeZero n] in
private theorem shMove_cycle_x (w : TwoCopyState (ZMod n) m) (z : ZMod n) :
    (shMove (cycleEdge n) m z w).x =
      if (w.R ∩ {z, z + 1}).card = 1 then Equiv.swap z (z + 1) w.x else w.x := by
  unfold shMove
  by_cases h : (w.R ∩ {z, z + 1}).card = 1
  · rw [if_pos (show (w.R ∩ edgeSet (cycleEdge n) z).card = 1 from h), if_pos h]; rfl
  · rw [if_neg (show ¬ (w.R ∩ edgeSet (cycleEdge n) z).card = 1 from h), if_neg h]

omit [NeZero n] in
private theorem shMove_cycle_y (w : TwoCopyState (ZMod n) m) (z : ZMod n) :
    (shMove (cycleEdge n) m z w).y =
      if (w.R ∩ {z, z + 1}).card = 1 then Equiv.swap z (z + 1) w.y else w.y := by
  unfold shMove
  by_cases h : (w.R ∩ {z, z + 1}).card = 1
  · rw [if_pos (show (w.R ∩ edgeSet (cycleEdge n) z).card = 1 from h), if_pos h]; rfl
  · rw [if_neg (show ¬ (w.R ∩ edgeSet (cycleEdge n) z).card = 1 from h), if_neg h]

omit [NeZero n] in
private theorem oneMove_term (hn : 3 ≤ n) (ψ : ZMod n → ℝ) (w : TwoCopyState (ZMod n) m)
    (z : ZMod n) :
    ψ ((oneMove (cycleEdge n) m z w).x - (oneMove (cycleEdge n) m z w).y) - ψ (w.x - w.y) =
      (if z = w.x then
        (if w.x + 1 ∈ w.R then ψ (w.x - w.y + 1) - ψ (w.x - w.y) else 0) else 0) +
      (if z = w.x - 1 then
        (if w.x - 1 ∈ w.R then ψ (w.x - w.y - 1) - ψ (w.x - w.y) else 0) else 0) := by
  have h1 := one_ne_zero_of_three_le hn
  rw [oneMove_cycle_x, oneMove_cycle_y]
  have hxR := w.x_mem
  have hne1 : w.x ≠ w.x - 1 := by intro h; apply h1; linear_combination h
  by_cases hz : z = w.x
  · subst hz
    simp only [hne1, if_true, if_false, insert_subset_iff, hxR, true_and, singleton_subset_iff,
      Equiv.swap_apply_left, add_zero]
    split_ifs <;> first | rfl | (congr 1; ring_nf)
  · by_cases hz' : z = w.x - 1
    · subst hz'
      simp only [hne1.symm, sub_add_cancel, if_true, if_false, insert_subset_iff, hxR, and_true,
        singleton_subset_iff, Equiv.swap_apply_right, zero_add]
      split_ifs <;> first | rfl | (congr 1; ring_nf)
    · have hne : w.x ≠ z + 1 := fun h => hz' (by rw [h]; ring)
      rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hz) hne]
      simp [hz, hz']

omit [NeZero n] in
private theorem twoMove_term (hn : 3 ≤ n) (ψ : ZMod n → ℝ) (w : TwoCopyState (ZMod n) m)
    (z : ZMod n) :
    ψ ((twoMove (cycleEdge n) m z w).x - (twoMove (cycleEdge n) m z w).y) - ψ (w.x - w.y) =
      (if z = w.y then
        (if w.y + 1 ∈ w.R then ψ (w.x - w.y - 1) - ψ (w.x - w.y) else 0) else 0) +
      (if z = w.y - 1 then
        (if w.y - 1 ∈ w.R then ψ (w.x - w.y + 1) - ψ (w.x - w.y) else 0) else 0) := by
  have h1 := one_ne_zero_of_three_le hn
  rw [twoMove_cycle_x, twoMove_cycle_y]
  have hyR := w.y_mem
  have hne1 : w.y ≠ w.y - 1 := by intro h; apply h1; linear_combination h
  by_cases hz : z = w.y
  · subst hz
    simp only [hne1, if_true, if_false, insert_subset_iff, hyR, true_and, singleton_subset_iff,
      Equiv.swap_apply_left, add_zero]
    split_ifs <;> first | rfl | (congr 1; ring_nf)
  · by_cases hz' : z = w.y - 1
    · subst hz'
      simp only [hne1.symm, sub_add_cancel, if_true, if_false, insert_subset_iff, hyR, and_true,
        singleton_subset_iff, Equiv.swap_apply_right, zero_add]
      split_ifs <;> first | rfl | (congr 1; ring_nf)
    · have hne : w.y ≠ z + 1 := fun h => hz' (by rw [h]; ring)
      rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hz) hne]
      simp [hz, hz']

omit [NeZero n] in
private theorem shMove_term (hn : 3 ≤ n) (ψ : ZMod n → ℝ) (w : TwoCopyState (ZMod n) m)
    (hxy : w.x ≠ w.y) (z : ZMod n) :
    ψ ((shMove (cycleEdge n) m z w).x - (shMove (cycleEdge n) m z w).y) - ψ (w.x - w.y) =
      (if z = w.x then
        (if w.x + 1 ∉ w.R then ψ (w.x - w.y + 1) - ψ (w.x - w.y) else 0) else 0) +
      (if z = w.x - 1 then
        (if w.x - 1 ∉ w.R then ψ (w.x - w.y - 1) - ψ (w.x - w.y) else 0) else 0) +
      (if z = w.y then
        (if w.y + 1 ∉ w.R then ψ (w.x - w.y - 1) - ψ (w.x - w.y) else 0) else 0) +
      (if z = w.y - 1 then
        (if w.y - 1 ∉ w.R then ψ (w.x - w.y + 1) - ψ (w.x - w.y) else 0) else 0) := by
  have h1 := one_ne_zero_of_three_le hn
  rw [shMove_cycle_x, shMove_cycle_y]
  have hxR := w.x_mem
  have hyR := w.y_mem
  have hne1 : ∀ a : ZMod n, a ≠ a - 1 := fun a h => h1 (by linear_combination h)
  have hne2 : ∀ a : ZMod n, a ≠ a + 1 := fun a h => h1 (by linear_combination -h)
  by_cases hz : z = w.x
  · subst hz
    simp only [card_inter_pair_eq_one_iff (hne2 _)]
    by_cases hy1 : w.y = w.x + 1
    · have : w.x = w.y - 1 := by rw [hy1]; ring
      simp [hxR, ← hy1, hyR, hxy, hne1, ← this]
    · have : w.x ≠ w.y - 1 := fun h => hy1 (by rw [h]; ring)
      rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm hxy) hy1]
      simp only [hxR, true_iff, hne1, hxy, this, if_true, if_false, add_zero]
      split_ifs <;> first | rfl | (congr 1; ring_nf)
  · by_cases hz2 : z = w.x - 1
    · subst hz2
      simp only [sub_add_cancel, card_inter_pair_eq_one_iff (hne1 _).symm]
      by_cases hy1 : w.y = w.x - 1
      · have : w.x = w.y + 1 := by rw [hy1]; ring
        simp [hxR, ← hy1, hyR, ← this]
        simp [Ne.symm hxy, hne1]
      · have hxy' : w.x - 1 ≠ w.y - 1 := fun h => hxy (by linear_combination h)
        rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hy1 (Ne.symm hxy)]
        simp only [hxR, iff_true, (hne1 _).symm, Ne.symm hy1, hxy', if_true, if_false, add_zero,
          zero_add]
        split_ifs <;> first | rfl | (congr 1; ring_nf)
    · by_cases hz3 : z = w.y
      · subst hz3
        simp only [card_inter_pair_eq_one_iff (hne2 _)]
        have hx1 : w.x ≠ w.y + 1 := fun h => hz2 (by rw [h]; ring)
        rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hxy hx1]
        simp only [hyR, true_iff, hne1, if_true, if_false, add_zero]
        split_ifs <;> first | rfl | ring_nf
      · by_cases hz4 : z = w.y - 1
        · subst hz4
          simp only [sub_add_cancel, card_inter_pair_eq_one_iff (hne1 _).symm]
          rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (Ne.symm hz) hxy]
          simp only [hyR, iff_true, if_true]
          split_ifs <;> first | rfl | ring_nf
        · have hx1 : w.x ≠ z + 1 := fun h => hz2 (by rw [h]; ring)
          have hy1 : w.y ≠ z + 1 := fun h => hz4 (by rw [h]; ring)
          rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hz) hx1,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm hz3) hy1]
          simp [hz, hz2, hz3, hz4]

omit [NeZero n] in
private theorem shMove_term_of_eq (ψ : ZMod n → ℝ) (w : TwoCopyState (ZMod n) m)
    (hxy : w.x = w.y) (z : ZMod n) :
    ψ ((shMove (cycleEdge n) m z w).x - (shMove (cycleEdge n) m z w).y) - ψ (w.x - w.y) = 0 := by
  rw [shMove_cycle_x, shMove_cycle_y, hxy]
  split_ifs <;> simp

/-- **The generator on functions of the separation.** For `ψ : ℤ/nℤ → ℝ`,
`L_{n,m}[ψ(X - Y)] = 2 (Δψ)(X - Y) + (w - 2) 1[X = Y] (Δψ)(0)`, where `w` is the red-neighbour
count. -/
@[cycle_cutoff "lem_separation_generator"]
theorem twoCopy_generator_comp_sub (hn : 3 ≤ n) (ψ : ZMod n → ℝ) :
    (twoCopy n m).generator (fun w => ψ (w.x - w.y)) = fun w =>
      2 * (Delta n *ᵥ ψ) (w.x - w.y) +
        (redNeighbourCount w - 2) * (if w.x = w.y then 1 else 0) * (Delta n *ᵥ ψ) 0 := by
  funext w
  simp only [InvFamily.generator, TwoCopyMove.sum_eq, twoCopy, twoCopyFamily_T_sh,
    twoCopyFamily_T_one, twoCopyFamily_T_two, Delta_mulVec, redNeighbourCount_apply]
  simp only [oneMove_term hn, twoMove_term hn, sum_add_distrib, sum_ite_eq', mem_univ, if_true]
  by_cases hxy : w.x = w.y
  · simp only [shMove_term_of_eq ψ w hxy, sum_const_zero, zero_add, if_pos hxy]
    rw [← hxy, sub_self, zero_add, zero_sub]
    split_ifs <;> ring
  · simp only [shMove_term hn ψ w hxy, sum_add_distrib, sum_ite_eq', mem_univ, if_true,
      if_neg hxy]
    split_ifs <;> ring

end CycleCutoff
