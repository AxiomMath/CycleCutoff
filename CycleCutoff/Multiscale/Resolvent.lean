/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Integrated.Defs
public import CycleCutoff.Multiscale.Defs
public import CycleCutoff.Generator.HMinusOneDualBound
public import CycleCutoff.Multiscale.MatchingDualBound

/-!
# The multiscale bound on the resolvent quantity

There is an absolute constant `K₃ > 0` such that for every `n ≥ 3` and every `1 ≤ m ≤ n`,
`𝓡_{n,m} ≤ K₃ (1 - m/n)/m (1 + log n)²`. This is Proposition 6.1 of C. Defant, *Cutoff for the
Adjacent Transposition Shuffle on a Cycle*.

## Main results

* `CycleCutoff.exists_resolventQuantity_le`: `𝓡_{n,m} ≤ K₃ (1 - m/n)/m (1 + log n)²`.
-/

public section

open Finset

namespace CycleCutoff

variable {n : ℕ}

private theorem val_add_one_of_lt (hn : 2 ≤ n) {x : ZMod n} (h : x.val + 1 < n) :
    (x + 1).val = x.val + 1 := by
  rw [ZMod.val_add_of_lt (by rw [ZMod.val_one'' (by omega)]; exact h), ZMod.val_one'' (by omega)]

/-- The edges `e_x` with `x ≤ n - 2` of a fixed parity form a matching. -/
private theorem isCycleMatching_parity [NeZero n] (hn : 2 ≤ n) (k : ℕ) :
    IsCycleMatching n (univ.filter fun x : ZMod n => x.val % 2 = k ∧ x.val + 2 ≤ n) := by
  intro x hx y hy hxy
  simp only [mem_filter, mem_univ, true_and] at hx hy
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [mem_insert, mem_singleton] at ha hb
  have hx1 := val_add_one_of_lt hn (x := x) (by omega)
  have hy1 := val_add_one_of_lt hn (x := y) (by omega)
  rcases ha with rfl | rfl <;> rcases hb with h | h
  · exact hxy h
  · have := congrArg ZMod.val h; omega
  · have := congrArg ZMod.val h; omega
  · exact hxy (add_right_cancel h)

/-- The single edge `e_{n-1}` forms a matching. -/
private theorem isCycleMatching_last [NeZero n] :
    IsCycleMatching n (univ.filter fun x : ZMod n => x.val + 1 = n) := by
  intro x hx y hy hxy
  simp only [mem_filter, mem_univ, true_and] at hx hy
  exact absurd (ZMod.val_injective n (by omega)) hxy

variable (m : ℕ)

/-- The source is the sum of the block sources of the three matchings `M₁, M₂, M₃` over the
whole cycle. -/
private theorem twoCopySource_eq_sum_blockSource [NeZero n] (w : TwoCopyState (ZMod n) m) :
    twoCopySource n m w =
      blockSource n m (univ.filter fun x : ZMod n => x.val % 2 = 0 ∧ x.val + 2 ≤ n) univ w +
      blockSource n m (univ.filter fun x : ZMod n => x.val % 2 = 1 ∧ x.val + 2 ≤ n) univ w +
      blockSource n m (univ.filter fun x : ZMod n => x.val + 1 = n) univ w := by
  simp only [blockSource, filter_true_of_mem fun (x : ZMod n) _ => subset_univ _, sum_filter,
    ← sum_add_distrib]
  set α : ℝ := ((m : ℝ) - 1) / ((n : ℝ) - 1)
  have hsplit : ∀ x : ZMod n, ∀ t : ℝ,
      ((if x.val % 2 = 0 ∧ x.val + 2 ≤ n then t else 0) +
        (if x.val % 2 = 1 ∧ x.val + 2 ≤ n then t else 0) +
        (if x.val + 1 = n then t else 0)) = t := by
    intro x t
    have := ZMod.val_lt x
    split_ifs <;> first | (exfalso; omega) | ring
  simp only [hsplit]
  by_cases hxy : w.x = w.y
  · rw [twoCopySource_apply, if_pos hxy, redNeighbourCount_apply]
    simp only [← hxy, and_self, ite_mul, one_mul, zero_mul, sum_add_distrib]
    simp only [← sub_eq_iff_eq_add, sum_ite_eq, mem_univ, if_true]
    simp only [α]
    ring
  · rw [twoCopySource_of_ne hxy]
    symm
    refine sum_eq_zero fun x _ => ?_
    have h1 : ¬ (w.x = x ∧ w.y = x) := fun h => hxy (h.1.trans h.2.symm)
    have h2 : ¬ (w.x = x + 1 ∧ w.y = x + 1) := fun h => hxy (h.1.trans h.2.symm)
    simp [h1, h2]

/-- For `m = 1` the source vanishes. -/
private theorem twoCopySource_one (hn : 2 ≤ n) : twoCopySource n 1 = 0 := by
  funext w
  by_cases hxy : w.x = w.y
  · have h10 : (1 : ZMod n) ≠ 0 := haveI : Fact (1 < n) := ⟨by omega⟩; one_ne_zero
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 w.card_R
    have hx := w.x_mem
    rw [ha, mem_singleton] at hx
    simp only [twoCopySource_apply, if_pos hxy, redNeighbourCount_apply, ha, mem_singleton,
      ← hx, sub_eq_self, add_eq_left, h10, if_false]
    simp
  · exact twoCopySource_of_ne hxy

/-- For `m = n` the source vanishes. -/
private theorem twoCopySource_self [NeZero n] (hn : 2 ≤ n) : twoCopySource n n = 0 := by
  funext w
  by_cases hxy : w.x = w.y
  · have hR : w.R = univ := Finset.eq_univ_of_card _ (by rw [w.card_R, ZMod.card])
    have hn1 : (n : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [twoCopySource_apply, if_pos hxy, redNeighbourCount_apply, hR, if_pos (mem_univ _),
      if_pos (mem_univ _), mul_div_assoc, div_self hn1]
    simp only [Pi.zero_apply]
    ring
  · exact twoCopySource_of_ne hxy

/-- **The multiscale bound on the resolvent quantity.** There is an absolute constant
`K₃ > 0` such that for all `n ≥ 3` and `1 ≤ m ≤ n`,
`𝓡_{n,m} ≤ K₃ (1 - m/n)/m (1 + log n)²`. -/
@[cycle_cutoff "prop_resolvent"]
theorem exists_resolventQuantity_le :
    ∃ K₃ > 0, ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ m : ℕ, 1 ≤ m → m ≤ n →
      resolventQuantity n m ≤ K₃ * ((1 - (m : ℝ) / n) / m) * (1 + Real.log n) ^ 2 := by
  obtain ⟨K, hK, hmatch⟩ := exists_innerP_blockSource_univ_sq_le
  refine ⟨9 * K, by positivity, fun n _ hn m hm1 hmn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hRHS : 0 ≤ 9 * K * ((1 - (m : ℝ) / n) / m) * (1 + Real.log n) ^ 2 := by
    have : (m : ℝ) / n ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hmn) hn0.le
    have : 0 ≤ (1 - (m : ℝ) / n) / m := div_nonneg (by linarith) hm0.le
    positivity
  have hzero : ∀ k, twoCopySource n k = 0 → resolventQuantity n k ≤ 0 := fun k hk => by
    rw [resolventQuantity_def, hk]
    exact InvFamily.hMinusOneNormSq_le _ 0 le_rfl _ fun f => by simp [innerP, expectation]
  rcases (show m = 1 ∨ m = n ∨ (2 ≤ m ∧ m < n) by omega) with rfl | rfl | ⟨hm2, hmn'⟩
  · exact (hzero 1 (twoCopySource_one (by omega))).trans hRHS
  · exact (hzero m (twoCopySource_self (by omega))).trans hRHS
  · rw [resolventQuantity_def]
    refine InvFamily.hMinusOneNormSq_le _ _ hRHS _ fun f => ?_
    set ν := unif (TwoCopyState (ZMod n) m)
    set M₁ := univ.filter fun x : ZMod n => x.val % 2 = 0 ∧ x.val + 2 ≤ n
    set M₂ := univ.filter fun x : ZMod n => x.val % 2 = 1 ∧ x.val + 2 ≤ n
    set M₃ := univ.filter fun x : ZMod n => x.val + 1 = n
    have hsum : innerP ν f (twoCopySource n m) =
        innerP ν f (blockSource n m M₁ univ) + innerP ν f (blockSource n m M₂ univ) +
          innerP ν f (blockSource n m M₃ univ) := by
      simp only [innerP, expectation, twoCopySource_eq_sum_blockSource m,
        mul_add, sum_add_distrib, M₁, M₂, M₃]
    have hz : ((n - 1 : ℕ) : ZMod n).val = n - 1 := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have hz₁ : ((n - 1 : ℕ) : ZMod n) ∉ M₁ := by
      simp only [M₁, mem_filter, mem_univ, true_and, hz]; omega
    have hz₂ : ((n - 1 : ℕ) : ZMod n) ∉ M₂ := by
      simp only [M₂, mem_filter, mem_univ, true_and, hz]; omega
    have hz₃ : (0 : ZMod n) ∉ M₃ := by
      simp only [M₃, mem_filter, mem_univ, true_and, ZMod.val_zero]; omega
    have h₁ := hmatch n hn m hm2 hmn' _ M₁ (isCycleMatching_parity (by omega) 0) hz₁ f
    have h₂ := hmatch n hn m hm2 hmn' _ M₂ (isCycleMatching_parity (by omega) 1) hz₂ f
    have h₃ := hmatch n hn m hm2 hmn' _ M₃ isCycleMatching_last hz₃ f
    have heq : 9 * K * ((1 - (m : ℝ) / n) / m) * (1 + Real.log n) ^ 2 *
        (twoCopy n m).dirichletForm f =
          9 * (K * (((n : ℝ) - m) / (n * m)) * (1 + Real.log n) ^ 2 *
            (twoCopy n m).dirichletForm f) := by
      field_simp
    rw [hsum, heq]
    nlinarith [sq_nonneg (innerP ν f (blockSource n m M₁ univ) -
        innerP ν f (blockSource n m M₂ univ)),
      sq_nonneg (innerP ν f (blockSource n m M₂ univ) - innerP ν f (blockSource n m M₃ univ)),
      sq_nonneg (innerP ν f (blockSource n m M₁ univ) - innerP ν f (blockSource n m M₃ univ))]

end CycleCutoff
