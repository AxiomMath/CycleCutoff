/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Multiscale.Defs

/-!
# The block mean is a conditional expectation

For every block `B ⊆ ℤ/nℤ`, the block mean `F_B` is the conditional expectation of the block source
`g_{M,B}` under the uniform measure `ϖ_{n,m}` given the block projection
`π_B(R, X, Y) = (R ∖ B, X^B, Y^B)`.

## Main results

* `CycleCutoff.sum_fiber_blockProj`: a sum over a fibre of `π_B` inside `{X, Y ∈ B}` of a function
  of `(R ∩ B, X, Y)` is a sum over `k`-subsets `S ⊆ B` and pairs `(x, y) ∈ S × S`.
* `CycleCutoff.blockMean_eq_condExp`: `F_B = 𝔼_{ϖ_{n,m}}[g_{M,B} ∣ π_B]`.

## Implementation notes

The paper states the lemma for non-empty `B`, `n ≥ 3`, `1 ≤ m ≤ n` and a matching `M`. The identity
holds for every `B` and every `M` (both sides vanish for `|B| ≤ 1`); the only hypothesis is
`2 ≤ n`.
-/

public section

open Finset

namespace CycleCutoff

variable {n : ℕ} [NeZero n] {m : ℕ}

/-- For distinct `i, j ∈ B` and `k ≥ 1`, `∑_{S ⊆ B, |S| = k} 1[i ∈ S] (1[j ∈ S] - q)
= (C(s, k) k / s) ((k - 1)/(s - 1) - q)`, `s = |B|`. -/
private theorem sum_powersetCard_ite_mem {α : Type*} [DecidableEq α] (B : Finset α) (k : ℕ)
    (hk : 1 ≤ k) {i j : α} (hi : i ∈ B) (hj : j ∈ B) (hij : i ≠ j) (q : ℝ) :
    ∑ S ∈ powersetCard k B, (if i ∈ S then ((if j ∈ S then (1 : ℝ) else 0) - q) else 0) =
      (B.card.choose k : ℝ) * k / #B * (((k : ℝ) - 1) / ((#B : ℝ) - 1) - q) := by
  have h1 : ∀ S : Finset α, (if i ∈ S then ((if j ∈ S then (1 : ℝ) else 0) - q) else 0) =
      (if {i, j} ⊆ S then 1 else 0) - q * (if {i} ⊆ S then 1 else 0) := by
    intro S
    simp only [insert_subset_iff, singleton_subset_iff]
    split_ifs <;> simp_all
  have hij' : ({i, j} : Finset α) ⊆ B := by simp [insert_subset_iff, hi, hj]
  simp only [h1, sum_sub_distrib, ← mul_sum, sum_boole]
  have hs2 : 2 ≤ #B := by simpa [card_pair hij] using card_le_card hij'
  obtain ⟨s, hs⟩ : ∃ s, #B = s + 2 := ⟨#B - 2, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [card_filter_powersetCard_subset {i} _ _ (by simpa using hi) (by simp), card_singleton, hs]
  have hc1 : ((s + 2).choose (k + 1) : ℝ) = (s + 2) * (s + 1).choose k / (k + 1) := by
    rw [eq_div_iff (by positivity)]
    exact_mod_cast (Nat.add_one_mul_choose_eq (s + 1) k).symm
  have e1 : s + 2 - 1 = s + 1 := by omega
  have e1' : (s : ℝ) + 2 - 1 = s + 1 := by ring
  rw [e1, Nat.add_sub_cancel]
  rcases k with _ | k
  · have h0 : (powersetCard (0 + 1) B).filter (fun S => ({i, j} : Finset α) ⊆ S) = ∅ := by
      refine filter_false_of_mem fun S hS hsub => ?_
      have := card_le_card hsub
      rw [card_pair hij, (mem_powersetCard.1 hS).2] at this
      omega
    rw [h0, hc1, card_empty]
    push_cast
    rw [e1']
    field_simp
    ring
  · rw [card_filter_powersetCard_subset _ _ _ hij' (by rw [card_pair hij]; omega), card_pair hij,
      hs, hc1]
    have hc2 : ((s + 1).choose (k + 1) : ℝ) = (s + 1) * s.choose k / (k + 1) := by
      rw [eq_div_iff (by positivity)]
      exact_mod_cast (Nat.add_one_mul_choose_eq s k).symm
    have e3 : s + 2 - 2 = s := by omega
    have e4 : k + 1 + 1 - 2 = k := by omega
    rw [e3, e4, hc2]
    push_cast
    rw [e1']
    field_simp
    ring

private theorem sum_sum_ite_diag {α : Type*} [DecidableEq α] (S : Finset α) (i : α) (c : ℝ) :
    ∑ a ∈ S, ∑ b ∈ S, (if a = i ∧ b = i then (1 : ℝ) else 0) * c = if i ∈ S then c else 0 := by
  split_ifs with h <;> simp [ite_and, sum_ite_eq', h]

/-- The fibre of `π_B` through a state with `X, Y ∈ B`: the states with the same red set outside
`B` and both auxiliary coordinates in `B`. -/
theorem mem_fiber_blockProj {B : Finset (ZMod n)} {w v : TwoCopyState (ZMod n) m}
    (hx : w.x ∈ B) (hy : w.y ∈ B) :
    v ∈ fiber (blockProj B) w ↔ v.R \ B = w.R \ B ∧ v.x ∈ B ∧ v.y ∈ B := by
  simp [mem_fiber, blockProj, hx, hy]

/-- The event `{X, Y ∈ B}` is `π_B`-measurable: off it, the whole fibre is off it. -/
theorem not_mem_of_mem_fiber_blockProj {B : Finset (ZMod n)} {w v : TwoCopyState (ZMod n) m}
    (h : ¬(w.x ∈ B ∧ w.y ∈ B)) (hv : v ∈ fiber (blockProj B) w) : ¬(v.x ∈ B ∧ v.y ∈ B) := by
  rw [mem_fiber, blockProj, blockProj] at hv
  simp only [Prod.mk.injEq] at hv
  obtain ⟨-, h1, h2⟩ := hv
  rintro ⟨hx, hy⟩
  simp only [hx, hy, if_true] at h1 h2
  split_ifs at h1 h2
  simp_all

/-- On a fibre of `π_B` inside `{X, Y ∈ B}`, the internal state `(R ∩ B, X, Y)` runs exactly
once over `{(S, x, y) : S ⊆ B, |S| = k, x, y ∈ S}`, `k = |R ∩ B|`. -/
theorem sum_fiber_blockProj {B : Finset (ZMod n)} {w : TwoCopyState (ZMod n) m}
    (hx : w.x ∈ B) (hy : w.y ∈ B) (φ : Finset (ZMod n) → ZMod n → ZMod n → ℝ) :
    ∑ v ∈ fiber (blockProj B) w, φ (v.R ∩ B) v.x v.y =
      ∑ S ∈ powersetCard #(w.R ∩ B) B, ∑ a ∈ S, ∑ b ∈ S, φ S a b := by
  have hcard : ∀ v : TwoCopyState (ZMod n) m, #(v.R ∩ B) + #(v.R \ B) = m := fun v => by
    rw [card_inter_add_card_sdiff, v.card_R]
  have e : ∑ S ∈ powersetCard #(w.R ∩ B) B, ∑ a ∈ S, ∑ b ∈ S, φ S a b =
      ∑ p ∈ (powersetCard #(w.R ∩ B) B).sigma (fun S => S ×ˢ S), φ p.1 p.2.1 p.2.2 := by
    rw [sum_sigma]; simp_rw [sum_product]
  rw [e]
  refine sum_bij' (fun v _ => ⟨v.R ∩ B, v.x, v.y⟩)
    (fun p hp => ⟨((w.R \ B) ∪ p.1, p.2.1, p.2.2), ?_, ?_, ?_⟩) ?_ ?_ ?_ ?_ ?_
  · simp only [mem_sigma, mem_powersetCard, mem_product] at hp
    rw [card_union_of_disjoint (disjoint_of_subset_right hp.1.1 sdiff_disjoint), hp.1.2, add_comm,
      hcard]
  · simp only [mem_sigma, mem_product] at hp
    exact mem_union_right _ hp.2.1
  · simp only [mem_sigma, mem_product] at hp
    exact mem_union_right _ hp.2.2
  · intro v hv
    rw [mem_fiber_blockProj hx hy] at hv
    simp only [mem_sigma, mem_powersetCard, mem_product, mem_inter]
    refine ⟨⟨inter_subset_right, ?_⟩, ⟨v.x_mem, hv.2.1⟩, ⟨v.y_mem, hv.2.2⟩⟩
    have h1 := hcard v
    have h2 := hcard w
    rw [hv.1] at h1
    omega
  · intro p hp
    simp only [mem_sigma, mem_powersetCard, mem_product] at hp
    rw [mem_fiber_blockProj hx hy]
    simp only [TwoCopyState.R_mk, TwoCopyState.x_mk, TwoCopyState.y_mk]
    refine ⟨?_, hp.1.1 hp.2.1, hp.1.1 hp.2.2⟩
    rw [union_sdiff_distrib, _root_.sdiff_idem, sdiff_eq_empty_iff_subset.2 hp.1.1, union_empty]
  · intro v hv
    rw [mem_fiber_blockProj hx hy] at hv
    rw [TwoCopyState.ext_iff']
    simp only [TwoCopyState.R_mk, TwoCopyState.x_mk, TwoCopyState.y_mk, and_true]
    rw [← hv.1, sdiff_union_inter]
  · intro p hp
    simp only [mem_sigma, mem_powersetCard, mem_product] at hp
    simp only [TwoCopyState.R_mk, TwoCopyState.x_mk, TwoCopyState.y_mk]
    rw [union_inter_distrib_right, sdiff_inter_self, empty_union, inter_eq_left.2 hp.1.1]
  · intro v hv
    rfl

/-- **The block mean is a conditional expectation.** `F_B = 𝔼_{ϖ_{n,m}}[g_{M,B} ∣ π_B]`. -/
@[cycle_cutoff "lem_block_mean_condexp"]
theorem blockMean_eq_condExp (hn : 2 ≤ n) (M B : Finset (ZMod n)) :
    blockMean n m M B =
      condExp (unif (TwoCopyState (ZMod n) m)) (blockProj B) (blockSource n m M B) := by
  funext w
  rw [condExp_apply]
  simp only [unif_apply, mass, ← mul_sum, sum_const, nsmul_eq_mul]
  have hF : (0 : ℝ) < #(fiber (blockProj B) w) := by
    exact_mod_cast card_pos.2 ⟨w, mem_fiber_self _ _⟩
  have hc : (0 : ℝ) < (Fintype.card (TwoCopyState (ZMod n) m) : ℝ)⁻¹ := by
    have : 0 < Fintype.card (TwoCopyState (ZMod n) m) := Fintype.card_pos_iff.2 ⟨w⟩
    positivity
  rw [mul_comm (_ : ℝ) (Fintype.card _ : ℝ)⁻¹, mul_div_mul_left _ _ hc.ne', eq_div_iff hF.ne']
  set q : ℝ := ((m : ℝ) - 1) / ((n : ℝ) - 1) with hq
  by_cases hxy : w.x ∈ B ∧ w.y ∈ B
  swap
  · rw [blockMean, if_neg (fun h => hxy h.2), zero_mul, eq_comm]
    refine sum_eq_zero fun v hv => ?_
    have hv' := not_mem_of_mem_fiber_blockProj hxy hv
    refine sum_eq_zero fun x hx => ?_
    rw [mem_filter, insert_subset_iff, singleton_subset_iff] at hx
    have h1 : ¬(v.x = x ∧ v.y = x) := fun h => hv' ⟨h.1 ▸ hx.2.1, h.2 ▸ hx.2.1⟩
    have h2 : ¬(v.x = x + 1 ∧ v.y = x + 1) := fun h => hv' ⟨h.1 ▸ hx.2.2, h.2 ▸ hx.2.2⟩
    simp [h1, h2]
  obtain ⟨hx, hy⟩ := hxy
  have hne : ∀ x : ZMod n, x ≠ x + 1 := by
    have : Fact (1 < n) := ⟨hn⟩
    simp
  by_cases hs : 2 ≤ #B
  swap
  · have hM : M.filter (fun x => ({x, x + 1} : Finset (ZMod n)) ⊆ B) = ∅ := by
      refine filter_false_of_mem fun x _ hsub => hs ?_
      simpa [card_pair (hne x)] using card_le_card hsub
    rw [blockMean, if_neg (fun h => hs h.1), zero_mul, eq_comm]
    exact sum_eq_zero fun v _ => by rw [blockSource, hM, sum_empty]
  rw [blockMean, if_pos ⟨hs, hx, hy⟩]
  set M' := M.filter (fun x => ({x, x + 1} : Finset (ZMod n)) ⊆ B) with hM'
  set k := #(w.R ∩ B) with hk
  have hk1 : 1 ≤ k := card_pos.2 ⟨w.x, mem_inter.2 ⟨w.x_mem, hx⟩⟩
  have hcardF : (#(fiber (blockProj B) w) : ℝ) = (#B).choose k * (k * k) := by
    rw [card_eq_sum_ones, Nat.cast_sum]
    have := sum_fiber_blockProj hx hy (fun _ _ _ => (1 : ℝ))
    simp only [Nat.cast_one] at this ⊢
    rw [this]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    rw [sum_congr rfl fun S hS => by rw [(mem_powersetCard.1 hS).2]]
    simp [sum_const, card_powersetCard]
    rfl
  have hsrc : ∀ v : TwoCopyState (ZMod n) m, blockSource n m M B v =
      ∑ x ∈ M', ((if v.x = x ∧ v.y = x then 1 else 0) *
          ((if x + 1 ∈ v.R ∩ B then 1 else 0) - q) +
        (if v.x = x + 1 ∧ v.y = x + 1 then 1 else 0) * ((if x ∈ v.R ∩ B then 1 else 0) - q)) := by
    intro v
    refine sum_congr rfl fun x hx => ?_
    rw [hM', mem_filter, insert_subset_iff, singleton_subset_iff] at hx
    simp only [mem_inter, hx.2.1, hx.2.2, and_true]
    rfl
  simp only [hsrc]
  rw [sum_comm]
  have hterm : ∀ x ∈ M', ∑ v ∈ fiber (blockProj B) w,
      ((if v.x = x ∧ v.y = x then 1 else 0) * ((if x + 1 ∈ v.R ∩ B then 1 else 0) - q) +
        (if v.x = x + 1 ∧ v.y = x + 1 then 1 else 0) * ((if x ∈ v.R ∩ B then 1 else 0) - q)) =
      2 * (((#B).choose k : ℝ) * k / #B * (((k : ℝ) - 1) / ((#B : ℝ) - 1) - q)) := by
    intro x hxM
    rw [hM', mem_filter, insert_subset_iff, singleton_subset_iff] at hxM
    rw [sum_fiber_blockProj hx hy (fun S a b =>
      (if a = x ∧ b = x then 1 else 0) * ((if x + 1 ∈ S then 1 else 0) - q) +
        (if a = x + 1 ∧ b = x + 1 then 1 else 0) * ((if x ∈ S then 1 else 0) - q))]
    simp only [sum_add_distrib, sum_sum_ite_diag]
    rw [sum_powersetCard_ite_mem B k hk1 hxM.2.1 hxM.2.2 (hne x),
      sum_powersetCard_ite_mem B k hk1 hxM.2.2 hxM.2.1 (hne x).symm]
    ring
  rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul, hcardF]
  have hs0 : (#B : ℝ) ≠ 0 := by positivity
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  simp only [hq]
  field_simp

end CycleCutoff
