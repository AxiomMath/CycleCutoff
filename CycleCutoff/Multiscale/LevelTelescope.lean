/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Multiscale.Defs
public import CycleCutoff.Multiscale.LevelStructure

/-!
# Telescoping over levels

Let `M` be a matching of the cycle `ℤ/nℤ` and `z` a point with `e_z ∉ M`. For every level `L`,
`g_{M,ℤ/nℤ} = ∑_{B ∈ 𝒫_L} (g_{M,B} - F_B) + ∑_{ℓ < L} ∑_{B ∈ 𝒫_ℓ ∖ 𝔄_{M,z}} U_B`.

## Main results

* `CycleCutoff.blockSource_univ_eq_sum`: the telescoping identity.

## Implementation notes

The paper states the identity under the hypothesis that every block of `𝒫_L` is an atom, and under
the standing assumptions `n ≥ 3`, `1 ≤ m ≤ n`. None of these is needed: the identity holds for
every `L`, assuming only `e_z ∉ M` and that `M` is a matching.
-/

public section

open Finset

namespace CycleCutoff

variable {n : ℕ} [NeZero n] {m : ℕ} {z : ZMod n} {M : Finset (ZMod n)}

/-- The interval `I^z[0, n)` is the whole cycle. -/
theorem cutInterval_zero_self : cutInterval n z 0 n = univ := by
  refine eq_univ_of_forall fun x =>
    (mem_cutInterval n).2 ⟨(x - z - 1).val, Nat.zero_le _, ZMod.val_lt _, ?_⟩
  rw [ZMod.natCast_zmod_val]
  ring

omit [NeZero n] in
/-- `I^z[a', b') ⊆ I^z[a, b)` whenever `a ≤ a'` and `b' ≤ b`. -/
theorem cutInterval_mono {a b a' b' : ℕ} (ha : a ≤ a') (hb : b' ≤ b) :
    cutInterval n z a' b' ⊆ cutInterval n z a b :=
  image_subset_image (Ico_subset_Ico ha hb)

omit [NeZero n] in
/-- The blocks of `split(I^z[a, b))` are subintervals of `[a, b)`. -/
theorem le_of_mem_splitInterval {a b : ℕ} {B : ℕ × ℕ} (hB : B ∈ splitInterval n z M a b) :
    a ≤ B.1 ∧ B.2 ≤ b := by
  by_cases h : (a, b) ∈ cutAtoms n z M
  · rw [splitInterval_of_mem_cutAtoms n h, mem_singleton] at hB
    subst hB
    exact ⟨le_rfl, le_rfl⟩
  cases hp : splitPoint n z M a b with
  | none =>
    rw [splitInterval_of_splitPoint_eq_none n hp, mem_singleton] at hB
    subst hB
    exact ⟨le_rfl, le_rfl⟩
  | some p =>
    have hmem := List.argmin_mem (by rw [splitPoint] at hp; exact hp)
    rw [List.mem_filter, List.mem_range'_1] at hmem
    rw [splitInterval_of_splitPoint n h hp, mem_insert, mem_singleton] at hB
    rcases hB with rfl | rfl
    · exact ⟨le_rfl, by simp only; omega⟩
    · exact ⟨by simp only; omega, le_rfl⟩

/-- The block mean of the whole cycle vanishes. -/
theorem blockMean_univ (w : TwoCopyState (ZMod n) m) : blockMean n m M univ w = 0 := by
  rw [blockMean, inter_univ, w.card_R, card_univ, ZMod.card]
  simp

/-- The splits of distinct blocks of `𝒫_ℓ` are disjoint. -/
theorem pairwiseDisjoint_splitInterval (hz : z ∉ M) (ℓ : ℕ) :
    (levelPartition n z M ℓ : Set (ℕ × ℕ)).PairwiseDisjoint
      fun B => splitInterval n z M B.1 B.2 := by
  intro B hB C hC hBC
  rw [Function.onFun, Finset.disjoint_left]
  intro B' hB' hC'
  have hB'mem : B' ∈ levelPartition n z M (ℓ + 1) := by
    rw [levelPartition_succ]
    exact mem_biUnion.2 ⟨B, hB, hB'⟩
  have hlt := ((levelPartition_structure hz (ℓ + 1)).1 B' hB'mem).1
  have hx : z + 1 + (B'.1 : ZMod n) ∈ cutInterval n z B'.1 B'.2 :=
    (mem_cutInterval n).2 ⟨B'.1, le_rfl, hlt, rfl⟩
  obtain ⟨hB₁, hB₂⟩ := le_of_mem_splitInterval hB'
  obtain ⟨hC₁, hC₂⟩ := le_of_mem_splitInterval hC'
  exact hBC (((levelPartition_structure hz ℓ).2 _).unique
    ⟨hB, cutInterval_mono hB₁ hB₂ hx⟩ ⟨hC, cutInterval_mono hC₁ hC₂ hx⟩)

/-- One level step: `∑_{𝒫_{ℓ+1}} F = ∑_{𝒫_ℓ} F + ∑_{𝒫_ℓ ∖ 𝔄} U`. -/
theorem sum_levelPartition_succ_blockMean (hz : z ∉ M) (ℓ : ℕ) (w : TwoCopyState (ZMod n) m) :
    ∑ B ∈ levelPartition n z M (ℓ + 1), blockMean n m M (cutInterval n z B.1 B.2) w =
      ∑ B ∈ levelPartition n z M ℓ, blockMean n m M (cutInterval n z B.1 B.2) w +
        ∑ B ∈ levelPartition n z M ℓ \ cutAtoms n z M, levelIncrement n m z M B.1 B.2 w := by
  have hU : ∑ B ∈ levelPartition n z M ℓ \ cutAtoms n z M, levelIncrement n m z M B.1 B.2 w =
      ∑ B ∈ levelPartition n z M ℓ, levelIncrement n m z M B.1 B.2 w := by
    refine sum_subset sdiff_subset fun B hB hB' => ?_
    have hA : (B.1, B.2) ∈ cutAtoms n z M := by
      by_contra h
      exact hB' (mem_sdiff.2 ⟨hB, h⟩)
    rw [levelIncrement, splitInterval_of_mem_cutAtoms n hA, sum_singleton, sub_self]
  rw [hU, levelPartition_succ, sum_biUnion (pairwiseDisjoint_splitInterval hz ℓ),
    ← sum_add_distrib]
  refine sum_congr rfl fun B _ => ?_
  rw [levelIncrement]
  ring

omit [NeZero n] in
/-- The atom containing an endpoint `x` of an edge `e_x ∈ M` also contains `x + 1`. -/
theorem add_one_mem_of_mem_cutAtoms (hM : IsCycleMatching n M) {x : ZMod n} (hx : x ∈ M)
    {A : ℕ × ℕ} (hA : A ∈ cutAtoms n z M) (hxA : x ∈ cutInterval n z A.1 A.2) :
    x + 1 ∈ cutInterval n z A.1 A.2 := by
  obtain ⟨q, hq₁, hq₂, rfl⟩ := (mem_cutInterval n).1 hxA
  rcases (mem_cutAtoms n).1 hA with ⟨-, hy, h₂⟩ | ⟨-, hy, -, h₂⟩
  · obtain rfl | rfl : q = A.1 ∨ q = A.1 + 1 := by omega
    · exact (mem_cutInterval n).2 ⟨A.1 + 1, by omega, by omega, by push_cast; ring⟩
    · by_cases hxy : z + 1 + ((A.1 + 1 : ℕ) : ZMod n) = z + 1 + (A.1 : ZMod n)
      · have : z + 1 + ((A.1 + 1 : ℕ) : ZMod n) + 1 = z + 1 + ((A.1 + 1 : ℕ) : ZMod n) := by
          conv_lhs => rw [hxy]
          push_cast
          ring
        rwa [this]
      · refine absurd (hM _ hx _ hy hxy) ?_
        rw [Finset.not_disjoint_iff]
        exact ⟨z + 1 + ((A.1 + 1 : ℕ) : ZMod n), mem_insert_self _ _, by
          rw [mem_insert, mem_singleton]; right; push_cast; ring⟩
  · obtain rfl : q = A.1 := by omega
    exact absurd hx hy

/-- The block sources of the blocks of `𝒫_ℓ` add up to the source of the whole cycle. -/
theorem sum_levelPartition_blockSource (hM : IsCycleMatching n M) (hz : z ∉ M) (ℓ : ℕ)
    (w : TwoCopyState (ZMod n) m) :
    ∑ B ∈ levelPartition n z M ℓ, blockSource n m M (cutInterval n z B.1 B.2) w =
      blockSource n m M univ w := by
  simp only [blockSource, sum_filter, subset_univ, ↓reduceIte]
  rw [sum_comm]
  refine sum_congr rfl fun x hx => ?_
  obtain ⟨B, ⟨hB, hxB⟩, huniq⟩ := (levelPartition_structure hz ℓ).2 x
  have hedge : ({x, x + 1} : Finset (ZMod n)) ⊆ cutInterval n z B.1 B.2 := by
    obtain ⟨S, hS, hBS⟩ := ((levelPartition_structure hz ℓ).1 B hB).2.2
    rw [hBS] at hxB ⊢
    obtain ⟨A, hAS, hxA⟩ := mem_biUnion.1 hxB
    rw [insert_subset_iff, singleton_subset_iff]
    exact ⟨hxB, mem_biUnion.2 ⟨A, hAS, add_one_mem_of_mem_cutAtoms hM hx (hS hAS) hxA⟩⟩
  rw [sum_eq_single_of_mem B hB, if_pos hedge]
  intro C hC hCB
  rw [if_neg]
  intro h
  exact hCB (huniq C ⟨hC, h (mem_insert_self _ _)⟩)

/-- **Telescoping over levels.** For every level `L`,
`g_{M,ℤ/nℤ} = ∑_{B ∈ 𝒫_L} (g_{M,B} - F_B) + ∑_{ℓ < L} ∑_{B ∈ 𝒫_ℓ ∖ 𝔄_{M,z}} U_B`. -/
@[cycle_cutoff "lem_level_telescope"]
theorem blockSource_univ_eq_sum (hM : IsCycleMatching n M) (hz : z ∉ M) (L : ℕ) :
    blockSource n m M univ = fun w =>
      ∑ B ∈ levelPartition n z M L,
          (blockSource n m M (cutInterval n z B.1 B.2) w -
            blockMean n m M (cutInterval n z B.1 B.2) w) +
        ∑ ℓ ∈ range L, ∑ B ∈ levelPartition n z M ℓ \ cutAtoms n z M,
          levelIncrement n m z M B.1 B.2 w := by
  funext w
  have hF : ∑ B ∈ levelPartition n z M L, blockMean n m M (cutInterval n z B.1 B.2) w =
      ∑ ℓ ∈ range L, ∑ B ∈ levelPartition n z M ℓ \ cutAtoms n z M,
        levelIncrement n m z M B.1 B.2 w := by
    have := sum_range_sub (fun ℓ => ∑ B ∈ levelPartition n z M ℓ,
      blockMean n m M (cutInterval n z B.1 B.2) w) L
    simp only [levelPartition_zero, sum_singleton, cutInterval_zero_self, blockMean_univ,
      sub_zero] at this
    rw [← this]
    refine sum_congr rfl fun ℓ _ => ?_
    rw [sum_levelPartition_succ_blockMean hz]
    ring
  rw [sum_sub_distrib, hF, sum_levelPartition_blockSource hM hz]
  ring

end CycleCutoff
