/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Multiscale.Defs
public import CycleCutoff.Multiscale.SplitBalance
public import CycleCutoff.Multiscale.BlockMeanCondExp
public import CycleCutoff.Multiscale.LevelStructure
public import CycleCutoff.Multiscale.LevelTelescope
public import CycleCutoff.FiniteProbability.CondExpTower

/-!
# The level increments are centred

Let `M` be a matching of the cycle `ℤ/nℤ` and `z` a point with `e_z ∉ M`. If a block `B` of the
level partition `𝒫_ℓ` is not an atom, with `split(B) = {B', B''}`, then its level increment
`U_B = F_{B'} + F_{B''} - F_B` has vanishing conditional expectation given the block projection
`π_B`, under the uniform measure `ϖ_{n,m}`.

## Main results

* `CycleCutoff.condExp_levelIncrement_eq_zero`: `𝔼_{ϖ_{n,m}}[U_B ∣ π_B] = 0` for a non-atom block
  `B ∈ 𝒫_ℓ`.

## Implementation notes

The paper's standing assumptions `n ≥ 3` and `1 ≤ m ≤ n` are not needed.
-/

public section

open Finset

namespace CycleCutoff

variable {n : ℕ} [NeZero n] {m : ℕ} {z : ZMod n} {M : Finset (ZMod n)}

omit [NeZero n] in
/-- For `B' ⊆ B`, the block projection `π_B` factors through `π_{B'}`. -/
private theorem blockProj_eq_comp {B B' : Finset (ZMod n)} (h : B' ⊆ B) :
    (blockProj B : TwoCopyState (ZMod n) m → _) =
      (fun t : Finset (ZMod n) × Option (ZMod n) × Option (ZMod n) =>
        (t.1 \ B, t.2.1.bind fun v => if v ∈ B then none else some v,
          t.2.2.bind fun v => if v ∈ B then none else some v)) ∘ blockProj B' := by
  funext w
  simp only [blockProj, Function.comp_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext v
    simp only [mem_sdiff]
    exact ⟨fun hv => ⟨⟨hv.1, fun hv' => hv.2 (h hv')⟩, hv.2⟩, fun hv => ⟨hv.1.1, hv.2⟩⟩
  · by_cases hx : w.x ∈ B'
    · simp [hx, h hx]
    · simp [hx]
  · by_cases hy : w.y ∈ B'
    · simp [hy, h hy]
    · simp [hy]

/-- Conditioning a coarser block mean: for `B' ⊆ B`, `𝔼[F_{B'} ∣ π_B] = 𝔼[g_{M,B'} ∣ π_B]`. -/
private theorem condExp_blockMean_of_subset (hn : 2 ≤ n) {B B' : Finset (ZMod n)} (h : B' ⊆ B) :
    condExp (unif (TwoCopyState (ZMod n) m)) (blockProj B) (blockMean n m M B') =
      condExp (unif (TwoCopyState (ZMod n) m)) (blockProj B) (blockSource n m M B') := by
  have hν : ∀ w, 0 < unif (TwoCopyState (ZMod n) m) w := unif_pos
  rw [blockProj_eq_comp h, blockMean_eq_condExp hn]
  exact condExp_condExp_comp _ hν _ _ _

/-- A point `x ∈ M` of a block of a level partition carries its edge `e_x` with it. -/
private theorem add_one_mem_of_mem_levelPartition (hM : IsCycleMatching n M) (hz : z ∉ M)
    {k : ℕ} {C : ℕ × ℕ} (hC : C ∈ levelPartition n z M k) {x : ZMod n} (hx : x ∈ M)
    (hxC : x ∈ cutInterval n z C.1 C.2) : x + 1 ∈ cutInterval n z C.1 C.2 := by
  obtain ⟨S, hS, hCS⟩ := ((levelPartition_structure hz k).1 C hC).2.2
  rw [hCS] at hxC ⊢
  obtain ⟨A, hAS, hxA⟩ := mem_biUnion.1 hxC
  exact mem_biUnion.2 ⟨A, hAS, add_one_mem_of_mem_cutAtoms hM hx (hS hAS) hxA⟩

/-- **Increments are centred.** For a block `B ∈ 𝒫_ℓ` that is not an atom,
`𝔼_{ϖ_{n,m}}[U_B ∣ π_B] = 0`. -/
@[cycle_cutoff "lem_increment_centered"]
theorem condExp_levelIncrement_eq_zero (hM : IsCycleMatching n M) (hz : z ∉ M) {ℓ : ℕ}
    {B : ℕ × ℕ} (hB : B ∈ levelPartition n z M ℓ) (hBA : B ∉ cutAtoms n z M) :
    condExp (unif (TwoCopyState (ZMod n) m)) (blockProj (cutInterval n z B.1 B.2))
      (levelIncrement n m z M B.1 B.2) = fun _ => 0 := by
  obtain ⟨a, b⟩ := B
  obtain ⟨p, hap, hpb, hsplit, -, -⟩ := splitInterval_balanced hM hz hB hBA
  dsimp only at hap hpb hsplit ⊢
  have hbn := ((levelPartition_structure hz ℓ).1 _ hB).2.1
  dsimp only at hbn
  have hn : 2 ≤ n := by omega
  have hmem : ∀ C ∈ ({(a, p), (p, b)} : Finset (ℕ × ℕ)), C ∈ levelPartition n z M (ℓ + 1) :=
    fun C hC => by
      rw [levelPartition_succ]
      exact mem_biUnion.2 ⟨(a, b), hB, hsplit ▸ hC⟩
  have h₁ := hmem (a, p) (by simp)
  have h₂ := hmem (p, b) (by simp)
  set I := cutInterval n z a b
  set I₁ := cutInterval n z a p
  set I₂ := cutInterval n z p b
  have hI : I = I₁ ∪ I₂ := by
    simp only [I, I₁, I₂, cutInterval, ← image_union, Ico_union_Ico_eq_Ico hap.le hpb.le]
  have hdisj : Disjoint I₁ I₂ := by
    refine disjoint_left.2 fun v hv₁ hv₂ => ?_
    have := ((levelPartition_structure hz (ℓ + 1)).2 v).unique ⟨h₁, hv₁⟩ ⟨h₂, hv₂⟩
    simp only [Prod.mk.injEq] at this
    omega
  have hU : levelIncrement n m z M a b =
      fun w => blockMean n m M I₁ w + blockMean n m M I₂ w - blockMean n m M I w := by
    funext w
    rw [levelIncrement, hsplit, sum_pair (by simp only [ne_eq, Prod.mk.injEq]; omega)]
  have hg : (fun w => blockSource n m M I₁ w + blockSource n m M I₂ w) =
      blockSource n m M I := by
    funext w
    simp only [blockSource, sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun x hx => ?_
    by_cases hxI : ({x, x + 1} : Finset (ZMod n)) ⊆ I
    · rw [if_pos hxI]
      have hxI' := hxI (mem_insert_self _ _)
      rw [hI, mem_union] at hxI'
      rcases hxI' with hx₁ | hx₂
      · have h1 : ({x, x + 1} : Finset (ZMod n)) ⊆ I₁ := by
          rw [insert_subset_iff, singleton_subset_iff]
          exact ⟨hx₁, add_one_mem_of_mem_levelPartition hM hz h₁ hx hx₁⟩
        have h2 : ¬({x, x + 1} : Finset (ZMod n)) ⊆ I₂ := fun h =>
          disjoint_left.1 hdisj hx₁ (h (mem_insert_self _ _))
        rw [if_pos h1, if_neg h2, add_zero]
      · have h2 : ({x, x + 1} : Finset (ZMod n)) ⊆ I₂ := by
          rw [insert_subset_iff, singleton_subset_iff]
          exact ⟨hx₂, add_one_mem_of_mem_levelPartition hM hz h₂ hx hx₂⟩
        have h1 : ¬({x, x + 1} : Finset (ZMod n)) ⊆ I₁ := fun h =>
          disjoint_left.1 hdisj (h (mem_insert_self _ _)) hx₂
        rw [if_pos h2, if_neg h1, zero_add]
    · have h1 : ¬({x, x + 1} : Finset (ZMod n)) ⊆ I₁ := fun h =>
        hxI (h.trans (hI ▸ subset_union_left))
      have h2 : ¬({x, x + 1} : Finset (ZMod n)) ⊆ I₂ := fun h =>
        hxI (h.trans (hI ▸ subset_union_right))
      rw [if_neg hxI, if_neg h1, if_neg h2, add_zero]
  rw [hU, condExp_sub, condExp_add,
    condExp_blockMean_of_subset hn (hI ▸ subset_union_left : I₁ ⊆ I),
    condExp_blockMean_of_subset hn (hI ▸ subset_union_right : I₂ ⊆ I),
    condExp_blockMean_of_subset hn (subset_refl I), ← condExp_add, hg]
  funext w
  exact sub_self _

end CycleCutoff
