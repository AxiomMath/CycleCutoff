/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Multiscale.Defs

/-!
# Structure of the level partitions

For a set `M` of edges of the cycle `ℤ/nℤ` and a point `z` with `e_z ∉ M`, for every `ℓ` the level
partition `𝒫_ℓ` of the cycle cut at the edge `e_z` is a partition of `ℤ/nℤ` into intervals
`I^z[a, b)`, each of which is a union of atoms of `𝔄_{M,z}`.

## Main results

* `CycleCutoff.levelPartition_structure`: every block `(a, b) ∈ 𝒫_ℓ` has `a < b ≤ n` and its set
  `I^z[a, b)` is a union of atom sets, and every `x : ZMod n` lies in the set of exactly one block
  of `𝒫_ℓ`.

## Implementation notes

The paper states the lemma under the standing assumptions `n ≥ 3` and `M` a matching. Neither is
needed: only `e_z ∉ M` is assumed.
-/

public section

open Finset

namespace CycleCutoff

variable {n : ℕ} {z : ZMod n} {M : Finset (ZMod n)}

/-- The position `c` is aligned with the atoms: no atom `(A.1, A.2)` has `A.1 < c < A.2`. -/
private def IsAligned (n : ℕ) (z : ZMod n) (M : Finset (ZMod n)) (c : ℕ) : Prop :=
  ∀ A ∈ cutAtoms n z M, ¬ (A.1 < c ∧ c < A.2)

/-- Every position `q < n` lies in some atom, provided `e_z ∉ M`. -/
private theorem exists_mem_cutAtoms (hz : z ∉ M) {q : ℕ} (hq : q < n) :
    ∃ A ∈ cutAtoms n z M, A.1 ≤ q ∧ q < A.2 := by
  by_cases h1 : z + 1 + (q : ZMod n) ∈ M
  · have hq' : q < n - 1 := by
      by_contra h
      obtain rfl : q = n - 1 := by omega
      apply hz
      have : z + 1 + ((n - 1 : ℕ) : ZMod n) = z := by simp [Nat.cast_sub (by omega : 1 ≤ n)]
      rwa [this] at h1
    exact ⟨(q, q + 2), (mem_cutAtoms n).2 (Or.inl ⟨hq', h1, rfl⟩), le_rfl, by simp⟩
  by_cases h2 : z + 1 + (q : ZMod n) - 1 ∈ M
  · obtain _ | q := q
    · exact absurd (by simpa using h2) hz
    · have : z + 1 + ((q + 1 : ℕ) : ZMod n) - 1 = z + 1 + (q : ZMod n) := by push_cast; ring
      rw [this] at h2
      exact ⟨(q, q + 2), (mem_cutAtoms n).2 (Or.inl ⟨by omega, h2, rfl⟩), by simp, by simp⟩
  exact ⟨(q, q + 1), (mem_cutAtoms n).2 (Or.inr ⟨hq, h1, h2, rfl⟩), le_rfl, by simp⟩

/-- `split(I^z[a, b))` is either `{(a, b)}` or `{(a, p), (p, b)}` for an atom boundary
`a < p < b`. -/
private theorem splitInterval_eq_or (a b : ℕ) :
    splitInterval n z M a b = {(a, b)} ∨ ∃ p, a < p ∧ p < b ∧ IsAtomBoundary n z M a b p ∧
      splitInterval n z M a b = {(a, p), (p, b)} := by
  by_cases h : (a, b) ∈ cutAtoms n z M
  · exact Or.inl (splitInterval_of_mem_cutAtoms n h)
  cases hp : splitPoint n z M a b with
  | none => exact Or.inl (splitInterval_of_splitPoint_eq_none n hp)
  | some p =>
    right
    have hmem := List.argmin_mem (by rw [splitPoint] at hp; exact hp)
    rw [List.mem_filter, List.mem_range'_1] at hmem
    exact ⟨p, by omega, by omega, by simpa using hmem.2, splitInterval_of_splitPoint n h hp⟩

/-- An atom boundary is aligned. -/
private theorem isAligned_of_isAtomBoundary {a b p : ℕ} (hap : a < p) (hpb : p < b)
    (hp : IsAtomBoundary n z M a b p) : IsAligned n z M p := by
  rintro A hA ⟨h1, h2⟩
  refine hp ⟨A, hA, ⟨z + 1 + ((p - 1 : ℕ) : ZMod n), ?_⟩, ⟨z + 1 + (p : ZMod n), ?_⟩⟩
  · rw [mem_inter, mem_cutInterval, mem_cutInterval]
    exact ⟨⟨p - 1, by omega, by omega, rfl⟩, ⟨p - 1, by omega, by omega, rfl⟩⟩
  · rw [mem_inter, mem_cutInterval, mem_cutInterval]
    exact ⟨⟨p, by omega, by omega, rfl⟩, ⟨p, le_rfl, hpb, rfl⟩⟩

/-- Every block of `split(I^z[a, b))` is a nonempty subinterval of `[a, b)` with aligned
endpoints, when `[a, b)` is itself nonempty with aligned endpoints. -/
private theorem mem_splitInterval_bounds {a b : ℕ} (hlt : a < b) (ha : IsAligned n z M a)
    (hb : IsAligned n z M b) {B : ℕ × ℕ} (hB : B ∈ splitInterval n z M a b) :
    a ≤ B.1 ∧ B.2 ≤ b ∧ B.1 < B.2 ∧ IsAligned n z M B.1 ∧ IsAligned n z M B.2 := by
  rcases splitInterval_eq_or (n := n) (z := z) (M := M) a b with h | ⟨p, hap, hpb, hp, h⟩
  · rw [h, mem_singleton] at hB
    subst hB
    exact ⟨le_rfl, le_rfl, hlt, ha, hb⟩
  · have hp' := isAligned_of_isAtomBoundary hap hpb hp
    rw [h, mem_insert, mem_singleton] at hB
    rcases hB with rfl | rfl
    · exact ⟨le_rfl, hpb.le, hap, ha, hp'⟩
    · exact ⟨hap.le, le_rfl, hpb, hp', hb⟩

/-- The blocks of `𝒫_ℓ` are intervals of positions with aligned endpoints which partition
`[0, n)`. -/
private theorem levelPartition_invariant [NeZero n] (ℓ : ℕ) :
    (∀ B ∈ levelPartition n z M ℓ,
      B.1 < B.2 ∧ B.2 ≤ n ∧ IsAligned n z M B.1 ∧ IsAligned n z M B.2) ∧
    (∀ q < n, ∃ B ∈ levelPartition n z M ℓ, B.1 ≤ q ∧ q < B.2) ∧
    (∀ B ∈ levelPartition n z M ℓ, ∀ B' ∈ levelPartition n z M ℓ, ∀ q,
      B.1 ≤ q → q < B.2 → B'.1 ≤ q → q < B'.2 → B = B') := by
  induction ℓ with
  | zero =>
    simp only [levelPartition_zero, mem_singleton]
    refine ⟨?_, fun q hq => ⟨(0, n), rfl, Nat.zero_le _, hq⟩,
      fun _ hB _ hB' _ _ _ _ _ => hB.trans hB'.symm⟩
    rintro B rfl
    refine ⟨Nat.pos_of_neZero n, le_rfl, fun A _ h => Nat.not_lt_zero _ h.1, ?_⟩
    rintro A hA ⟨-, h⟩
    have := snd_le_of_mem_cutAtoms hA
    omega
  | succ ℓ ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    rw [levelPartition_succ]
    have key : ∀ B ∈ levelPartition n z M ℓ, ∀ B' ∈ splitInterval n z M B.1 B.2,
        B.1 ≤ B'.1 ∧ B'.2 ≤ B.2 ∧ B'.1 < B'.2 ∧ IsAligned n z M B'.1 ∧
          IsAligned n z M B'.2 := by
      intro B hB B' hB'
      obtain ⟨hlt, -, ha, hb⟩ := ih1 B hB
      exact mem_splitInterval_bounds hlt ha hb hB'
    refine ⟨?_, ?_, ?_⟩
    · intro B' hB'
      obtain ⟨B, hB, hB'⟩ := mem_biUnion.1 hB'
      obtain ⟨-, h2, h3, h4, h5⟩ := key B hB B' hB'
      exact ⟨h3, h2.trans (ih1 B hB).2.1, h4, h5⟩
    · intro q hq
      obtain ⟨B, hB, h1, h2⟩ := ih2 q hq
      rcases splitInterval_eq_or (n := n) (z := z) (M := M) B.1 B.2 with
        h | ⟨p, hap, hpb, -, h⟩
      · exact ⟨B, mem_biUnion.2 ⟨B, hB, by rw [h]; exact mem_singleton_self _⟩, h1, h2⟩
      · by_cases hqp : q < p
        · exact ⟨(B.1, p), mem_biUnion.2 ⟨B, hB, by rw [h]; simp⟩, h1, hqp⟩
        · exact ⟨(p, B.2), mem_biUnion.2 ⟨B, hB, by rw [h]; simp⟩, Nat.le_of_not_lt hqp, h2⟩
    · intro B₁ h₁ B₂ h₂ q hq₁ hq₁' hq₂ hq₂'
      obtain ⟨C₁, hC₁, h₁⟩ := mem_biUnion.1 h₁
      obtain ⟨C₂, hC₂, h₂⟩ := mem_biUnion.1 h₂
      have k₁ := key C₁ hC₁ B₁ h₁
      have k₂ := key C₂ hC₂ B₂ h₂
      obtain rfl := ih3 C₁ hC₁ C₂ hC₂ q (by omega) (by omega) (by omega) (by omega)
      rcases splitInterval_eq_or (n := n) (z := z) (M := M) C₁.1 C₁.2 with
        h | ⟨p, hap, hpb, -, h⟩
      · rw [h, mem_singleton] at h₁ h₂
        rw [h₁, h₂]
      · rw [h, mem_insert, mem_singleton] at h₁ h₂
        rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> first | rfl | (simp at *; omega)

/-- **Structure of the level partitions.** Every block `(a, b)` of `𝒫_ℓ` satisfies
`a < b ≤ n`, and its set `I^z[a, b)` is a union of atoms of `𝔄_{M,z}`; every `x : ZMod n` lies
in the set of exactly one block of `𝒫_ℓ`. -/
@[cycle_cutoff "lem_level_structure"]
theorem levelPartition_structure [NeZero n] (hz : z ∉ M) (ℓ : ℕ) :
    (∀ B ∈ levelPartition n z M ℓ, B.1 < B.2 ∧ B.2 ≤ n ∧
      ∃ S ⊆ cutAtoms n z M, cutInterval n z B.1 B.2 = S.biUnion fun A => cutInterval n z A.1 A.2) ∧
    ∀ x : ZMod n, ∃! B : ℕ × ℕ, B ∈ levelPartition n z M ℓ ∧ x ∈ cutInterval n z B.1 B.2 := by
  obtain ⟨h1, h2, h3⟩ := levelPartition_invariant (n := n) (z := z) (M := M) ℓ
  refine ⟨fun B hB => ?_, fun x => ?_⟩
  · obtain ⟨hlt, hle, ha, hb⟩ := h1 B hB
    refine ⟨hlt, hle, (cutAtoms n z M).filter fun A => B.1 ≤ A.1 ∧ A.2 ≤ B.2,
      filter_subset _ _, ?_⟩
    ext x
    simp only [mem_biUnion, mem_filter, mem_cutInterval]
    constructor
    · rintro ⟨q, hq₁, hq₂, rfl⟩
      obtain ⟨A, hA, hA₁, hA₂⟩ := exists_mem_cutAtoms hz (show q < n by omega)
      have := ha A hA
      have := hb A hA
      exact ⟨A, ⟨hA, by omega, by omega⟩, q, hA₁, hA₂, rfl⟩
    · rintro ⟨A, ⟨-, hA₁, hA₂⟩, q, hq₁, hq₂, rfl⟩
      exact ⟨q, by omega, by omega, rfl⟩
  · have hq : (x - z - 1).val < n := ZMod.val_lt _
    have hx : z + 1 + ((x - z - 1).val : ZMod n) = x := by simp
    obtain ⟨B, hB, hB₁, hB₂⟩ := h2 _ hq
    refine ⟨B, ⟨hB, (mem_cutInterval n).2 ⟨_, hB₁, hB₂, hx⟩⟩, ?_⟩
    rintro B' ⟨hB', hx'⟩
    obtain ⟨q', hq₁, hq₂, hq'⟩ := (mem_cutInterval n).1 hx'
    have hle := (h1 B' hB').2.1
    obtain rfl : q' = (x - z - 1).val := eq_of_add_natCast_eq (by omega) hq (hq'.trans hx.symm)
    exact h3 B' hB' B hB _ hq₁ hq₂ hB₁ hB₂

end CycleCutoff
