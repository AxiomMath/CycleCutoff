/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Multiscale.Defs
public import CycleCutoff.Multiscale.LevelStructure

/-!
# Balanced splits

Let `M` be a matching of the cycle `ℤ/nℤ` and `z` a point with `e_z ∉ M`. If a block
`B = I^z[a, b)` of a level partition `𝒫_ℓ` is not an atom, then `split(B)` consists of two
intervals `I^z[a, p)` and `I^z[p, b)`, each with at least `|B| / 4` elements.

## Main results

* `CycleCutoff.splitInterval_balanced`: a non-atom block `B ∈ 𝒫_ℓ` splits as `{(B.1, p), (p, B.2)}`
  with `B.1 < p < B.2`, and `|I^z[B.1, B.2)| ≤ 4 |I^z[B.1, p)|`,
  `|I^z[B.1, B.2)| ≤ 4 |I^z[p, B.2)|`.

## Implementation notes

The paper's standing assumption `n ≥ 3` is not needed. The bound "at least `|B|/4` elements" is
stated in `ℕ` as `|B| ≤ 4 · |B'|`.
-/

public section

open Finset

namespace CycleCutoff

variable {n : ℕ} {z : ZMod n} {M : Finset (ZMod n)}

/-- An atom straddling the position `p` is the two-point atom `(p - 1, p + 1)`. -/
private theorem eq_of_lt_of_lt_of_mem_cutAtoms {A : ℕ × ℕ} (hA : A ∈ cutAtoms n z M) {p : ℕ}
    (h₁ : A.1 < p) (h₂ : p < A.2) :
    A = (p - 1, p + 1) ∧ z + 1 + ((p - 1 : ℕ) : ZMod n) ∈ M := by
  rcases (mem_cutAtoms n).1 hA with ⟨-, hM, h'⟩ | ⟨-, -, -, h'⟩
  · have h : A.1 = p - 1 := by omega
    exact ⟨Prod.ext h (by simp only; omega), h ▸ hM⟩
  · omega

/-- For a matching `M` with `e_z ∉ M`, no two consecutive positions are both straddled by
atoms. -/
private theorem false_of_straddle_straddle_succ (hM : IsCycleMatching n M) (hz : z ∉ M)
    {p : ℕ} {A A' : ℕ × ℕ} (hA : A ∈ cutAtoms n z M) (h₁ : A.1 < p) (h₂ : p < A.2)
    (hA' : A' ∈ cutAtoms n z M) (h₁' : A'.1 < p + 1) (h₂' : p + 1 < A'.2) : False := by
  obtain ⟨rfl, hx⟩ := eq_of_lt_of_lt_of_mem_cutAtoms hA h₁ h₂
  obtain ⟨-, hx'⟩ := eq_of_lt_of_lt_of_mem_cutAtoms hA' h₁' h₂'
  have hp : 1 ≤ p := by simp only at h₁ h₂; omega
  set x := z + 1 + ((p - 1 : ℕ) : ZMod n)
  have hx1 : z + 1 + ((p + 1 - 1 : ℕ) : ZMod n) = x + 1 := by
    simp only [x, Nat.add_sub_cancel, Nat.cast_sub hp]; ring
  rw [hx1] at hx'
  by_cases hne : x = x + 1
  · have h10 : (1 : ZMod n) = 0 := by linear_combination -hne
    have h0 : ∀ y : ZMod n, y = 0 := fun y => by simpa using congrArg (y * ·) h10
    exact hz (by rwa [h0 z, ← h0 x])
  · exact Finset.disjoint_left.1 (hM x hx (x + 1) hx' hne)
      (show x + 1 ∈ ({x, x + 1} : Finset (ZMod n)) by simp) (by simp)

/-- **Balanced splits.** If a block `B` of the level partition `𝒫_ℓ` is not an atom, then
`split(B) = {(B.1, p), (p, B.2)}` with `B.1 < p < B.2`, and each of the two intervals has at
least `|B| / 4` elements. -/
@[cycle_cutoff "lem_split_balance"]
theorem splitInterval_balanced [NeZero n] (hM : IsCycleMatching n M) (hz : z ∉ M) {ℓ : ℕ}
    {B : ℕ × ℕ} (hB : B ∈ levelPartition n z M ℓ) (hBA : B ∉ cutAtoms n z M) :
    ∃ p, B.1 < p ∧ p < B.2 ∧ splitInterval n z M B.1 B.2 = {(B.1, p), (p, B.2)} ∧
      #(cutInterval n z B.1 B.2) ≤ 4 * #(cutInterval n z B.1 p) ∧
      #(cutInterval n z B.1 B.2) ≤ 4 * #(cutInterval n z p B.2) := by
  obtain ⟨a, b⟩ := B
  obtain ⟨hab, hbn, S, hS, hSeq⟩ := (levelPartition_structure hz ℓ).1 _ hB
  dsimp only at hab hbn hSeq hBA ⊢
  have hbd : ∀ p, a < p → p < b → (∀ A ∈ cutAtoms n z M, ¬ (A.1 < p ∧ p < A.2)) →
      IsAtomBoundary n z M a b p := by
    rintro p hap hpb hp ⟨A, hA, ⟨v, hv⟩, ⟨w, hw⟩⟩
    rw [mem_inter, mem_cutInterval, mem_cutInterval] at hv hw
    obtain ⟨⟨q₁, h₁, h₁', rfl⟩, ⟨q₁', h₂, h₂', hq₁⟩⟩ := hv
    obtain ⟨⟨q₂, h₃, h₃', rfl⟩, ⟨q₂', h₄, h₄', hq₂⟩⟩ := hw
    have hA2 := snd_le_of_mem_cutAtoms hA
    obtain rfl := eq_of_add_natCast_eq (by omega) (by omega) hq₁
    obtain rfl := eq_of_add_natCast_eq (by omega) (by omega) hq₂
    exact hp A hA ⟨by omega, by omega⟩
  have hs : 2 ≤ b - a := by
    by_contra hs
    obtain rfl : b = a + 1 := by omega
    have hsub : ∀ A ∈ S, ∀ q, A.1 ≤ q → q < A.2 → q = a := by
      intro A hAS q hq hq'
      have hmem : z + 1 + (q : ZMod n) ∈ cutInterval n z a (a + 1) := by
        rw [hSeq, mem_biUnion]
        exact ⟨A, hAS, (mem_cutInterval n).2 ⟨q, hq, hq', rfl⟩⟩
      obtain ⟨q', h₁, h₂, h₃⟩ := (mem_cutInterval n).1 hmem
      have := snd_le_of_mem_cutAtoms (hS hAS)
      have := eq_of_add_natCast_eq (by omega) (by omega) h₃
      omega
    have hmem : z + 1 + (a : ZMod n) ∈ cutInterval n z a (a + 1) :=
      (mem_cutInterval n).2 ⟨a, le_rfl, by omega, rfl⟩
    rw [hSeq, mem_biUnion] at hmem
    obtain ⟨A, hAS, -⟩ := hmem
    have hAc := hS hAS
    rcases (mem_cutAtoms n).1 hAc with ⟨-, -, h'⟩ | ⟨-, -, -, h'⟩
    · have := hsub A hAS A.1 le_rfl (by omega)
      have := hsub A hAS (A.1 + 1) (by omega) (by omega)
      omega
    · have h1 : A.1 = a := hsub A hAS A.1 le_rfl (by omega)
      exact hBA (by rwa [show A = (a, a + 1) from Prod.ext h1 (by simp only; omega)] at hAc)
  have hex : ∃ p₀, a < p₀ ∧ p₀ < b ∧ IsAtomBoundary n z M a b p₀ ∧
      Int.natAbs (2 * (p₀ : ℤ) - (a + b)) ≤ 2 := by
    by_cases hc : ∀ A ∈ cutAtoms n z M, ¬ (A.1 < (a + b) / 2 ∧ (a + b) / 2 < A.2)
    · exact ⟨(a + b) / 2, by omega, by omega, hbd _ (by omega) (by omega) hc, by omega⟩
    push Not at hc
    obtain ⟨A, hA, h₁, h₂⟩ := hc
    have hs3 : 3 ≤ b - a := by
      by_contra hs3
      obtain ⟨rfl, -⟩ := eq_of_lt_of_lt_of_mem_cutAtoms hA h₁ h₂
      exact hBA (by convert hA using 2 <;> omega)
    refine ⟨(a + b) / 2 + 1, by omega, by omega, hbd _ (by omega) (by omega) ?_, by omega⟩
    rintro A' hA' ⟨h₁', h₂'⟩
    exact false_of_straddle_straddle_succ hM hz hA h₁ h₂ hA' h₁' h₂'
  obtain ⟨p₀, hp₀a, hp₀b, hp₀, hp₀d⟩ := hex
  have hL : p₀ ∈ (List.range' (a + 1) (b - a - 1)).filter
      fun p => decide (IsAtomBoundary n z M a b p) := by
    rw [List.mem_filter, List.mem_range'_1]
    exact ⟨⟨by omega, by omega⟩, by simpa using hp₀⟩
  obtain ⟨p, hp⟩ : ∃ p, splitPoint n z M a b = some p := by
    refine Option.ne_none_iff_exists'.1 ?_
    rw [splitPoint, Ne, List.argmin_eq_none]
    exact List.ne_nil_of_mem hL
  have hle := List.not_lt_of_mem_argmin hL hp
  have hpL := List.argmin_mem hp
  rw [List.mem_filter, List.mem_range'_1] at hpL
  refine ⟨p, by omega, by omega, splitInterval_of_splitPoint n hBA hp, ?_, ?_⟩ <;>
    rw [card_cutInterval hbn, card_cutInterval (by omega)] <;> omega

end CycleCutoff
