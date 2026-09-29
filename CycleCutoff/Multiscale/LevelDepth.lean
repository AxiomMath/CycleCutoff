/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Multiscale.Defs
public import CycleCutoff.Multiscale.SplitBalance
public import CycleCutoff.Multiscale.LevelStructure
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Depth of the level partitions

Let `M` be a matching of the cycle `ℤ/nℤ` and `z` a point with `e_z ∉ M`. If `L ≥ 4 log n`, every
block of the level partition `𝒫_L` is an atom of `𝔄_{M,z}`.

## Main results

* `CycleCutoff.mem_cutAtoms_of_mem_levelPartition`: for `L ≥ 4 log n`, every block of `𝒫_L` is an
  atom.

## Implementation notes

The paper's standing assumption `n ≥ 3` is not needed.
-/

public section

open Finset

namespace CycleCutoff

variable {n : ℕ} [NeZero n] {z : ZMod n} {M : Finset (ZMod n)}

/-- A non-atom block `(a, b)` of `𝒫_ℓ` has `4^ℓ (b - a) ≤ 3^ℓ n`. -/
private theorem pow_mul_le_of_mem_levelPartition (hM : IsCycleMatching n M) (hz : z ∉ M)
    (ℓ : ℕ) : ∀ B ∈ levelPartition n z M ℓ, B ∉ cutAtoms n z M →
      4 ^ ℓ * (B.2 - B.1) ≤ 3 ^ ℓ * n := by
  induction ℓ with
  | zero =>
    intro B hB _
    rw [levelPartition_zero, mem_singleton] at hB
    subst hB
    simp
  | succ ℓ ih =>
    intro B hB hBA
    rw [levelPartition_succ, mem_biUnion] at hB
    obtain ⟨C, hC, hBC⟩ := hB
    by_cases hCA : C ∈ cutAtoms n z M
    · rw [splitInterval_of_mem_cutAtoms n hCA, mem_singleton] at hBC
      exact absurd (hBC ▸ hCA) hBA
    obtain ⟨p, hp₁, hp₂, hsplit, h₁, h₂⟩ := splitInterval_balanced hM hz hC hCA
    have hCn := ((levelPartition_structure hz ℓ).1 C hC).2.1
    rw [card_cutInterval hCn, card_cutInterval (by omega)] at h₁
    rw [card_cutInterval hCn, card_cutInterval hCn] at h₂
    have hB4 : 4 * (B.2 - B.1) ≤ 3 * (C.2 - C.1) := by
      rw [hsplit, mem_insert, mem_singleton] at hBC
      rcases hBC with rfl | rfl <;> simp only <;> omega
    calc 4 ^ (ℓ + 1) * (B.2 - B.1) = 4 ^ ℓ * (4 * (B.2 - B.1)) := by ring
      _ ≤ 4 ^ ℓ * (3 * (C.2 - C.1)) := Nat.mul_le_mul_left _ hB4
      _ = 3 * (4 ^ ℓ * (C.2 - C.1)) := by ring
      _ ≤ 3 * (3 ^ ℓ * n) := Nat.mul_le_mul_left _ (ih C hC hCA)
      _ = 3 ^ (ℓ + 1) * n := by ring

/-- **Depth of the level partitions.** If `L ≥ 4 log n`, every block of the level partition
`𝒫_L` is an atom of `𝔄_{M,z}`. -/
@[cycle_cutoff "lem_level_depth"]
theorem mem_cutAtoms_of_mem_levelPartition (hM : IsCycleMatching n M) (hz : z ∉ M)
    {L : ℕ} (hL : 4 * Real.log n ≤ L) {B : ℕ × ℕ} (hB : B ∈ levelPartition n z M L) :
    B ∈ cutAtoms n z M := by
  by_contra hBA
  have hpow := pow_mul_le_of_mem_levelPartition hM hz L B hB hBA
  obtain ⟨p, hp₁, hp₂, -⟩ := splitInterval_balanced hM hz hB hBA
  have h2 : 4 ^ L * 2 ≤ 3 ^ L * n :=
    (Nat.mul_le_mul_left _ (by omega : 2 ≤ B.2 - B.1)).trans hpow
  have h2' : ((4 : ℝ) ^ L * 2) ≤ (3 : ℝ) ^ L * n := by exact_mod_cast h2
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_neZero n
  have hlog := Real.log_le_log (by positivity) h2'
  rw [Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) hn.ne',
    Real.log_pow, Real.log_pow] at hlog
  have h43 : (1 : ℝ) / 4 ≤ Real.log 4 - Real.log 3 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
    norm_num at this ⊢
    linarith
  have hlogn : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne n))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  nlinarith

end CycleCutoff
