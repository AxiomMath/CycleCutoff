/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.FiniteProbability.SampleSumMean

/-!
# The variance of a sum over a uniformly random `k`-subset

Let `V` be a finite set with `|V| = N ≥ 2`, let `0 ≤ k ≤ N` and `w : V → ℝ`, and let `T` be a
uniformly random `k`-element subset of `V`. Writing `w̄ = N⁻¹ ∑_{y ∈ V} w y`,
`Var(∑_{y ∈ T} w y) = k (N - k) / (N (N - 1)) · ∑_{y ∈ V} (w y - w̄)²`.

After centring, `w` may be replaced by `u = w - w̄`, whose total is `0`. Expanding the square,
`𝔼[(∑_{y ∈ T} u y)²] = ∑_{y, y'} u y u y' ℙ(y, y' ∈ T)`, where `ℙ(y ∈ T) = k / N` and, for
`y ≠ y'`, `ℙ(y, y' ∈ T) = k (k - 1) / (N (N - 1))`; since `∑ u = 0` the off-diagonal part
contributes `-k (k - 1) / (N (N - 1)) ∑ u²`.

## Main results

* `CycleCutoff.sampleAvg_sq_sub`: the variance formula above.
-/

public section

open Finset

namespace CycleCutoff

/-- The number of `k`-subsets of `V` containing a given point `y`, times `|V|`, is
`k · C(|V|, k)`. -/
theorem card_filter_mem_mul {V : Type*} [Fintype V] [DecidableEq V] (k : ℕ)
    (hk : k ≤ Fintype.card V) (y : V) :
    (#((univ.powersetCard k).filter (fun T : Finset V => y ∈ T)) : ℝ) * Fintype.card V =
      k * (Fintype.card V).choose k := by
  have h := sampleAvg_sum k hk (fun z => if z = y then (1 : ℝ) else 0)
  simp only [sum_ite_eq', mem_univ, if_true, mul_one] at h
  unfold sampleAvg at h
  have hC : ((Fintype.card V).choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  simp only [sum_boole] at h
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hN | hN
  · have : k = 0 := by omega
    subst this
    simp
  have hNr : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [div_eq_iff hC] at h
  rw [h]
  field_simp

/-- The number of `k`-subsets of `V` containing two given distinct points, times
`|V| (|V| - 1)`, is `k (k - 1) · C(|V|, k)`. -/
theorem card_filter_mem_mem_mul {V : Type*} [Fintype V] [DecidableEq V] (k : ℕ)
    (hk : k ≤ Fintype.card V) {y y' : V} (hy : y ≠ y') :
    (#((univ.powersetCard k).filter (fun T : Finset V => y ∈ T ∧ y' ∈ T)) : ℝ) *
        (Fintype.card V * (Fintype.card V - 1)) =
      k * (k - 1) * (Fintype.card V).choose k := by
  rcases lt_or_ge k 2 with hk2 | hk2
  · have hempty : (univ.powersetCard k).filter (fun T : Finset V => y ∈ T ∧ y' ∈ T) = ∅ := by
      refine filter_eq_empty_iff.2 fun T hT hmem => ?_
      have hsub : ({y, y'} : Finset V) ⊆ T := by
        intro z hz
        rw [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl
        exacts [hmem.1, hmem.2]
      have := card_le_card hsub
      rw [card_pair hy, (mem_powersetCard.1 hT).2] at this
      omega
    rw [hempty, card_empty]
    obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    all_goals simp
  have hfilt : (univ.powersetCard k).filter (fun T : Finset V => y ∈ T ∧ y' ∈ T) =
      (univ.powersetCard k).filter (fun T : Finset V => ({y, y'} : Finset V) ⊆ T) := by
    refine filter_congr fun T _ => ?_
    simp [insert_subset_iff]
  rw [hfilt, card_filter_powersetCard_subset _ _ _ (subset_univ _)
    (by rw [card_pair hy]; exact hk2), card_pair hy, card_univ]
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card V = m + 2 := ⟨Fintype.card V - 2, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [hm]
  simp only [Nat.add_sub_cancel]
  have h1 : ((m + 1 + 1 : ℕ) : ℝ) * ((m + 1).choose (j + 1) : ℕ) =
      ((m + 1 + 1).choose (j + 1 + 1) : ℕ) * ((j + 1 + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq (m + 1) (j + 1)
  have h2 : ((m + 1 : ℕ) : ℝ) * (m.choose j : ℕ) =
      ((m + 1).choose (j + 1) : ℕ) * ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq m j
  push_cast at h1 h2 ⊢
  linear_combination (↑m + 1 + 1) * h2 + (j + 1) * h1

/-- **The variance of a sum over a uniformly random subset.** For a uniformly random
`k`-subset `T` of `V` with `|V| = N ≥ 2`,
`Var(∑_{y ∈ T} w y) = k (N - k) / (N (N - 1)) · ∑_y (w y - w̄)²`, where `w̄ = N⁻¹ ∑_y w y`. -/
@[cycle_cutoff "lem_sample_sum_variance"]
theorem sampleAvg_sq_sub {V : Type*} [Fintype V] (hN : 2 ≤ Fintype.card V) (k : ℕ)
    (hk : k ≤ Fintype.card V) (w : V → ℝ) :
    sampleAvg k (fun T => (∑ y ∈ T, w y - sampleAvg k (fun T => ∑ y ∈ T, w y)) ^ 2) =
      (k * (Fintype.card V - k) : ℝ) / (Fintype.card V * (Fintype.card V - 1)) *
        ∑ y, (w y - (Fintype.card V : ℝ)⁻¹ * ∑ y', w y') ^ 2 := by
  classical
  set N := Fintype.card V with hNdef
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hn1 : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hC : (N.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  set wbar : ℝ := (N : ℝ)⁻¹ * ∑ y', w y' with hwbar
  set u : V → ℝ := fun y => w y - wbar with hu
  have hu0 : ∑ y, u y = 0 := by
    simp only [u, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, wbar, ← hNdef]
    field_simp
    ring
  set a : ℝ := k * N.choose k / N with ha
  set b : ℝ := k * (k - 1) * N.choose k / (N * (N - 1)) with hb
  have hcnt : ∀ y y' : V,
      (#((univ.powersetCard k).filter (fun T : Finset V => y ∈ T ∧ y' ∈ T)) : ℝ) =
        if y = y' then a else b := by
    intro y y'
    split_ifs with h
    · subst h
      simp only [and_self]
      rw [ha, eq_div_iff hn]
      exact card_filter_mem_mul k hk y
    · rw [hb, eq_div_iff (mul_ne_zero hn hn1)]
      exact card_filter_mem_mem_mul k hk h
  have hmean : sampleAvg k (fun T => ∑ y ∈ T, w y) = k * wbar := by
    rw [sampleAvg_sum k hk, hwbar]
    ring
  rw [hmean]
  unfold sampleAvg
  have h1 : ∑ T ∈ univ.powersetCard k, (∑ y ∈ T, w y - k * wbar) ^ 2 =
      ∑ T ∈ univ.powersetCard k, ∑ y, ∑ y', u y * u y' * (if y ∈ T ∧ y' ∈ T then 1 else 0) := by
    refine sum_congr rfl fun T hT => ?_
    rw [mem_powersetCard] at hT
    have hS : ∑ y ∈ T, w y - k * wbar = ∑ y, if y ∈ T then u y else 0 := by
      rw [← sum_filter, filter_mem_eq_inter, univ_inter, sum_sub_distrib, sum_const, hT.2,
        nsmul_eq_mul]
    rw [hS, sq, sum_mul_sum]
    refine sum_congr rfl fun y _ => sum_congr rfl fun y' _ => ?_
    by_cases h : y ∈ T <;> by_cases h' : y' ∈ T <;> simp [h, h']
  have h2 : ∑ T ∈ univ.powersetCard k, ∑ y, ∑ y', u y * u y' *
        (if y ∈ T ∧ y' ∈ T then (1 : ℝ) else 0) =
      ∑ y, ∑ y', u y * u y' * (if y = y' then a else b) := by
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun y' _ => ?_
    rw [← mul_sum, sum_boole, hcnt]
  have h3 : ∑ y, ∑ y', u y * u y' * (if y = y' then a else b) =
      b * (∑ y, u y) ^ 2 + (a - b) * ∑ y, u y ^ 2 := by
    have : ∀ y y' : V, u y * u y' * (if y = y' then a else b) =
        b * (u y * u y') + (a - b) * (if y = y' then u y * u y' else 0) := by
      intro y y'
      split_ifs <;> ring
    simp only [this, sum_add_distrib, ← mul_sum, sum_ite_eq, mem_univ, if_true, sq,
      sum_mul_sum]
  rw [h1, h2, h3, hu0]
  simp only [u]
  rw [div_eq_iff hC, ha, hb]
  field_simp
  ring

end CycleCutoff
