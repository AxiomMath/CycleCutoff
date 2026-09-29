/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.FiniteProbability.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# The mean of a sum over a uniformly random `k`-subset

Let `V` be a finite set with `|V| = N`, let `0 ≤ k ≤ N` and `w : V → ℝ`, and let `T` be a
uniformly random `k`-element subset of `V`. Then `𝔼[∑_{y ∈ T} w y] = (k / N) ∑_{y ∈ V} w y`.
Each `y ∈ V` lies in exactly `(N - 1).choose (k - 1)` of the `N.choose k` subsets, and
`(N - 1).choose (k - 1) / N.choose k = k / N`.

## Main definitions

* `CycleCutoff.sampleAvg k F`: the average of `F` over the `k`-element subsets of `V`, that
  is, the expectation of `F T` for a uniformly random `k`-subset `T`.

## Main results

* `CycleCutoff.sampleAvg_sum`: the mean of `∑_{y ∈ T} w y` is `(k / |V|) ∑_y w y`.
* `CycleCutoff.sampleAvg_mono`: `sampleAvg` is monotone.
* `CycleCutoff.sampleAvg_div_const`: `sampleAvg` commutes with division by a constant.
* `CycleCutoff.sampleAvg_affine`: `sampleAvg` is affine in its argument.
* `CycleCutoff.sampleAvg_sub_const_sq`: `𝔼[(X - a)²] = Var X + (𝔼 X - a)²`.
-/

@[expose] public section

open Finset

namespace CycleCutoff

/-- The average of `F` over the `k`-element subsets of `V` (the expectation for a uniformly
random `k`-subset `T`). -/
noncomputable def sampleAvg {V : Type*} [Fintype V] (k : ℕ) (F : Finset V → ℝ) : ℝ :=
  (∑ T ∈ (Finset.univ : Finset V).powersetCard k, F T) / ((Fintype.card V).choose k : ℝ)

end CycleCutoff

end

public section

open Finset

namespace CycleCutoff

/-- **The mean of a sum over a uniformly random subset.** For a uniformly random `k`-subset
`T` of `V`, `𝔼[∑_{y ∈ T} w y] = (k / |V|) ∑_y w y`. -/
@[cycle_cutoff "lem_sample_sum_mean"]
theorem sampleAvg_sum {V : Type*} [Fintype V] (k : ℕ) (hk : k ≤ Fintype.card V) (w : V → ℝ) :
    sampleAvg k (fun T => ∑ y ∈ T, w y) = (k : ℝ) / Fintype.card V * ∑ y, w y := by
  classical
  unfold sampleAvg
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  have hcount : ∀ y : V, #((univ.powersetCard k).filter (fun T : Finset V => y ∈ T))
      = (Fintype.card V - 1).choose (k - 1) := by
    intro y
    simpa using card_filter_powersetCard_subset {y} (univ : Finset V) k (subset_univ _)
      (by rw [card_singleton]; exact hk0)
  have hswap : ∑ T ∈ (univ : Finset V).powersetCard k, ∑ y ∈ T, w y
      = ((Fintype.card V - 1).choose (k - 1) : ℝ) * ∑ y, w y := by
    calc ∑ T ∈ (univ : Finset V).powersetCard k, ∑ y ∈ T, w y
        = ∑ T ∈ (univ : Finset V).powersetCard k, ∑ y, if y ∈ T then w y else 0 := by
          refine sum_congr rfl fun T _ => ?_
          rw [← sum_filter]; congr 1; ext; simp
      _ = ∑ y, ∑ T ∈ (univ : Finset V).powersetCard k, if y ∈ T then w y else 0 := sum_comm
      _ = ∑ y, ((Fintype.card V - 1).choose (k - 1) : ℝ) * w y := by
          refine sum_congr rfl fun y _ => ?_
          rw [← sum_filter, sum_const, hcount, nsmul_eq_mul]
      _ = _ := by rw [mul_sum]
  have hN : 0 < Fintype.card V := hk0.trans_le hk
  have hid : (Fintype.card V : ℝ) * ((Fintype.card V - 1).choose (k - 1) : ℝ)
      = (k : ℝ) * ((Fintype.card V).choose k : ℝ) := by
    obtain ⟨n, hn⟩ : ∃ n, Fintype.card V = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hN).symm⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hk0).symm⟩
    rw [hn]
    simp only [Nat.add_sub_cancel]
    have h := Nat.add_one_mul_choose_eq n j
    rw [mul_comm _ (j + 1)] at h
    exact_mod_cast h
  have hC : ((Fintype.card V).choose k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  have hNr : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [hswap, div_eq_iff hC]
  field_simp
  linear_combination (∑ y, w y) * hid

section Linearity

variable {V : Type*} [Fintype V]

/-- `sampleAvg` is monotone. -/
theorem sampleAvg_mono {k : ℕ} {F G : Finset V → ℝ}
    (h : ∀ T ∈ (univ : Finset V).powersetCard k, F T ≤ G T) :
    sampleAvg k F ≤ sampleAvg k G :=
  div_le_div_of_nonneg_right (sum_le_sum h) (Nat.cast_nonneg _)

/-- `sampleAvg` commutes with division by a constant. -/
theorem sampleAvg_div_const (k : ℕ) (F : Finset V → ℝ) (c : ℝ) :
    sampleAvg k (fun T => F T / c) = sampleAvg k F / c := by
  unfold sampleAvg
  rw [← sum_div, div_div, div_div, mul_comm]

/-- `sampleAvg` is affine in its argument. -/
theorem sampleAvg_affine {k : ℕ} (hk : k ≤ Fintype.card V) (a b c : ℝ) (F G : Finset V → ℝ) :
    sampleAvg k (fun T => a + b * F T + c * G T) = a + b * sampleAvg k F + c * sampleAvg k G := by
  have hC : ((Fintype.card V).choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  unfold sampleAvg
  rw [sum_add_distrib, sum_add_distrib, sum_const, card_powersetCard, card_univ, ← mul_sum,
    ← mul_sum, nsmul_eq_mul]
  field_simp

/-- `𝔼[(X - a)²] = Var X + (𝔼 X - a)²` for a uniformly random `k`-subset. -/
theorem sampleAvg_sub_const_sq {k : ℕ} (hk : k ≤ Fintype.card V) (X : Finset V → ℝ) (a : ℝ) :
    sampleAvg k (fun T => (X T - a) ^ 2) =
      sampleAvg k (fun T => (X T - sampleAvg k X) ^ 2) + (sampleAvg k X - a) ^ 2 := by
  have hexp : ∀ c : ℝ, ∑ T ∈ (univ : Finset V).powersetCard k, (X T - c) ^ 2 =
      ∑ T ∈ (univ : Finset V).powersetCard k, X T ^ 2
        - 2 * c * ∑ T ∈ (univ : Finset V).powersetCard k, X T
        + ((Fintype.card V).choose k : ℝ) * c ^ 2 := by
    intro c
    simp only [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, card_powersetCard,
      card_univ, nsmul_eq_mul, mul_sum]
    congr 1
    congr 1
    exact sum_congr rfl fun T _ => by ring
  have hC : ((Fintype.card V).choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  unfold sampleAvg
  rw [hexp, hexp]
  field_simp
  ring

end Linearity

end CycleCutoff
