/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Multiscale.Defs
public import CycleCutoff.FiniteProbability.Hypergeometric

/-!
# Second moment of the block mean

Let `n ≥ 3`, `1 ≤ m ≤ n`, let `M` be a matching of the cycle `ℤ/nℤ` and let `B ⊆ ℤ/nℤ` be
non-empty. Under the uniform measure `ϖ_{n,m}` on `Ω_{n,m}`, the block mean `F_B` satisfies
`𝔼[F_B²] ≤ 8 (m/n) (1 - m/n) / (m² |B|)`.

## Main results

* `CycleCutoff.expectation_blockMean_sq_le`: `𝔼_{ϖ_{n,m}}[F_B²] ≤ 8 (m/n) (1 - m/n) / (m² |B|)`.
-/

public section

open Finset

namespace CycleCutoff

variable {n : ℕ} {m : ℕ} {M : Finset (ZMod n)}

/-- For a matching `M`, `c_B = 2 |{e ∈ M : e ⊆ B}| ≤ |B|`. -/
private theorem two_mul_card_filter_subset_le (hn : 2 ≤ n) (hM : IsCycleMatching n M)
    (B : Finset (ZMod n)) :
    2 * #(M.filter fun x => ({x, x + 1} : Finset (ZMod n)) ⊆ B) ≤ #B := by
  have : Fact (1 < n) := ⟨by omega⟩
  set S := M.filter fun x => ({x, x + 1} : Finset (ZMod n)) ⊆ B
  have hdisj : (S : Set (ZMod n)).PairwiseDisjoint fun x => ({x, x + 1} : Finset (ZMod n)) :=
    fun x hx y hy hxy => hM x (mem_filter.1 hx).1 y (mem_filter.1 hy).1 hxy
  have hcard : #(S.biUnion fun x => ({x, x + 1} : Finset (ZMod n))) = 2 * #S := by
    rw [card_biUnion hdisj, mul_comm, ← smul_eq_mul, ← sum_const]
    exact sum_congr rfl fun x _ => card_pair (by simp)
  rw [← hcard]
  exact card_le_card (biUnion_subset.2 fun x hx => (mem_filter.1 hx).2)

/-- For `s = |B| ≥ 2` the second moment of the block mean is `(c_B / s)² / m²` times the average,
over uniform `m`-subsets `R`, of `((K_B - 1)/(s - 1) - (m - 1)/(n - 1))² 1[K_B ≥ 1]` with
`K_B = |R ∩ B|`. -/
private theorem expectation_blockMean_sq_eq [NeZero n] (hm₁ : 1 ≤ m) (hm : m ≤ n)
    {B : Finset (ZMod n)} (hs : 2 ≤ #B) :
    expectation (unif (TwoCopyState (ZMod n) m)) (fun w => blockMean n m M B w ^ 2) =
      (2 * (#(M.filter fun x => ({x, x + 1} : Finset (ZMod n)) ⊆ B) : ℝ) / #B) ^ 2 /
        (m : ℝ) ^ 2 * sampleAvg m (fun R : Finset (ZMod n) => if 1 ≤ #(R ∩ B) then
          (((#(R ∩ B) : ℝ) - 1) / (#B - 1) - ((m : ℝ) - 1) / ((n : ℝ) - 1)) ^ 2 else 0) := by
  set c : ℝ := 2 * (#(M.filter fun x => ({x, x + 1} : Finset (ZMod n)) ⊆ B) : ℝ) with hc
  set q : ℕ → ℝ := fun k => ((k : ℝ) - 1) / ((#B : ℝ) - 1) - ((m : ℝ) - 1) / ((n : ℝ) - 1)
    with hq
  set H : Finset (ZMod n) → ℝ := fun R => (c / ((#B : ℝ) * #(R ∩ B)) * q #(R ∩ B)) ^ 2 with hH
  set G : Finset (ZMod n) → ℝ := fun R => if 1 ≤ #(R ∩ B) then q #(R ∩ B) ^ 2 else 0 with hG
  set f : Finset (ZMod n) × ZMod n × ZMod n → ℝ :=
    fun t => if t.2.1 ∈ B ∧ t.2.2 ∈ B then H t.1 else 0 with hf
  change _ = (c / #B) ^ 2 / (m : ℝ) ^ 2 * sampleAvg m G
  have hpt : ∀ w : TwoCopyState (ZMod n) m, blockMean n m M B w ^ 2 = f w.1 := by
    intro w
    change _ = if w.x ∈ B ∧ w.y ∈ B then H w.R else 0
    simp only [blockMean, hH, hq, hc]
    by_cases hxy : w.x ∈ B ∧ w.y ∈ B
    · rw [if_pos ⟨hs, hxy⟩, if_pos hxy]
    · rw [if_neg (fun h => hxy h.2), if_neg hxy, zero_pow two_ne_zero]
  have hfib : ∀ R : Finset (ZMod n), ∑ t ∈ R ×ˢ R, f (R, t) = (#(R ∩ B) : ℝ) ^ 2 * H R := by
    intro R
    have hK : ∑ x ∈ R, (if x ∈ B then (1 : ℝ) else 0) = #(R ∩ B) := by
      rw [sum_boole, filter_mem_eq_inter]
    rw [sum_product, sq, ← hK, sum_mul_sum]
    simp only [sum_mul]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    by_cases hx : x ∈ B <;> by_cases hy : y ∈ B <;> simp [hf, hx, hy]
  have hHG : ∀ R : Finset (ZMod n), (#(R ∩ B) : ℝ) ^ 2 * H R = (c / #B) ^ 2 * G R := by
    intro R
    simp only [hH, hG]
    by_cases hK : 1 ≤ #(R ∩ B)
    · rw [if_pos hK]
      have : (0 : ℝ) < #(R ∩ B) := Nat.cast_pos.2 hK
      field_simp
    · rw [if_neg hK]
      simp [show #(R ∩ B) = 0 by omega]
  have hcardΩ : (Fintype.card (TwoCopyState (ZMod n) m) : ℝ) =
      ((n.choose m : ℕ) : ℝ) * (m : ℝ) ^ 2 := by
    rw [TwoCopyState.card_eq, ZMod.card]
    push_cast
    ring
  rw [expectation_unif, sum_congr rfl fun w _ => hpt w, TwoCopyState.sum_eq_sum_product,
    sum_congr rfl fun R _ => (hfib R).trans (hHG R), ← mul_sum, hcardΩ, sampleAvg, ZMod.card]
  have : ((n.choose m : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos hm).ne'
  field_simp

/-- **Second moment of the block mean.** For `n ≥ 3`, `1 ≤ m ≤ n`, a matching `M` and every
non-empty `B ⊆ ℤ/nℤ`, `𝔼_{ϖ_{n,m}}[F_B²] ≤ 8 (m/n) (1 - m/n) / (m² |B|)`. -/
@[cycle_cutoff "lem_block_second_moment"]
theorem expectation_blockMean_sq_le [NeZero n] (hn : 3 ≤ n) (hm₁ : 1 ≤ m) (hm : m ≤ n)
    (hM : IsCycleMatching n M) {B : Finset (ZMod n)} (hB : B.Nonempty) :
    expectation (unif (TwoCopyState (ZMod n) m)) (fun w => blockMean n m M B w ^ 2) ≤
      8 * ((m : ℝ) / n) * (1 - (m : ℝ) / n) / ((m : ℝ) ^ 2 * #B) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (NeZero.pos n)
  have hmn : (m : ℝ) ≤ n := Nat.cast_le.2 hm
  have hB0 : (0 : ℝ) < #B := Nat.cast_pos.2 hB.card_pos
  have hρ : 0 ≤ 1 - (m : ℝ) / n := sub_nonneg.2 ((div_le_one hn0).2 hmn)
  have hrhs : 0 ≤ 8 * ((m : ℝ) / n) * (1 - (m : ℝ) / n) / ((m : ℝ) ^ 2 * #B) := by positivity
  rcases lt_or_ge #B 2 with hs | hs
  · simpa [expectation, blockMean, show ¬ 2 ≤ #B by omega] using hrhs
  have hhyp := sampleAvg_hypergeometric_le (V := ZMod n) (by rwa [ZMod.card]) m hm₁
    (by rwa [ZMod.card]) B hs
  simp only [ZMod.card] at hhyp
  rw [expectation_blockMean_sq_eq hm₁ hm hs]
  set c : ℝ := 2 * (#(M.filter fun x => ({x, x + 1} : Finset (ZMod n)) ⊆ B) : ℝ) with hc
  set G : Finset (ZMod n) → ℝ := fun R : Finset (ZMod n) => if 1 ≤ #(R ∩ B) then
    (((#(R ∩ B) : ℝ) - 1) / (#B - 1) - ((m : ℝ) - 1) / ((n : ℝ) - 1)) ^ 2 else 0 with hG
  have hG0 : 0 ≤ sampleAvg m G := by
    refine div_nonneg (sum_nonneg fun R _ => ?_) (Nat.cast_nonneg _)
    simp only [hG]
    split_ifs <;> positivity
  have hcs : c ≤ #B :=
    hc.trans_le (by exact_mod_cast two_mul_card_filter_subset_le (by omega) hM B)
  have hcs1 : (c / #B) ^ 2 ≤ 1 :=
    pow_le_one₀ (div_nonneg (by positivity) hB0.le) ((div_le_one hB0).2 hcs)
  calc (c / #B) ^ 2 / (m : ℝ) ^ 2 * sampleAvg m G
      ≤ 1 / (m : ℝ) ^ 2 * (8 * ((m : ℝ) / n) * (1 - (m : ℝ) / n) / #B) := by gcongr
    _ = 8 * ((m : ℝ) / n) * (1 - (m : ℝ) / n) / ((m : ℝ) ^ 2 * #B) := by field_simp

end CycleCutoff
