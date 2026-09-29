/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Exposure.Defs
public import CycleCutoff.FiniteProbability.SampleSumVariance
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A lower bound on the mean logarithm of an exposed row sum

Let `n ≥ 3`, `1 ≤ m ≤ n`, and let `W : ℤ/n × ℤ/n → [1/2, 3/2]` have all row sums equal to `n`. For
`i ∈ ℤ/n` and `σ ∈ S_n`, let `A` be a uniformly random `m`-subset of `ℤ/n` containing `i` and
`Z = m⁻¹ ∑_{x ∈ σ(A)} W(i, x)`. Then `𝔼 log Z ≥ -3/m`.

## Main results

* `CycleCutoff.neg_three_div_le_sum_log_exposure`: `𝔼 log Z ≥ -3/m`, with the average over the
  `m`-sets `A ∋ i` written as `binom(n - 1, m - 1)⁻¹ ∑_{A ∋ i, |A| = m}`.
-/

public section

open Finset Real

namespace CycleCutoff

/-- For `z ≥ 1/2`, `log z ≥ (z - 1) - 2 (z - 1)²`. -/
private lemma sub_one_sub_two_mul_sq_le_log {z : ℝ} (hz : 1 / 2 ≤ z) :
    (z - 1) - 2 * (z - 1) ^ 2 ≤ log z := by
  have hz0 : 0 < z := by linarith
  refine le_trans ?_ (one_sub_inv_le_log_of_pos hz0)
  rw [show 1 - z⁻¹ = (z - 1) / z by field_simp, le_div_iff₀ hz0]
  nlinarith [sq_nonneg (z - 1)]

/-- The sample form of the bound: if `|V| = N ≥ 2`, `w : V → [1/2, 3/2]`, `w₀ ∈ [1/2, 3/2]` and
`∑_V w = N + 1 - w₀`, then for a uniformly random `k`-subset `T` of `V`,
`𝔼 log ((k + 1)⁻¹ (w₀ + ∑_{y ∈ T} w y)) ≥ -3/(k + 1)`. -/
private lemma neg_three_div_le_sampleAvg_log {V : Type*} [Fintype V] (hN : 2 ≤ Fintype.card V)
    {k : ℕ} (hk : k ≤ Fintype.card V) (w : V → ℝ) (hw : ∀ y, 1 / 2 ≤ w y ∧ w y ≤ 3 / 2)
    {w₀ : ℝ} (hw₀ : 1 / 2 ≤ w₀ ∧ w₀ ≤ 3 / 2) (hsum : ∑ y, w y = Fintype.card V + 1 - w₀) :
    -3 / ((k : ℝ) + 1) ≤
      sampleAvg k (fun T => log (((k : ℝ) + 1)⁻¹ * (w₀ + ∑ y ∈ T, w y))) := by
  classical
  set N := Fintype.card V with hNdef
  set m : ℝ := (k : ℝ) + 1 with hm
  have hm1 : 1 ≤ m := by simp [hm]
  have hm0 : 0 < m := by linarith
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk
  set S : Finset V → ℝ := fun T => ∑ y ∈ T, w y with hS
  set μ := sampleAvg k S with hμdef
  have hμ : μ = k / N * (N + 1 - w₀) := by
    rw [hμdef, hS, sampleAvg_sum k hk, hsum]
  set Var := sampleAvg k (fun T => (S T - μ) ^ 2) with hVardef
  have hVar : Var ≤ k := by
    rw [hVardef, hμdef, hS, sampleAvg_sq_sub hN k hk, ← hNdef]
    set wbar := (N : ℝ)⁻¹ * ∑ y', w y' with hwbar
    have hwbar1 : 1 / 2 ≤ wbar ∧ wbar ≤ 3 / 2 := by
      have h1 : (N : ℝ) * (1 / 2) ≤ ∑ y', w y' := by
        simpa [hNdef] using card_nsmul_le_sum (univ : Finset V) w (1 / 2) fun y _ => (hw y).1
      have h2 : ∑ y', w y' ≤ (N : ℝ) * (3 / 2) := by
        simpa [hNdef] using sum_le_card_nsmul (univ : Finset V) w (3 / 2) fun y _ => (hw y).2
      rw [hwbar]
      exact ⟨by rw [le_inv_mul_iff₀ hN0]; linarith, by rw [inv_mul_le_iff₀ hN0]; linarith⟩
    have hsq : ∑ y, (w y - wbar) ^ 2 ≤ N := by
      have := sum_le_card_nsmul (univ : Finset V) (fun y => (w y - wbar) ^ 2) 1
        fun y _ => by
          have := hw y
          nlinarith
      simpa [hNdef] using this
    have hcoef : 0 ≤ (k * (N - k) : ℝ) / (N * (N - 1)) := by
      apply div_nonneg <;> nlinarith
    calc (k * (N - k) : ℝ) / (N * (N - 1)) * ∑ y, (w y - wbar) ^ 2
        ≤ (k * (N - k) : ℝ) / (N * (N - 1)) * N := mul_le_mul_of_nonneg_left hsq hcoef
      _ ≤ k := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by nlinarith)]
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · simp [h0]
        · have : (1 : ℝ) ≤ k := by exact_mod_cast h0
          nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg N))
            (sub_nonneg.2 this)]
  set e := (w₀ + μ) / m - 1 with he
  have hem : e * m * N = (w₀ - 1) * (N - k) := by
    rw [he, hμ, hm]
    field_simp
    ring
  have hpt : ∀ T ∈ (univ : Finset V).powersetCard k,
      (e - 2 * e ^ 2 - (1 - 4 * e) / m * μ) + (1 - 4 * e) / m * S T +
          (-2 / m ^ 2) * (S T - μ) ^ 2 ≤ log (m⁻¹ * (w₀ + ∑ y ∈ T, w y)) := by
    intro T hT
    have hcard := (mem_powersetCard.1 hT).2
    have hST : (k : ℝ) * (1 / 2) ≤ S T := by
      simpa [hS, hcard] using card_nsmul_le_sum T w (1 / 2) fun y _ => (hw y).1
    have hZ : 1 / 2 ≤ m⁻¹ * (w₀ + ∑ y ∈ T, w y) := by
      rw [le_inv_mul_iff₀ hm0]
      simp only [hS] at hST
      rw [hm]; linarith [hw₀.1]
    refine le_trans (le_of_eq ?_) (sub_one_sub_two_mul_sq_le_log hZ)
    simp only [hS, he]
    field_simp
    ring
  refine le_trans ?_ (sampleAvg_mono hpt)
  rw [sampleAvg_affine hk, ← hμdef, ← hVardef]
  have hf1 : -1 / 2 ≤ e * m := by
    by_contra h
    push Not at h
    nlinarith [mul_lt_mul_of_pos_right h hN0]
  have hf2 : e * m ≤ 1 / 2 := by
    by_contra h
    push Not at h
    nlinarith [mul_lt_mul_of_pos_right h hN0]
  have hrw : e - 2 * e ^ 2 - (1 - 4 * e) / m * μ + (1 - 4 * e) / m * μ + -2 / m ^ 2 * Var
      = ((e * m) * m - 2 * (e * m) ^ 2 - 2 * Var) / m ^ 2 := by
    field_simp
    ring
  have hfm : -m / 2 ≤ (e * m) * m := by nlinarith
  have hf2' : (e * m) ^ 2 ≤ 1 / 4 := by nlinarith
  have key : -3 * m ≤ (e * m) * m - 2 * (e * m) ^ 2 - 2 * Var := by linarith
  rw [hrw, div_le_div_iff₀ hm0 (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right key hm0.le]

/-- **The mean logarithm of an exposed row sum**: for `n ≥ 3`, `1 ≤ m ≤ n` and
`W : ℤ/n × ℤ/n → [1/2, 3/2]` with all row sums `n`, the average over the `m`-sets `A ∋ i` of
`log (m⁻¹ ∑_{x ∈ σ(A)} W(i, x))` is at least `-3/m`. -/
@[cycle_cutoff "lem_log_Z_bound"]
theorem neg_three_div_le_sum_log_exposure {n : ℕ} [NeZero n] (hn : 3 ≤ n) {m : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) (W : ZMod n → ZMod n → ℝ)
    (hW : ∀ i x, 1 / 2 ≤ W i x ∧ W i x ≤ 3 / 2) (hrow : ∀ i, ∑ x, W i x = n)
    (i : ZMod n) (σ : Equiv.Perm (ZMod n)) :
    -(3 : ℝ) / m ≤ (((n - 1).choose (m - 1) : ℕ) : ℝ)⁻¹ *
      ∑ A : Finset (ZMod n) with i ∈ A ∧ A.card = m,
        Real.log ((m : ℝ)⁻¹ * ∑ x ∈ A.image σ, W i x) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  set x₀ := σ i with hx₀
  have hV : Fintype.card {y : ZMod n // y ≠ x₀} = n - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ZMod.card]
  have hsum : ∑ y : {y : ZMod n // y ≠ x₀}, W i y =
      (Fintype.card {y : ZMod n // y ≠ x₀} : ℝ) + 1 - W i x₀ := by
    rw [← sum_subtype (univ.erase x₀) (fun y => by simp) (W i), hV,
      Nat.cast_sub (by omega : 1 ≤ n), ← hrow i, ← add_sum_erase univ (W i) (mem_univ x₀)]
    push_cast
    ring
  have hmain := neg_three_div_le_sampleAvg_log (V := {y : ZMod n // y ≠ x₀}) (by rw [hV]; omega)
    (k := k) (by rw [hV]; omega) (fun y => W i y) (fun y => hW i y) (hW i x₀) hsum
  push_cast
  refine hmain.trans_eq ?_
  unfold sampleAvg
  rw [hV, div_eq_inv_mul]
  congr 1
  symm
  apply sum_nbij' (fun A => (A.image σ).subtype (· ≠ x₀))
    (fun T => insert i ((T.map (Function.Embedding.subtype _)).image σ.symm))
  · intro A hA
    rw [mem_filter] at hA
    rw [mem_powersetCard]
    refine ⟨subset_univ _, ?_⟩
    rw [card_subtype, filter_ne', card_erase_of_mem (by simp [hx₀, hA.2.1]),
      card_image_of_injective _ σ.injective, hA.2.2, Nat.add_sub_cancel]
  · intro T hT
    rw [mem_powersetCard] at hT
    rw [mem_filter]
    refine ⟨mem_univ _, mem_insert_self _ _, ?_⟩
    rw [card_insert_of_notMem, card_image_of_injective _ σ.symm.injective, card_map, hT.2]
    simp only [mem_image, mem_map, Function.Embedding.coe_subtype, not_exists, not_and]
    rintro x ⟨y, -, rfl⟩ hx
    exact y.2 (hx₀.trans (σ.symm_apply_eq.1 hx).symm).symm
  · intro A hA
    rw [mem_filter] at hA
    ext a
    simp only [mem_insert, mem_image, mem_map, mem_subtype, Function.Embedding.coe_subtype]
    constructor
    · rintro (rfl | ⟨_, ⟨⟨y, hy⟩, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩)
      · exact hA.2.1
      · simpa using hb
    · intro ha
      by_cases hai : a = i
      · exact Or.inl hai
      · refine Or.inr ⟨σ a, ⟨⟨σ a, fun h => hai (σ.injective (h.trans hx₀))⟩, ⟨a, ha, rfl⟩, rfl⟩,
          by simp⟩
  · intro T hT
    ext y
    simp only [mem_subtype, mem_image, mem_insert, mem_map, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨a, (rfl | ⟨b, ⟨c, hc, rfl⟩, rfl⟩), hy⟩
      · exact absurd (hy.symm.trans hx₀.symm) y.2
      · rwa [show y = c from Subtype.ext (by simpa using hy.symm)]
    · intro hy
      exact ⟨σ.symm y, Or.inr ⟨y, ⟨y, hy, rfl⟩, rfl⟩, by simp⟩
  · intro A hA
    rw [mem_filter] at hA
    congr 2
    rw [sum_subtype_eq_sum_filter, filter_ne', add_sum_erase _ _ (by simp [hx₀, hA.2.1])]

end CycleCutoff
