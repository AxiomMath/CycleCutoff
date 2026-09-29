/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.FiniteProbability.SampleSumMean
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Fintype

/-!
# Size-biasing the intersection of a uniformly random subset with a fixed set

Let `V` be a finite set with `|V| = n`, let `B ⊆ V` and `b₀ ∈ B`, and let `1 ≤ m ≤ n`. If `R` is
a uniformly random `m`-subset of `V` and `R'` a uniformly random `(m - 1)`-subset of
`V ∖ {b₀}`, then for every `g : ℤ → ℝ`,
`𝔼[|R ∩ B| g(|R ∩ B|)] = (|B| m / n) 𝔼[g(1 + |R' ∩ (B ∖ {b₀})|)]`.

Writing `|R ∩ B| = ∑_{b ∈ B} 1[b ∈ R]`, the left side is a sum over `b ∈ B` of the sums of
`g(|R ∩ B|)` over the `m`-subsets `R ∋ b`. The transposition of `b` and `b₀` preserves `B`,
so each of these sums equals the one for `b = b₀`, and `R ↦ R ∖ {b₀}` is a bijection from the
`m`-subsets containing `b₀` onto the `(m - 1)`-subsets of `V ∖ {b₀}`, under which
`|R ∩ B| = 1 + |(R ∖ {b₀}) ∩ (B ∖ {b₀})|`. The normalisation is
`n · C(n - 1, m - 1) = m · C(n, m)`.

## Main results

* `CycleCutoff.sampleAvg_card_inter_mul`: the size-bias identity above.

## Implementation notes

The set `V ∖ {b₀}` is the subtype `{v : V // v ≠ b₀}`, a finite type in its own right, and
`B ∖ {b₀}` is `B.subtype (· ≠ b₀)`.
-/

public section

open Finset

namespace CycleCutoff

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The sum of `g #(R ∩ B)` over the `m`-subsets `R` of `V` containing a point `b` does not
depend on which point `b ∈ B` is chosen: the transposition of `b` and `b₀` preserves `B`. -/
private theorem sum_powersetCard_filter_mem_eq (B : Finset V) (m : ℕ) (g : ℤ → ℝ) {b b₀ : V}
    (hb : b ∈ B) (hb₀ : b₀ ∈ B) :
    ∑ R ∈ ((univ : Finset V).powersetCard m).filter (b ∈ ·), g #(R ∩ B) =
      ∑ R ∈ ((univ : Finset V).powersetCard m).filter (b₀ ∈ ·), g #(R ∩ B) := by
  set σ := Equiv.swap b b₀
  have hσB : B.map σ.toEmbedding = B := by
    ext x
    simp only [mem_map_equiv, σ, Equiv.symm_swap, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  refine sum_equiv σ.finsetCongr (fun R => ?_) (fun R _ => ?_)
  · simp [σ]
  · rw [Equiv.finsetCongr_apply]
    congr 2
    conv_rhs => rw [← hσB, ← map_inter, card_map]

/-- Deleting `b₀` is a bijection from the `m`-subsets of `V` containing `b₀` onto the
`(m - 1)`-subsets of `V ∖ {b₀}`, under which `#(R ∩ B) = 1 + #(R' ∩ (B ∖ {b₀}))`. -/
private theorem sum_powersetCard_filter_mem_eq_sum_powersetCard_subtype (B : Finset V) (m : ℕ)
    (hm₁ : 1 ≤ m) {b₀ : V} (hb₀ : b₀ ∈ B) (g : ℤ → ℝ) :
    ∑ R ∈ ((univ : Finset V).powersetCard m).filter (b₀ ∈ ·), g #(R ∩ B) =
      ∑ R' ∈ (univ : Finset {v : V // v ≠ b₀}).powersetCard (m - 1),
        g (1 + #(R' ∩ B.subtype (· ≠ b₀))) := by
  symm
  refine sum_nbij' (fun R' => insert b₀ (R'.map (Function.Embedding.subtype _)))
    (fun R => R.subtype (· ≠ b₀)) (fun R' hR' => ?_) (fun R hR => ?_) (fun R' _ => ?_)
    (fun R hR => ?_) (fun R' _ => ?_)
  · rw [mem_powersetCard_univ] at hR'
    simp only [mem_filter, mem_powersetCard_univ, mem_insert, true_or, and_true]
    rw [card_insert_of_notMem (by simp), card_map, hR']
    omega
  · simp only [mem_filter, mem_powersetCard_univ] at hR
    rw [mem_powersetCard_univ, card_subtype, filter_ne', card_erase_of_mem hR.2, hR.1]
  · ext x
    simp [x.2]
  · simp only [mem_filter] at hR
    rw [subtype_map, filter_ne', insert_erase hR.2]
  · rw [insert_inter_of_mem hb₀, card_insert_of_notMem (by simp)]
    have : (R' ∩ B.subtype (· ≠ b₀)).map (Function.Embedding.subtype _) =
        R'.map (Function.Embedding.subtype _) ∩ B := by
      ext x
      aesop
    rw [← this, card_map, add_comm 1, Nat.cast_add, Nat.cast_one]

/-- Summing `|R ∩ B| g(|R ∩ B|)` over the `m`-subsets `R` gives `|B|` times the sum of
`g(1 + |R' ∩ (B ∖ {b₀})|)` over the `(m - 1)`-subsets `R'` of `V ∖ {b₀}`. -/
theorem sum_powersetCard_card_inter_mul (B : Finset V) (m : ℕ) (hm₁ : 1 ≤ m) (b₀ : V)
    (hb₀ : b₀ ∈ B) (g : ℤ → ℝ) :
    ∑ R ∈ (univ : Finset V).powersetCard m, (#(R ∩ B) : ℝ) * g #(R ∩ B) =
      #B * ∑ R' ∈ (univ : Finset {v : V // v ≠ b₀}).powersetCard (m - 1),
        g (1 + #(R' ∩ B.subtype (· ≠ b₀))) := by
  set S := (univ : Finset V).powersetCard m
  calc ∑ R ∈ S, (#(R ∩ B) : ℝ) * g #(R ∩ B)
      = ∑ R ∈ S, ∑ b ∈ B, if b ∈ R then g #(R ∩ B) else 0 :=
        sum_congr rfl fun R _ => by
          rw [← sum_filter, sum_const, nsmul_eq_mul, filter_mem_eq_inter, inter_comm]
    _ = ∑ b ∈ B, ∑ R ∈ S.filter (b ∈ ·), g #(R ∩ B) := by
        rw [sum_comm]
        exact sum_congr rfl fun b _ => (sum_filter _ _).symm
    _ = ∑ _b ∈ B, ∑ R ∈ S.filter (b₀ ∈ ·), g #(R ∩ B) :=
        sum_congr rfl fun b hb => sum_powersetCard_filter_mem_eq B m g hb hb₀
    _ = _ := by
        rw [sum_const, nsmul_eq_mul,
          sum_powersetCard_filter_mem_eq_sum_powersetCard_subtype B m hm₁ hb₀ g]

/-- **Size-biasing the intersection with a fixed set.** For a uniformly random `m`-subset `R`
of `V` and a uniformly random `(m - 1)`-subset `R'` of `V ∖ {b₀}`, where `b₀ ∈ B`,
`𝔼[|R ∩ B| g(|R ∩ B|)] = (|B| m / |V|) 𝔼[g(1 + |R' ∩ (B ∖ {b₀})|)]`. -/
@[cycle_cutoff "lem_size_bias"]
theorem sampleAvg_card_inter_mul (B : Finset V) (m : ℕ) (hm₁ : 1 ≤ m)
    (hm : m ≤ Fintype.card V) (b₀ : V) (hb₀ : b₀ ∈ B) (g : ℤ → ℝ) :
    sampleAvg m (fun R : Finset V => (#(R ∩ B) : ℝ) * g #(R ∩ B)) =
      (#B * m : ℝ) / Fintype.card V *
        sampleAvg (V := {v : V // v ≠ b₀}) (m - 1)
          (fun R' => g (1 + #(R' ∩ B.subtype (· ≠ b₀)))) := by
  unfold sampleAvg
  rw [sum_powersetCard_card_inter_mul B m hm₁ b₀ hb₀ g,
    show Fintype.card {v : V // v ≠ b₀} = Fintype.card V - 1 by
      simp [Fintype.card_subtype, filter_ne', card_erase_of_mem]]
  set N := Fintype.card V
  have hN : 0 < N := hm₁.trans hm
  have hid : (N : ℝ) * ((N - 1).choose (m - 1) : ℝ) = (m : ℝ) * (N.choose m : ℝ) := by
    obtain ⟨n, hn⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [hn]
    simp only [Nat.add_sub_cancel]
    exact_mod_cast (Nat.add_one_mul_choose_eq n j).trans (mul_comm _ _)
  have hC : (N.choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hm).ne'
  have hC' : ((N - 1).choose (m - 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  linear_combination (#B : ℝ) *
    (∑ R' ∈ (univ : Finset {v : V // v ≠ b₀}).powersetCard (m - 1),
      g (1 + #(R' ∩ B.subtype (· ≠ b₀)))) * hid

end CycleCutoff
