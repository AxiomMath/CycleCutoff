/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.TwoCopy.Defs
public import CycleCutoff.Generator.Lumping

/-!
# Projection of the black-labelled two-copy chain to the two-copy process

Let `|A| = m` and let `Ψ : Ξ_A → Ω_{n,m}` be the projection `Ψ(β, y₁, y₂) = (R(β), y₁, y₂)`.
Then `Ψ` intertwines the maps of the black-labelled two-copy chain `𝒢_A` with those of the
two-copy process `𝒯_{n,m}`: `Ψ ∘ S_z = T^sh_z ∘ Ψ`, `Ψ ∘ X_z = T^1_z ∘ Ψ` and
`Ψ ∘ Y_z = T^2_z ∘ Ψ` for every `z ∈ ℤ/nℤ`. Hence `L_{𝒢_A} (f ∘ Ψ) = (L_{n,m} f) ∘ Ψ`, and
lumping gives, for every `t` and every `(β₀, y⁰₁, y⁰₂) ∈ Ξ_A`, `(R, x, y) ∈ Ω_{n,m}`,
`∑_{β : R(β) = R} P^{𝒢_A}_t((β₀, y⁰₁, y⁰₂), (β, x, y))
  = P^{𝒯_{n,m}}_t((R(β₀), y⁰₁, y⁰₂), (R, x, y))`.

## Main results

* `CycleCutoff.BlackTwoState.proj_blackS`: `Ψ ∘ S_z = T^sh_z ∘ Ψ`.
* `CycleCutoff.BlackTwoState.proj_blackX`: `Ψ ∘ X_z = T^1_z ∘ Ψ`.
* `CycleCutoff.BlackTwoState.proj_blackY`: `Ψ ∘ Y_z = T^2_z ∘ Ψ`.
* `CycleCutoff.BlackTwoState.proj_T`: `Ψ ∘ (𝒢_A)_θ = (𝒯_{n,m})_θ ∘ Ψ` for every move `θ`.
* `CycleCutoff.sum_blackTwoCopy_semigroup_eq_twoCopy`: the lumping identity above.

## Implementation notes

The paper's sum over the configurations `β` with `R(β) = R` of `P_t(w₀, (β, x, y))` is written as
the sum over the states `w = (β, y₁, y₂) ∈ Ξ_A` with `R(β) = R`, `y₁ = x`, `y₂ = y`, which is the
same sum reindexed along `β ↦ (β, x, y)`. The paper's standing assumptions `t ≥ 0` and `n ≥ 3`
are not needed.
-/

public section

open Finset Matrix

namespace CycleCutoff

variable {n : ℕ} {A : Finset (ZMod n)} {m : ℕ}

/-- If the edge `{z, z + 1}` neither lies in `R` nor meets it in exactly one point, it misses
`R`. -/
private theorem not_mem_of_card_inter_ne_one {R : Finset (ZMod n)} {z : ZMod n}
    (h₁ : ¬ ({z, z + 1} : Finset (ZMod n)) ⊆ R) (h₂ : (R ∩ {z, z + 1}).card ≠ 1) :
    z ∉ R ∧ z + 1 ∉ R := by
  by_cases hz : z ∈ R <;> by_cases hz' : z + 1 ∈ R <;>
    simp_all [insert_subset_iff, inter_insert_of_mem, inter_insert_of_notMem]

/-- A transposition of two points outside `R` fixes `R`. -/
private theorem map_swap_eq_self {R : Finset (ZMod n)} {a b : ZMod n} (ha : a ∉ R)
    (hb : b ∉ R) : R.map (Equiv.swap a b).toEmbedding = R := by
  ext v
  rw [mem_map_equiv, Equiv.symm_swap]
  grind

variable [NeZero n]

/-- `Ψ ∘ S_z = T^sh_z ∘ Ψ`. -/
theorem BlackTwoState.proj_blackS (hA : A.card = m) (z : ZMod n) (w : BlackTwoState n A) :
    (blackS z w).proj hA = shMove (cycleEdge n) m z (w.proj hA) := by
  have hR : (w.proj hA).R = blackRed w.1.1 := rfl
  rw [blackS, shMove]
  by_cases hs : ({z, z + 1} : Finset (ZMod n)) ⊆ blackRed w.1.1 <;>
    by_cases hc : ((w.proj hA).R ∩ edgeSet (cycleEdge n) z).card = 1
  · rw [if_pos hs, if_pos hc, TwoCopyState.ext_iff']
    rw [hR, edgeSet_cycleEdge, inter_eq_right.2 hs] at hc
    have hzz : z + 1 = z := by
      by_contra hne
      simp [card_pair (Ne.symm hne)] at hc
    simp [hzz]
  · rw [if_pos hs, if_neg hc]
  · rw [if_neg hs, if_pos hc, TwoCopyState.ext_iff']
    exact ⟨blackRed_trans _ _, rfl, rfl⟩
  · rw [if_neg hs, if_neg hc, TwoCopyState.ext_iff']
    rw [hR, edgeSet_cycleEdge] at hc
    obtain ⟨hz, hz'⟩ := not_mem_of_card_inter_ne_one hs hc
    exact ⟨(blackRed_trans _ _).trans (map_swap_eq_self hz hz'),
      Equiv.swap_apply_of_ne_of_ne (ne_of_mem_of_not_mem w.2.1 hz)
        (ne_of_mem_of_not_mem w.2.1 hz'),
      Equiv.swap_apply_of_ne_of_ne (ne_of_mem_of_not_mem w.2.2 hz)
        (ne_of_mem_of_not_mem w.2.2 hz')⟩

/-- `Ψ ∘ X_z = T^1_z ∘ Ψ`. -/
theorem BlackTwoState.proj_blackX (hA : A.card = m) (z : ZMod n) (w : BlackTwoState n A) :
    (blackX z w).proj hA = oneMove (cycleEdge n) m z (w.proj hA) := by
  rw [blackX, oneMove]
  by_cases hs : ({z, z + 1} : Finset (ZMod n)) ⊆ blackRed w.1.1
  · rw [dif_pos hs, dif_pos (by simpa using hs)]
    rfl
  · rw [dif_neg hs, dif_neg (by simpa using hs)]

/-- `Ψ ∘ Y_z = T^2_z ∘ Ψ`. -/
theorem BlackTwoState.proj_blackY (hA : A.card = m) (z : ZMod n) (w : BlackTwoState n A) :
    (blackY z w).proj hA = twoMove (cycleEdge n) m z (w.proj hA) := by
  rw [blackY, twoMove]
  by_cases hs : ({z, z + 1} : Finset (ZMod n)) ⊆ blackRed w.1.1
  · rw [dif_pos hs, dif_pos (by simpa using hs)]
    rfl
  · rw [dif_neg hs, dif_neg (by simpa using hs)]

/-- The projection `Ψ` intertwines every map of `𝒢_A` with the map of `𝒯_{n,m}` of the same
index. -/
theorem BlackTwoState.proj_T (hA : A.card = m) (θ : TwoCopyMove (ZMod n))
    (w : BlackTwoState n A) :
    ((blackTwoCopy n A).T θ w).proj hA = (twoCopy n m).T θ (w.proj hA) := by
  cases θ with
  | sh z => exact proj_blackS hA z w
  | one z => exact proj_blackX hA z w
  | two z => exact proj_blackY hA z w

/-- **Projection of the black-labelled two-copy chain.** Summing the black-labelled two-copy
semigroup over the states `(β, x, y)` with `R(β) = R` gives the two-copy semigroup:
`∑_{β : R(β) = R} P^{𝒢_A}_t((β₀, y⁰₁, y⁰₂), (β, x, y))
  = P^{𝒯_{n,m}}_t((R(β₀), y⁰₁, y⁰₂), (R, x, y))`. -/
@[cycle_cutoff "lem_black_projection"]
theorem sum_blackTwoCopy_semigroup_eq_twoCopy (n : ℕ) [NeZero n] (A : Finset (ZMod n)) (m : ℕ)
    (hA : A.card = m) (t : ℝ) (w₀ : BlackTwoState n A) (v : TwoCopyState (ZMod n) m) :
    ∑ w : BlackTwoState n A with blackRed w.1.1 = v.R ∧ w.1.2.1 = v.x ∧ w.1.2.2 = v.y,
        (blackTwoCopy n A).semigroup t w₀ w =
      (twoCopy n m).semigroup t (w₀.proj hA) v := by
  refine (sum_congr (filter_congr fun w _ => ?_) fun _ _ => rfl).trans
    (sum_semigroup_fiber _ _ _ (fun f => ?_) t w₀ v)
  · rw [TwoCopyState.ext_iff']
    rfl
  · rw [InvFamily.rateMatrix_mulVec, InvFamily.rateMatrix_mulVec]
    funext w
    simp only [InvFamily.generator, Function.comp_apply, BlackTwoState.proj_T]

end CycleCutoff
