/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.Defs
public import CycleCutoff.BernoulliLaplace.Defs
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Fin
public import Mathlib.GroupTheory.Perm.Basic

/-!
# The adjacent transposition shuffle on a path

Cards and positions are elements of `Fin N` (0-indexed), and a permutation
`σ : Equiv.Perm (Fin N)` sends card `a` to its position `σ a`. The path shuffle applies
`τ_j = (j  j+1)`, `j < N - 1`, on the left, exchanging the cards at positions `j` and `j + 1`.

## Main definitions

* `CycleCutoff.adjSwap`: the adjacent transposition `(j  j+1)` of `Fin N`, for `j : Fin (N - 1)`.
* `CycleCutoff.pathShuffle`: the involution family `(σ ↦ τ_j ∘ σ)_j` on `𝔖_N`.
* `CycleCutoff.bisectionSet`: the set `S_k(σ) = {a : σ(a) < k}` of cards in the first `k`
  positions.
* `CycleCutoff.bisectionSlice`: `S_k(σ)` as a point of the slice `Ω_{[N],k}`, for `k ≤ N`.
* `CycleCutoff.ColoredConfig`: the maps `c : Fin s → 𝒜` (the colour at each position) with
  `|c⁻¹(a)| = k a` for every colour `a`.
* `CycleCutoff.coloredProcess`: the coloured path process `(c ↦ c ∘ τ_j)_j`, which exchanges
  the colours at positions `j` and `j + 1`.
-/

@[expose] public section

open Finset

namespace CycleCutoff

/-- The adjacent transposition `τ^{(N)}_{j+1} = (j  j+1)` of `Fin N`, for `j : Fin (N - 1)`
(0-indexed). -/
@[cycle_cutoff "def_path_shuffle"]
def adjSwap (N : ℕ) (j : Fin (N - 1)) : Equiv.Perm (Fin N) :=
  Equiv.swap ⟨j, by omega⟩ ⟨j + 1, by omega⟩

/-- An adjacent transposition is an involution: `τ_j τ_j = 1`. -/
@[simp] theorem adjSwap_mul_self (N : ℕ) (j : Fin (N - 1)) : adjSwap N j * adjSwap N j = 1 :=
  Equiv.swap_mul_self _ _

/-- An adjacent transposition is an involution: `τ_j (τ_j i) = i`. -/
@[simp] theorem adjSwap_adjSwap (N : ℕ) (j : Fin (N - 1)) (i : Fin N) :
    adjSwap N j (adjSwap N j i) = i :=
  Equiv.swap_apply_self _ _ _

/-- The path shuffle `𝒯^path_N = (σ ↦ τ_j ∘ σ)_{j}` on `𝔖_N`. -/
@[cycle_cutoff "def_path_shuffle"]
def pathShuffle (N : ℕ) : InvFamily (Fin (N - 1)) (Equiv.Perm (Fin N)) where
  T j σ := adjSwap N j * σ
  involutive j σ := by simp [adjSwap, Equiv.swap_mul_self_mul]

/-- The move of the path shuffle at `j` is left multiplication by `τ_j`. -/
@[simp] theorem pathShuffle_T (N : ℕ) (j : Fin (N - 1)) (σ : Equiv.Perm (Fin N)) :
    (pathShuffle N).T j σ = adjSwap N j * σ := rfl

/-- The bisection set `S_k(σ) = {a : σ(a) < k}` (0-indexed), the cards in the first `k`
positions. -/
@[cycle_cutoff "def_bisection_set"]
def bisectionSet (N k : ℕ) (σ : Equiv.Perm (Fin N)) : Finset (Fin N) :=
  {a | (σ a : ℕ) < k}

/-- A card lies in `S_k(σ)` iff its position `σ a` is less than `k`. -/
@[simp] theorem mem_bisectionSet {N k : ℕ} {σ : Equiv.Perm (Fin N)} {a : Fin N} :
    a ∈ bisectionSet N k σ ↔ (σ a : ℕ) < k := by
  simp [bisectionSet]

/-- `|S_k(σ)| = k` for `k ≤ N`. -/
theorem card_bisectionSet {N k : ℕ} (hk : k ≤ N) (σ : Equiv.Perm (Fin N)) :
    (bisectionSet N k σ).card = k := by
  have : bisectionSet N k σ = ({i : Fin N | (i : ℕ) < k} : Finset (Fin N)).map
      σ.symm.toEmbedding := by
    ext a
    simp only [mem_bisectionSet, mem_map, mem_filter, mem_univ, true_and,
      Equiv.coe_toEmbedding]
    exact ⟨fun h => ⟨σ a, h, by simp⟩, fun ⟨i, hi, hia⟩ => by simpa [← hia] using hi⟩
  rw [this, card_map, Fin.card_filter_val_lt, min_eq_right hk]

/-- `S_k(σ)` is a subset of `[N]` of size `min k N`. -/
theorem bisectionSet_mem_powersetCard (N k : ℕ) (σ : Equiv.Perm (Fin N)) :
    bisectionSet N k σ ∈ (univ : Finset (Fin N)).powersetCard (min k N) := by
  rcases le_total k N with hk | hk
  · rw [min_eq_left hk]
    exact mem_powersetCard.2 ⟨subset_univ _, card_bisectionSet hk σ⟩
  · rw [min_eq_right hk]
    refine mem_powersetCard.2 ⟨subset_univ _, ?_⟩
    have : bisectionSet N k σ = univ := by
      ext a; simp only [mem_bisectionSet, mem_univ, iff_true]; omega
    simp [this]

/-- The bisection set as a point of the slice `Ω_{[N],k}` (for `k ≤ N`). -/
def bisectionSlice (N k : ℕ) (hk : k ≤ N) (σ : Equiv.Perm (Fin N)) :
    blSlice (univ : Finset (Fin N)) k :=
  ⟨bisectionSet N k σ, mem_powersetCard.2 ⟨subset_univ _, card_bisectionSet hk σ⟩⟩

/-- The underlying set of `bisectionSlice N k hk σ` is `S_k(σ)`. -/
@[simp] theorem coe_bisectionSlice (N k : ℕ) (hk : k ≤ N) (σ : Equiv.Perm (Fin N)) :
    ((bisectionSlice N k hk σ : blSlice (univ : Finset (Fin N)) k) : Finset (Fin N)) =
      bisectionSet N k σ := rfl

/-- The maps `bisectionSlice N k hk` and `bisectionSet N k` have the same fibres. -/
theorem fiber_bisectionSlice (N k : ℕ) (hk : k ≤ N) (σ : Equiv.Perm (Fin N)) :
    fiber (bisectionSlice N k hk) σ = fiber (bisectionSet N k) σ := by
  ext τ
  simp only [mem_fiber, Subtype.ext_iff, coe_bisectionSlice]

/-! ### The coloured path process -/

section Colored

variable {𝒜 : Type*} [DecidableEq 𝒜]

/-- The state space `Ω_{s,k} = {c : [s] → 𝒜 : |c⁻¹(a)| = k_a ∀ a}` of the coloured path
process; `c i` is the colour at position `i`. -/
@[cycle_cutoff "def_colored_process"]
abbrev ColoredConfig (s : ℕ) (k : 𝒜 → ℕ) : Type _ :=
  {c : Fin s → 𝒜 // ∀ a, (univ.filter fun i => c i = a).card = k a}

/-- Precomposing with a permutation of the positions preserves the number of positions of each
colour. -/
theorem card_filter_comp_equiv {s : ℕ} (c : Fin s → 𝒜) (e : Equiv.Perm (Fin s)) (a : 𝒜) :
    (univ.filter fun i => c (e i) = a).card = (univ.filter fun i => c i = a).card := by
  have : (univ.filter fun i => c (e i) = a) =
      (univ.filter fun i => c i = a).map e.symm.toEmbedding := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_map, Equiv.coe_toEmbedding]
    exact ⟨fun h => ⟨e i, h, by simp⟩, fun ⟨x, hx, hxi⟩ => by simpa [← hxi] using hx⟩
  rw [this, card_map]

/-- The coloured path process `𝒯^col_{s,k} = (c ↦ c ∘ τ_j)_j` on `Ω_{s,k}`: `T j` exchanges
the colours at positions `j` and `j + 1`. -/
@[cycle_cutoff "def_colored_process"]
def coloredProcess (s : ℕ) (k : 𝒜 → ℕ) : InvFamily (Fin (s - 1)) (ColoredConfig s k) where
  T j c := ⟨c.1 ∘ adjSwap s j, fun a => by
    rw [← c.2 a]
    exact card_filter_comp_equiv c.1 (adjSwap s j) a⟩
  involutive j c := by
    apply Subtype.ext
    funext i
    simp

/-- The move of the coloured path process at `j` precomposes the colouring with `τ_j`. -/
@[simp] theorem coloredProcess_T_val (s : ℕ) (k : 𝒜 → ℕ) (j : Fin (s - 1))
    (c : ColoredConfig s k) : ((coloredProcess s k).T j c).1 = c.1 ∘ adjSwap s j := rfl

end Colored

end CycleCutoff
