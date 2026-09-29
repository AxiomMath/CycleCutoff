/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.TwoCopy.Defs
public import CycleCutoff.PathShuffle.Defs

/-!
# The path two-copy process and the shared-transposition chain

The two-copy process and the shared-transposition chain on the path graph with vertex set `Fin s`
(0-indexed).

## Main definitions

* `sharedFamily`: The family `S_e(R, x, y) = (τ_e R, τ_e x, τ_e y)` indexed by edges `e`.
* `pathEdge`: The path edges `(j, j + 1)` of `Fin s`, for `j : Fin (s - 1)`.
* `pathTwoCopy`: The path two-copy process `𝒯^p_{s,k}` on `Ω^p_{s,k} = TwoCopyState (Fin s) k`.
* `sharedChain`: The shared-transposition chain `𝒮_{s,k}` on `Ω^p_{s,k}`.

## Implementation notes

The transposition of the path edge `j` is `edgeSwap (pathEdge s) j = adjSwap s j` (definitionally),
which swaps `j` and `j + 1` and is written `τ^{(s)}_j` below. The stationary measure `ν_{s,k}` is
`unif _` and `𝒟^p_{s,k}` is `(pathTwoCopy s k).dirichletForm`.
-/

@[expose] public section

open Finset

namespace CycleCutoff

section Shared

variable {V ι : Type*} [DecidableEq V] (edge : ι → V × V) (m : ℕ)

/-- The shared-transposition family `S_e(R, x, y) = (τ_e R, τ_e x, τ_e y)`. -/
def sharedFamily : InvFamily ι (TwoCopyState V m) where
  T e w := w.permMap (edgeSwap edge e)
  involutive _ w := w.permMap_swap_swap _ _

/-- `S_e` applies the transposition `τ_e` to all three coordinates. -/
@[simp] theorem sharedFamily_T (e : ι) (w : TwoCopyState V m) :
    (sharedFamily edge m).T e w = w.permMap (edgeSwap edge e) := rfl

end Shared

section Path

variable (s : ℕ)

/-- The path edges `e_j = {j, j + 1}` of `Fin s`, for `j : Fin (s - 1)` (0-indexed). -/
def pathEdge (j : Fin (s - 1)) : Fin s × Fin s :=
  (⟨j, by lia⟩, ⟨j + 1, by lia⟩)

/-- The transposition of the path edge `j` is the adjacent transposition `adjSwap s j`. -/
@[simp] theorem edgeSwap_pathEdge (j : Fin (s - 1)) : edgeSwap (pathEdge s) j = adjSwap s j :=
  rfl

/-- **The path two-copy process.** The family `𝒯^p_{s,k}` on `Ω^p_{s,k} = TwoCopyState (Fin s) k`
consisting, for each path edge `j`, of the maps `T^sh_j`, `T^1_j`, `T^2_j` (with `τ_z` replaced by
`τ^{(s)}_j`). -/
@[cycle_cutoff "def_path_two_copy"]
def pathTwoCopy (k : ℕ) : InvFamily (TwoCopyMove (Fin (s - 1))) (TwoCopyState (Fin s) k) :=
  twoCopyFamily (pathEdge s) k

/-- **The shared-transposition chain.** The chain `𝒮_{s,k} = (S_j)_j`,
`S_j(R, x, y) = (τ^{(s)}_j R, τ^{(s)}_j x, τ^{(s)}_j y)`, on `Ω^p_{s,k}`. -/
@[cycle_cutoff "def_shared_chain"]
def sharedChain (k : ℕ) : InvFamily (Fin (s - 1)) (TwoCopyState (Fin s) k) :=
  sharedFamily (pathEdge s) k

/-- `S_j` applies the adjacent transposition `adjSwap s j` to all three coordinates. -/
@[simp] theorem sharedChain_T (k : ℕ) (j : Fin (s - 1)) (w : TwoCopyState (Fin s) k) :
    (sharedChain s k).T j w = w.permMap (adjSwap s j) := rfl

end Path

end CycleCutoff
