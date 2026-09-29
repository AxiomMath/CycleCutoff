/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.Defs
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# The adjacent transposition shuffle on the cycle

Positions and cards are elements of `ZMod n` (with `[NeZero n]`, so that `ZMod n` is a
`Fintype`), and a permutation `σ : Equiv.Perm (ZMod n)` sends card `i` to its position `σ i`.
The shuffle applies `τ_x = Equiv.swap x (x + 1)` on the left at rate one for each `x`; its
semigroup `(cycleShuffle n).semigroup t` is `P_t`, and the uniform law on permutations is
`π_n = unif (Equiv.Perm (ZMod n))`. The shuffle `CycleCutoff.cycleShuffle`, the distance
`CycleCutoff.dn`, the mixing time `CycleCutoff.tmix`, the spectral gap `CycleCutoff.lambdaN` and
the cutoff location `CycleCutoff.tn` are defined in `CycleCutoff.Definitions`.

## Main definitions

* `CycleCutoff.muT`: the law `μ_t(σ) = P_t(id, σ)` of the shuffle started from the identity.
-/

@[expose] public section

open Finset

namespace CycleCutoff

section Shuffle

variable (n : ℕ)

/-- The move of the cycle shuffle at `x` is left multiplication by `τ_x = (x  x+1)`. -/
@[simp] theorem cycleShuffle_T (x : ZMod n) (σ : Equiv.Perm (ZMod n)) :
    (cycleShuffle n).T x σ = Equiv.swap x (x + 1) * σ := rfl

variable [NeZero n]

/-- The law of the shuffle started from the identity, `μ_t(σ) = P_t(id, σ)`. -/
@[cycle_cutoff "def_mu_t"]
noncomputable def muT (t : ℝ) (σ : Equiv.Perm (ZMod n)) : ℝ :=
  (cycleShuffle n).semigroup t 1 σ

/-- The law `μ_t` is the row of the identity in the semigroup `P_t`. -/
theorem muT_def (t : ℝ) (σ : Equiv.Perm (ZMod n)) :
    muT n t σ = (cycleShuffle n).semigroup t 1 σ := rfl

end Shuffle

end CycleCutoff
