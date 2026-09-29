/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Attr
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# The objects in the statement of the cutoff theorem

The adjacent transposition shuffle on the cycle `ℤ/nℤ`, run in continuous time, and the
quantities in which its cutoff is stated.

## Main definitions

* `CycleCutoff.unif`: the uniform probability vector `u_Ω(z) = 1 / |Ω|`.
* `CycleCutoff.tvDist`: the total variation distance `‖α - β‖_TV = ½ ∑_z |α(z) - β(z)|`.
* `CycleCutoff.InvFamily`: a family of involutions `(T_e)_{e ∈ ι}` of `Ω`.
* `CycleCutoff.InvFamily.rateMatrix`: the rate matrix `Q_𝒯` of an involution family.
* `CycleCutoff.semigroup`: the semigroup `P^Q_t = exp(t Q)` of a real square matrix `Q`.
* `CycleCutoff.InvFamily.semigroup`: the semigroup `P^𝒯_t` of an involution family.
* `CycleCutoff.cycleShuffle`: the involution family `(σ ↦ τ_x ∘ σ)_{x ∈ ℤ/nℤ}`.
* `CycleCutoff.dn`: the worst-case total variation distance `d_n(t)`.
* `CycleCutoff.tmix`: the mixing time `inf {t ≥ 0 : d_n(t) ≤ ε}`.
* `CycleCutoff.lambdaN`: the spectral gap `λ_n = 2 - 2 cos(2π/n)` of the one-card walk.
* `CycleCutoff.tn`: the cutoff location `t_n = log n / (2 λ_n)`.

## Implementation notes

These declarations are, in order and verbatim, the definitions written out in
`Challenge/Basic.lean`.
-/

@[expose] public section

open Finset

namespace CycleCutoff

section FiniteProbability

variable {Ω Y : Type*} [Fintype Ω]

variable (Ω) in
/-- The uniform probability vector `u_Ω(z) = 1 / |Ω|`. -/
@[cycle_cutoff "def_uniform"]
noncomputable def unif : Ω → ℝ :=
  fun _ => (Fintype.card Ω : ℝ)⁻¹

/-- Total variation distance `‖α - β‖_TV = ½ ∑_z |α(z) - β(z)|`. -/
@[cycle_cutoff "def_tv"]
noncomputable def tvDist (α β : Ω → ℝ) : ℝ :=
  (1 / 2) * ∑ z, |α z - β z|

end FiniteProbability

/-- A finite family of involutions `(T_e)_{e ∈ ι}` of `Ω`. -/
structure InvFamily (ι Ω : Type*) where
  /-- The map indexed by `e`. -/
  T : ι → Ω → Ω
  /-- Each map is an involution. -/
  involutive : ∀ e, Function.Involutive (T e)

namespace InvFamily

variable {ι Ω : Type*} (𝒯 : InvFamily ι Ω)

variable [Fintype ι]

/-- The rate matrix `Q_𝒯(z, w) = ∑_e (1[T_e z = w] - 1[z = w])` of an involution family. -/
@[cycle_cutoff "def_inv_generator"]
noncomputable def rateMatrix [DecidableEq Ω] : Matrix Ω Ω ℝ :=
  fun z w => ∑ e, ((if 𝒯.T e z = w then 1 else 0) - (if z = w then 1 else 0))

end InvFamily

section Semigroup

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The semigroup `P^Q_t = exp(t Q)` of a real square matrix `Q` (matrix exponential). -/
@[cycle_cutoff "def_semigroup"]
noncomputable def semigroup (Q : Matrix Ω Ω ℝ) (t : ℝ) : Matrix Ω Ω ℝ :=
  NormedSpace.exp (t • Q)

/-- The semigroup `P^𝒯_t = P^{Q_𝒯}_t` of an involution family. -/
@[cycle_cutoff "def_semigroup"]
noncomputable def InvFamily.semigroup {ι : Type*} [Fintype ι] (𝒯 : InvFamily ι Ω) (t : ℝ) :
    Matrix Ω Ω ℝ :=
  CycleCutoff.semigroup 𝒯.rateMatrix t

end Semigroup

section Shuffle

variable (n : ℕ)

/-- The adjacent transposition shuffle on the cycle, `𝒯_n = (σ ↦ τ_x ∘ σ)_{x ∈ ℤ/nℤ}` with
`τ_x = (x  x+1)`. -/
@[cycle_cutoff "def_cycle_shuffle"]
def cycleShuffle : InvFamily (ZMod n) (Equiv.Perm (ZMod n)) where
  T x σ := Equiv.swap x (x + 1) * σ
  involutive _ σ := Equiv.swap_mul_self_mul _ _ σ

variable [NeZero n]

/-- The worst-case distance `d_n(t) = max_σ ‖P_t(σ, ·) - π_n‖_TV`. -/
@[cycle_cutoff "def_dn"]
noncomputable def dn (t : ℝ) : ℝ :=
  ⨆ σ : Equiv.Perm (ZMod n),
    tvDist (fun σ' => (cycleShuffle n).semigroup t σ σ') (unif (Equiv.Perm (ZMod n)))

/-- The mixing time `t_mix^{(n)}(ε) = inf {t ≥ 0 : d_n(t) ≤ ε}`. -/
@[cycle_cutoff "def_tmix"]
noncomputable def tmix (ε : ℝ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ dn n t ≤ ε}

end Shuffle

/-- The spectral gap of the one-card walk, `λ_n = 2 - 2 cos(2π/n)`. -/
@[cycle_cutoff "def_lambda_n"]
noncomputable def lambdaN (n : ℕ) : ℝ :=
  2 - 2 * Real.cos (2 * Real.pi / n)

/-- The cutoff location `t_n = log n / (2 λ_n)`. -/
@[cycle_cutoff "def_tn"]
noncomputable def tn (n : ℕ) : ℝ :=
  Real.log n / (2 * lambdaN n)

end CycleCutoff
