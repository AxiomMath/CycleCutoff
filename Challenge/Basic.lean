/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! # The formal challenge file, written by humans

This is a human-written file certifying the formal statements that this repository proves.

-/

@[expose] public section

open Finset

namespace CycleCutoff

/-! ## Finite probability -/

section FiniteProbability

variable {Ω Y : Type*} [Fintype Ω]

variable (Ω) in
/-- The uniform probability vector `u_Ω(z) = 1 / |Ω|`. -/
noncomputable def unif : Ω → ℝ :=
  fun _ => (Fintype.card Ω : ℝ)⁻¹

/-- Total variation distance `‖α - β‖_TV = ½ ∑_z |α(z) - β(z)|`. -/
noncomputable def tvDist (α β : Ω → ℝ) : ℝ :=
  (1 / 2) * ∑ z, |α z - β z|

end FiniteProbability

/-! ## Involution families and their semigroups -/

/-- A finite family of involutions `(T_e)_{e ∈ ι}` of `Ω`. -/
structure InvFamily (ι Ω : Type*) where
  /-- The map indexed by `e`. -/
  T : ι → Ω → Ω
  /-- Each map is an involution. -/
  involutive : ∀ e, Function.Involutive (T e)

namespace InvFamily

variable {ι Ω : Type*} (𝒯 : InvFamily ι Ω)

variable [Fintype ι]

/-- The rate matrix `Q_𝒯(z, w) = ∑_e (1[T_e z = w] - 1[z = w])` of an involution family: the
generator of the continuous-time chain that applies each `T_e` at rate one. -/
noncomputable def rateMatrix [DecidableEq Ω] : Matrix Ω Ω ℝ :=
  fun z w => ∑ e, ((if 𝒯.T e z = w then 1 else 0) - (if z = w then 1 else 0))

end InvFamily

section Semigroup

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The semigroup `P^Q_t = exp(t Q)` of a real square matrix `Q` (matrix exponential). -/
noncomputable def semigroup (Q : Matrix Ω Ω ℝ) (t : ℝ) : Matrix Ω Ω ℝ :=
  NormedSpace.exp (t • Q)

/-- The semigroup `P^𝒯_t = P^{Q_𝒯}_t` of an involution family; its row `z` is the law at time
`t` of the chain started from `z`. -/
noncomputable def InvFamily.semigroup {ι : Type*} [Fintype ι] (𝒯 : InvFamily ι Ω) (t : ℝ) :
    Matrix Ω Ω ℝ :=
  CycleCutoff.semigroup 𝒯.rateMatrix t

end Semigroup

/-! ## The adjacent transposition shuffle on the cycle -/

section Shuffle

variable (n : ℕ)

/-- The adjacent transposition shuffle on the cycle, `𝒯_n = (σ ↦ τ_x ∘ σ)_{x ∈ ℤ/nℤ}` with
`τ_x = (x  x+1)`: a permutation `σ` sends card `i` to position `σ i`, and each adjacent pair of
positions, including `n - 1, 0`, is swapped at rate one. -/
def cycleShuffle : InvFamily (ZMod n) (Equiv.Perm (ZMod n)) where
  T x σ := Equiv.swap x (x + 1) * σ
  involutive _ σ := Equiv.swap_mul_self_mul _ _ σ

variable [NeZero n]

/-- The worst-case distance `d_n(t) = max_σ ‖P_t(σ, ·) - π_n‖_TV`, where `π_n` is the uniform
law on permutations. -/
noncomputable def dn (t : ℝ) : ℝ :=
  ⨆ σ : Equiv.Perm (ZMod n),
    tvDist (fun σ' => (cycleShuffle n).semigroup t σ σ') (unif (Equiv.Perm (ZMod n)))

/-- The mixing time `t_mix^{(n)}(ε) = inf {t ≥ 0 : d_n(t) ≤ ε}`, an infimum in `ℝ`. -/
noncomputable def tmix (ε : ℝ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ dn n t ≤ ε}

end Shuffle

/-- The spectral gap of the one-card walk, `λ_n = 2 - 2 cos(2π/n)`. -/
noncomputable def lambdaN (n : ℕ) : ℝ :=
  2 - 2 * Real.cos (2 * Real.pi / n)

/-- The cutoff location `t_n = log n / (2 λ_n)`, asymptotic to `n² log n / (8π²)`. -/
noncomputable def tn (n : ℕ) : ℝ :=
  Real.log n / (2 * lambdaN n)

end CycleCutoff

namespace CycleCutoff.Challenge

/-! ## The objective -/

/-- **`thm_main` — cutoff for the adjacent transposition shuffle on the cycle.** There is an
absolute constant `C > 0` such that for every `ε ∈ (0, 1)` there is `C_ε > 0` with
`t_n - C_ε n² ≤ t_mix^{(n)}(ε) ≤ t_n + C n² log log n + C_ε n²` for all sufficiently large `n`,
rendered as `n ≥ N₀`. The binder `[NeZero n]` only makes `ZMod n` finite. -/
theorem thm_main :
    ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ Cε > (0 : ℝ), ∃ N₀ : ℕ,
      ∀ (n : ℕ) [NeZero n], N₀ ≤ n →
        tn n - Cε * (n : ℝ) ^ 2 ≤ tmix n ε ∧
        tmix n ε ≤ tn n + C * (n : ℝ) ^ 2 * Real.log (Real.log n) + Cε * (n : ℝ) ^ 2 :=
  sorry

end CycleCutoff.Challenge
