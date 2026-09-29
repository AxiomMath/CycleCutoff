/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Cycle.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The one-card walk

The one-card generator `Δ` on `ℤ/nℤ`, its heat kernel `p_t = exp(tΔ)`, the eigenvalues
`λ_{n,j}` of `-Δ`, and the collision sums, entropy and integral built from the row
`p_t(0, ·)`.

## Main definitions

* `CycleCutoff.Delta`: the generator `Δ(x, y) = 1[y = x - 1] + 1[y = x + 1] - 2 · 1[y = x]`,
  acting by `(Δ f)(x) = f(x - 1) + f(x + 1) - 2 f(x)` for every `n`.
* `CycleCutoff.oneCardFamily`: the involution family `(y ↦ τ_x(y))_{x ∈ ℤ/nℤ}`,
  `τ_x = (x  x+1)`.
* `CycleCutoff.heatKernel`: the heat kernel `p_t(i, x) = exp(tΔ)(i, x)`.
* `CycleCutoff.lambdaNJ`: the eigenvalues `λ_{n,j} = 2(1 - cos(2πj/n))`.
* `CycleCutoff.a0`: the time scale `a₀ = 5`.
* `CycleCutoff.S2`, `CycleCutoff.S3`: the sums `S_k(t) = ∑_x p_t(0, x)^k` for `k = 2, 3`.
* `CycleCutoff.oneCardEntropy`: the entropy `h(t) = ∑_x p_t(0, x) log(n p_t(0, x))`.
* `CycleCutoff.Bn`: the integral `B_n = ∫_{(0, ∞)} (S₃(t) - S₂(t)/n) dt`.

## Main results

* `CycleCutoff.Delta_mulVec`: `Δ f = (x ↦ f(x - 1) + f(x + 1) - 2 f(x))`.
* `CycleCutoff.lambdaNJ_one`: `λ_{n,1} = λ_n`.
-/

@[expose] public section

open Finset Matrix MeasureTheory

namespace CycleCutoff

section Generator

variable (n : ℕ)

/-- The one-card generator `(Δ f)(x) = f(x - 1) + f(x + 1) - 2 f(x)`, as a matrix on `ℤ/nℤ`:
`Δ(x, y) = 1[y = x - 1] + 1[y = x + 1] - 2 · 1[y = x]`. -/
@[cycle_cutoff "def_Delta"]
def Delta : Matrix (ZMod n) (ZMod n) ℝ :=
  Matrix.of fun x y =>
    (if y = x - 1 then 1 else 0) + (if y = x + 1 then 1 else 0) - 2 * (if y = x then 1 else 0)

/-- The entries of the one-card generator. -/
theorem Delta_apply (x y : ZMod n) :
    Delta n x y =
      (if y = x - 1 then 1 else 0) + (if y = x + 1 then 1 else 0) -
        2 * (if y = x then 1 else 0) := rfl

/-- The one-card involution family `𝒯' = (y ↦ τ_x(y))_{x ∈ ℤ/nℤ}` on positions,
`τ_x = (x  x+1)`. -/
def oneCardFamily : InvFamily (ZMod n) (ZMod n) where
  T x y := Equiv.swap x (x + 1) y
  involutive _ y := Equiv.swap_apply_self _ _ y

/-- The `x`-th involution of the one-card family is the swap `τ_x = (x  x+1)`. -/
@[simp] theorem oneCardFamily_T (x y : ZMod n) :
    (oneCardFamily n).T x y = Equiv.swap x (x + 1) y := rfl

variable [NeZero n]

/-- `Δ` acts on functions as the discrete Laplacian, for every `n`. -/
theorem Delta_mulVec (f : ZMod n → ℝ) :
    Delta n *ᵥ f = fun x => f (x - 1) + f (x + 1) - 2 * f x := by
  ext x
  simp [Delta, mulVec, dotProduct, add_mul, sub_mul, sum_add_distrib, sum_sub_distrib]

/-- The heat kernel `p_t(i, x) = P^Δ_t(i, x)`. -/
@[cycle_cutoff "def_heat_kernel"]
noncomputable def heatKernel (t : ℝ) (i x : ZMod n) : ℝ :=
  semigroup (Delta n) t i x

/-- The heat kernel is the entry `exp(tΔ)(i, x)` of the semigroup of `Δ`. -/
theorem heatKernel_def (t : ℝ) (i x : ZMod n) :
    heatKernel n t i x = semigroup (Delta n) t i x := rfl

end Generator

/-- The eigenvalues of `-Δ`, `λ_{n,j} = 2(1 - cos(2πj/n))`. -/
@[cycle_cutoff "def_lambda_nj"]
noncomputable def lambdaNJ (n j : ℕ) : ℝ :=
  2 * (1 - Real.cos (2 * Real.pi * j / n))

/-- The first eigenvalue is the spectral gap: `λ_{n,1} = λ_n`. -/
theorem lambdaNJ_one (n : ℕ) : lambdaNJ n 1 = lambdaN n := by
  simp only [lambdaNJ, lambdaN, Nat.cast_one, mul_one]
  ring

/-- The time scale `a₀ = 5`. -/
@[cycle_cutoff "def_a0"]
noncomputable def a0 : ℝ := 5

section Sums

variable (n : ℕ) [NeZero n]

/-- The collision sum `S₂(t) = ∑_x p_t(0, x)²`. -/
@[cycle_cutoff "def_S2"]
noncomputable def S2 (t : ℝ) : ℝ :=
  ∑ x : ZMod n, heatKernel n t 0 x ^ 2

/-- The triple collision sum `S₃(t) = ∑_x p_t(0, x)³`. -/
@[cycle_cutoff "def_S3"]
noncomputable def S3 (t : ℝ) : ℝ :=
  ∑ x : ZMod n, heatKernel n t 0 x ^ 3

/-- The one-card entropy `h(t) = ∑_x p_t(0, x) log(n p_t(0, x))` (`0 log 0 = 0` since
`Real.log 0 = 0`). -/
@[cycle_cutoff "def_h"]
noncomputable def oneCardEntropy (t : ℝ) : ℝ :=
  ∑ x : ZMod n, heatKernel n t 0 x * Real.log (n * heatKernel n t 0 x)

/-- The constant `B_n = ∫_0^∞ (S₃(t) - S₂(t)/n) dt` (Lebesgue integral over `(0, ∞)`). -/
@[cycle_cutoff "def_Bn"]
noncomputable def Bn : ℝ :=
  ∫ t in Set.Ioi 0, (S3 n t - S2 n t / n)

end Sums

end CycleCutoff
