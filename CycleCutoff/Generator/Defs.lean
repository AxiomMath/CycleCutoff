/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.FiniteProbability.Defs
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Involution generators and their semigroups

An involution family on `Ω` is a family `𝒯 = (T_e)_{e ∈ ι}` of involutions of `Ω`. For finite `ι`
and `Ω` it has the rate matrix `Q_𝒯(z, w) = ∑_e (1[T_e z = w] - 1[z = w])`, the generator
`(L_𝒯 f)(z) = ∑_e (f(T_e z) - f(z))`, the semigroup `P^𝒯_t = exp(t Q_𝒯)` and the Dirichlet form
`𝒟_𝒯(f) = ⟨f, -L_𝒯 f⟩_{u_Ω}`.

## Main definitions

* `CycleCutoff.InvFamily.prod`: the product family on `Ω₁ × Ω₂`.
* `CycleCutoff.InvFamily.generator`: the generator `L_𝒯`.
* `CycleCutoff.InvFamily.dirichletForm`: the Dirichlet form `𝒟_𝒯`.

## Main results

* `CycleCutoff.InvFamily.rateMatrix_mulVec`: `Q_𝒯` acting on functions is `L_𝒯`.
* `CycleCutoff.semigroup_add`: `P^Q_{s + t} = P^Q_s P^Q_t`.

## Implementation notes

* The involutivity `T e ∘ T e = id` is a field of `InvFamily`.
* The rate matrix is a `Matrix Ω Ω ℝ`, and `semigroup Q t` is Mathlib's matrix exponential
  `NormedSpace.exp (t • Q)`. The generator is a plain function on `Ω → ℝ`.
* `P^Q_t f` is `semigroup Q t *ᵥ f`; a row vector `α` is pushed by `α ᵥ* semigroup Q t`.
-/

@[expose] public section

open Finset Matrix

namespace CycleCutoff

namespace InvFamily

variable {ι Ω : Type*} (𝒯 : InvFamily ι Ω)

/-- Each map of an involution family is an involution: `T_e (T_e z) = z`. -/
@[simp] theorem T_T (e : ι) (z : Ω) : 𝒯.T e (𝒯.T e z) = z := 𝒯.involutive e z

/-- Each map of an involution family is a bijection. -/
theorem bijective (e : ι) : Function.Bijective (𝒯.T e) := (𝒯.involutive e).bijective

/-- `T_e z = w` if and only if `T_e w = z`. -/
theorem T_eq_iff (e : ι) (z w : Ω) : 𝒯.T e z = w ↔ 𝒯.T e w = z := by
  constructor <;> rintro rfl <;> simp

/-- The product family on `Ω₁ × Ω₂`: the maps `T¹_e × id` (`e ∈ ι₁`) and `id × T²_e` (`e ∈ ι₂`),
indexed by `ι₁ ⊕ ι₂`. -/
def prod {ι₁ ι₂ Ω₁ Ω₂ : Type*} (𝒯₁ : InvFamily ι₁ Ω₁) (𝒯₂ : InvFamily ι₂ Ω₂) :
    InvFamily (ι₁ ⊕ ι₂) (Ω₁ × Ω₂) where
  T
    | .inl e => fun p => (𝒯₁.T e p.1, p.2)
    | .inr e => fun p => (p.1, 𝒯₂.T e p.2)
  involutive
    | .inl e => fun p => by simp
    | .inr e => fun p => by simp

variable [Fintype ι]

/-- The generator `(L_𝒯 f)(z) = ∑_e (f(T_e z) - f(z))` of an involution family. -/
@[cycle_cutoff "def_inv_generator"]
noncomputable def generator (f : Ω → ℝ) : Ω → ℝ :=
  fun z => ∑ e, (f (𝒯.T e z) - f z)

/-- The generator is the rate matrix acting on functions: `L_𝒯 f = Q_𝒯 f`. -/
theorem rateMatrix_mulVec [Fintype Ω] [DecidableEq Ω] (f : Ω → ℝ) :
    𝒯.rateMatrix *ᵥ f = 𝒯.generator f := by
  ext z
  simp only [mulVec, dotProduct, rateMatrix, generator, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun e _ => ?_
  simp [sub_mul, sum_sub_distrib, ite_mul]

end InvFamily

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
/-- The Dirichlet form `𝒟_𝒯(f) = ⟨f, -L_𝒯 f⟩_{u_Ω}`. -/
@[cycle_cutoff "def_dirichlet_form"]
noncomputable def InvFamily.dirichletForm {ι : Type*} [Fintype ι] (𝒯 : InvFamily ι Ω)
    (f : Ω → ℝ) : ℝ :=
  innerP (unif Ω) f (fun z => -𝒯.generator f z)

/-- The semigroup at time zero is the identity: `P^Q_0 = 1`. -/
theorem semigroup_zero (Q : Matrix Ω Ω ℝ) : semigroup Q 0 = 1 := by
  simp [semigroup]

/-- The semigroup property `P^Q_{s + t} = P^Q_s P^Q_t`. -/
theorem semigroup_add (Q : Matrix Ω Ω ℝ) (s t : ℝ) :
    semigroup Q (s + t) = semigroup Q s * semigroup Q t := by
  rw [semigroup, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl Q).smul_left s).smul_right t)

end CycleCutoff
