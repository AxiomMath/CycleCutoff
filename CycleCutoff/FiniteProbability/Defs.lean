/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Attr
public import CycleCutoff.Definitions
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite probability: the basic functionals

Expectation, variance, entropy, relative entropy and total variation distance for real weight
vectors on a finite type, together with conditional measures, push-forwards, and conditional
expectation, variance and entropy given a map.

## Main definitions

* `CycleCutoff.IsProbVec`: `ν` has non-negative weights summing to one.
* `CycleCutoff.expectation`: the expectation `𝔼_ν[f] = ∑_z ν(z) f(z)`.
* `CycleCutoff.innerP`: the inner product `⟨f, g⟩_ν = 𝔼_ν[f g]`.
* `CycleCutoff.variance`: the variance `Var_ν(f) = 𝔼_ν[(f - 𝔼_ν f)²]`.
* `CycleCutoff.ent`: the entropy functional `Ent_ν(g) = 𝔼_ν[g log g] - 𝔼_ν[g] log 𝔼_ν[g]`.
* `CycleCutoff.relEnt`: the relative entropy `H(α ∣ ν) = ∑_z α(z) log(α(z)/ν(z))`.
* `CycleCutoff.mass`: the mass `ν(B) = ∑_{z ∈ B} ν(z)` of a set.
* `CycleCutoff.condMeasure`: the conditional measure `ν(· ∣ B)`.
* `CycleCutoff.pushforward`: the push-forward `Φ_* ν`.
* `CycleCutoff.fiber`: the fibre `Φ⁻¹(Φ(z))` of `Φ` through `z`.
* `CycleCutoff.condExp`, `CycleCutoff.condVar`, `CycleCutoff.condEnt`: conditional
  expectation, variance and entropy given a map `Φ`.

## Main results

* `CycleCutoff.condExp_apply`: `𝔼_ν[f ∣ Φ](z)` is the `ν`-weighted average of `f` over the
  fibre through `z`.
* `CycleCutoff.exists_condExp_eq_comp`: a conditional expectation given `Φ` is a function of
  `Φ`.
* `CycleCutoff.variance_eq_of_isProbVec`: `Var_ν(f) = 𝔼_ν[f²] - (𝔼_ν f)²`.
* `CycleCutoff.relEnt_nonneg`: Gibbs' inequality `0 ≤ H(α ∣ ν)`.

## Implementation notes

* A probability vector on `Ω` is a plain function `ν : Ω → ℝ`, not a `PMF` or a
  `MeasureTheory.Measure`; the conditions `0 ≤ ν z` and `∑ z, ν z = 1` are the separate
  hypothesis `IsProbVec ν`, assumed only where needed.
* The convention `0 log 0 = 0` is automatic, since `Real.log 0 = 0`.
* Subsets of `Ω` are `Finset Ω`. Conditional objects given a map `Φ` are functions on `Ω`,
  constant on the fibres of `Φ`.
* Outside their hypotheses (a set of mass zero, a non-positive weight) the definitions take
  the junk values determined by `x / 0 = 0`.
-/

@[expose] public section

open Finset

namespace CycleCutoff

variable {Ω Y : Type*} [Fintype Ω]

/-- `ν` is a probability vector: non-negative weights summing to one. -/
structure IsProbVec (ν : Ω → ℝ) : Prop where
  nonneg : ∀ z, 0 ≤ ν z
  sum_eq_one : ∑ z, ν z = 1

/-- Expectation `𝔼_ν[f] = ∑_z ν(z) f(z)` against a weight vector `ν`. -/
@[cycle_cutoff "def_expectation"]
noncomputable def expectation (ν : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ z, ν z * f z

/-- The inner product `⟨f, g⟩_ν = 𝔼_ν[f g]`. -/
@[cycle_cutoff "def_inner"]
noncomputable def innerP (ν : Ω → ℝ) (f g : Ω → ℝ) : ℝ :=
  expectation ν (fun z => f z * g z)

/-- The variance `Var_ν(f) = 𝔼_ν[(f - 𝔼_ν f)²]`. -/
@[cycle_cutoff "def_variance"]
noncomputable def variance (ν : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  expectation ν (fun z => (f z - expectation ν f) ^ 2)

/-- The entropy functional `Ent_ν(g) = 𝔼_ν[g log g] - 𝔼_ν[g] log 𝔼_ν[g]`
(meaningful for `g ≥ 0`; `0 log 0 = 0` since `Real.log 0 = 0`). -/
@[cycle_cutoff "def_ent"]
noncomputable def ent (ν : Ω → ℝ) (g : Ω → ℝ) : ℝ :=
  expectation ν (fun z => g z * Real.log (g z)) - expectation ν g * Real.log (expectation ν g)

/-- Relative entropy `H(α ∣ ν) = ∑_z α(z) log(α(z)/ν(z))` (used for `ν > 0`). -/
@[cycle_cutoff "def_relent"]
noncomputable def relEnt (α ν : Ω → ℝ) : ℝ :=
  ∑ z, α z * Real.log (α z / ν z)

/-- The mass `ν(B) = ∑_{z ∈ B} ν(z)` of a set. -/
def mass (ν : Ω → ℝ) (B : Finset Ω) : ℝ :=
  ∑ z ∈ B, ν z

open Classical in
/-- The conditional measure `ν(z ∣ B) = ν(z) 1_B(z) / ν(B)` (used for `ν(B) > 0`). -/
@[cycle_cutoff "def_cond_measure"]
noncomputable def condMeasure (ν : Ω → ℝ) (B : Finset Ω) : Ω → ℝ :=
  fun z => (if z ∈ B then ν z else 0) / mass ν B

open Classical in
/-- The push-forward `(Φ_* ν)(y) = ∑_{z ∈ Φ⁻¹(y)} ν(z)`. -/
@[cycle_cutoff "def_pushforward"]
noncomputable def pushforward (Φ : Ω → Y) (ν : Ω → ℝ) : Y → ℝ :=
  fun y => ∑ z with Φ z = y, ν z

open Classical in
/-- The fibre `Φ⁻¹(Φ(z))` of `Φ` through `z`. -/
noncomputable def fiber (Φ : Ω → Y) (z : Ω) : Finset Ω :=
  {w | Φ w = Φ z}

/-- Conditional expectation given a map:
`𝔼_ν[f ∣ Φ](z) = 𝔼_{ν(· ∣ Φ⁻¹(Φ(z)))}[f]`. -/
@[cycle_cutoff "def_cond_exp"]
noncomputable def condExp (ν : Ω → ℝ) (Φ : Ω → Y) (f : Ω → ℝ) : Ω → ℝ :=
  fun z => expectation (condMeasure ν (fiber Φ z)) f

/-- Conditional variance given a map:
`Var_ν(f ∣ Φ) = 𝔼_ν[(f - 𝔼_ν[f ∣ Φ])² ∣ Φ]`. -/
@[cycle_cutoff "def_cond_var"]
noncomputable def condVar (ν : Ω → ℝ) (Φ : Ω → Y) (f : Ω → ℝ) : Ω → ℝ :=
  condExp ν Φ (fun z => (f z - condExp ν Φ f z) ^ 2)

/-- Conditional entropy given a map:
`Ent_ν(φ ∣ Φ)(z) = Ent_{ν(· ∣ Φ⁻¹(Φ(z)))}(φ)`. -/
@[cycle_cutoff "def_cond_ent"]
noncomputable def condEnt (ν : Ω → ℝ) (Φ : Ω → Y) (φ : Ω → ℝ) : Ω → ℝ :=
  fun z => ent (condMeasure ν (fiber Φ z)) φ

/-! ### Basic API -/

section API

variable (ν : Ω → ℝ) (f g : Ω → ℝ) (c : ℝ)

/-- The expectation unfolded: `𝔼_ν[f] = ∑_z ν(z) f(z)`. -/
theorem expectation_def : expectation ν f = ∑ z, ν z * f z := rfl

/-- Expectation is additive: `𝔼_ν[f + g] = 𝔼_ν[f] + 𝔼_ν[g]`. -/
@[simp] theorem expectation_add :
    expectation ν (fun z => f z + g z) = expectation ν f + expectation ν g := by
  simp [expectation, mul_add, sum_add_distrib]

/-- Expectation commutes with subtraction: `𝔼_ν[f - g] = 𝔼_ν[f] - 𝔼_ν[g]`. -/
@[simp] theorem expectation_sub :
    expectation ν (fun z => f z - g z) = expectation ν f - expectation ν g := by
  simp [expectation, mul_sub, sum_sub_distrib]

/-- Expectation commutes with negation: `𝔼_ν[-f] = -𝔼_ν[f]`. -/
@[simp] theorem expectation_neg :
    expectation ν (fun z => -f z) = -expectation ν f := by
  simp [expectation, sum_neg_distrib]

/-- Expectation commutes with left multiplication by a constant: `𝔼_ν[c f] = c 𝔼_ν[f]`. -/
@[simp] theorem expectation_const_mul :
    expectation ν (fun z => c * f z) = c * expectation ν f := by
  simp only [expectation, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

/-- Expectation commutes with right multiplication by a constant: `𝔼_ν[f c] = 𝔼_ν[f] c`. -/
@[simp] theorem expectation_mul_const :
    expectation ν (fun z => f z * c) = expectation ν f * c := by
  simp only [expectation, sum_mul]
  exact sum_congr rfl fun _ _ => by ring

/-- The expectation of a constant `c` is `(∑_z ν(z)) c`. -/
theorem expectation_const : expectation ν (fun _ => c) = (∑ z, ν z) * c := by
  simp [expectation, sum_mul]

/-- The expectation of the zero function is zero. -/
@[simp] theorem expectation_zero : expectation ν (fun _ => 0) = 0 := by
  simp [expectation]

/-- Against a probability vector, the expectation of a constant `c` is `c`. -/
theorem IsProbVec.expectation_const {ν : Ω → ℝ} (hν : IsProbVec ν) (c : ℝ) :
    expectation ν (fun _ => c) = c := by
  rw [CycleCutoff.expectation_const, hν.sum_eq_one, one_mul]

/-- Expectation against a non-negative weight vector is monotone. -/
theorem expectation_mono {ν : Ω → ℝ} (hν : ∀ z, 0 ≤ ν z) {f g : Ω → ℝ}
    (hfg : ∀ z, f z ≤ g z) : expectation ν f ≤ expectation ν g :=
  sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hfg z) (hν z)

/-- Against a non-negative weight vector, a non-negative function has non-negative
expectation. -/
theorem expectation_nonneg {ν : Ω → ℝ} (hν : ∀ z, 0 ≤ ν z) {f : Ω → ℝ}
    (hf : ∀ z, 0 ≤ f z) : 0 ≤ expectation ν f :=
  sum_nonneg fun z _ => mul_nonneg (hν z) (hf z)

/-- Every weight of the uniform vector is `|Ω|⁻¹`. -/
theorem unif_apply (z : Ω) : unif Ω z = (Fintype.card Ω : ℝ)⁻¹ := rfl

/-- The uniform vector on a non-empty finite type is a probability vector. -/
theorem isProbVec_unif [Nonempty Ω] : IsProbVec (unif Ω) where
  nonneg _ := by simp [unif]
  sum_eq_one := by
    simp [unif, Finset.card_univ]

/-- Expectation against the uniform vector is the average `|Ω|⁻¹ ∑_z f(z)`. -/
theorem expectation_unif : expectation (unif Ω) f = (Fintype.card Ω : ℝ)⁻¹ * ∑ z, f z := by
  simp [expectation, unif, mul_sum]

/-- `w` lies in the fibre of `Φ` through `z` if and only if `Φ w = Φ z`. -/
theorem mem_fiber {Φ : Ω → Y} {z w : Ω} : w ∈ fiber Φ z ↔ Φ w = Φ z := by
  classical
  simp [fiber]

/-- Every point lies in the fibre through itself. -/
theorem mem_fiber_self (Φ : Ω → Y) (z : Ω) : z ∈ fiber Φ z := mem_fiber.2 rfl

/-- If `w` lies in the fibre of `Φ` through `z`, the fibres through `w` and `z` coincide. -/
theorem fiber_eq_of_mem {Φ : Ω → Y} {z w : Ω} (h : w ∈ fiber Φ z) : fiber Φ w = fiber Φ z := by
  ext v
  rw [mem_fiber, mem_fiber, mem_fiber.1 h]

omit [Fintype Ω] in
/-- Under a strictly positive weight vector, a non-empty set has positive mass. -/
theorem mass_pos_of_pos {ν : Ω → ℝ} (hν : ∀ z, 0 < ν z) {B : Finset Ω} (hB : B.Nonempty) :
    0 < mass ν B :=
  sum_pos (fun z _ => hν z) hB

/-- The conditional expectation, unfolded: the `ν`-weighted average of `f` over the fibre. -/
theorem condExp_apply (Φ : Ω → Y) (z : Ω) :
    condExp ν Φ f z = (∑ w ∈ fiber Φ z, ν w * f w) / mass ν (fiber Φ z) := by
  classical
  simp only [condExp, expectation, condMeasure, sum_div]
  rw [← sum_filter_add_sum_filter_not univ (· ∈ fiber Φ z)]
  simp only [filter_mem_eq_inter, univ_inter]
  rw [sum_eq_zero (s := filter (fun x => x ∉ fiber Φ z) univ) (by
    intro w hw
    simp only [mem_filter] at hw
    simp [hw.2]), add_zero]
  refine sum_congr rfl fun w hw => ?_
  simp [hw, div_mul_eq_mul_div]

end API

section Fibres

variable (ν : Ω → ℝ) (Φ : Ω → Y) (f : Ω → ℝ)

/-- A conditional expectation given `Φ` is constant on the fibres of `Φ`. -/
theorem condExp_eq_of_eq {z w : Ω} (h : Φ w = Φ z) : condExp ν Φ f w = condExp ν Φ f z := by
  rw [condExp_apply, condExp_apply, fiber_eq_of_mem (mem_fiber.2 h)]

/-- A conditional expectation given `Φ` is a function of `Φ`. -/
theorem exists_condExp_eq_comp : ∃ h : Y → ℝ, ∀ z, condExp ν Φ f z = h (Φ z) := by
  classical
  refine ⟨fun y => if hy : ∃ z, Φ z = y then condExp ν Φ f hy.choose else 0, fun z => ?_⟩
  have hz : ∃ w, Φ w = Φ z := ⟨z, rfl⟩
  dsimp only
  rw [dif_pos hz]
  exact (condExp_eq_of_eq ν Φ f hz.choose_spec).symm

/-- Conditional expectation given `Φ` is additive. -/
theorem condExp_add (g : Ω → ℝ) :
    condExp ν Φ (fun w => f w + g w) = fun w => condExp ν Φ f w + condExp ν Φ g w :=
  funext fun _ => expectation_add _ _ _

/-- Conditional expectation given `Φ` commutes with subtraction. -/
theorem condExp_sub (g : Ω → ℝ) :
    condExp ν Φ (fun w => f w - g w) = fun w => condExp ν Φ f w - condExp ν Φ g w :=
  funext fun _ => expectation_sub _ _ _

end Fibres

/-- The uniform weight is positive. -/
theorem unif_pos (z : Ω) : 0 < unif Ω z := by
  have : Nonempty Ω := ⟨z⟩
  exact inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos)

/-- A point mass is a probability vector. -/
theorem isProbVec_single [DecidableEq Ω] (a : Ω) : IsProbVec (Pi.single a 1 : Ω → ℝ) :=
  ⟨fun z => by by_cases h : z = a <;> simp [h], by simp⟩

/-- The variance is the second moment minus the squared mean. -/
theorem variance_eq_of_isProbVec {ν : Ω → ℝ} (hν : IsProbVec ν) (f : Ω → ℝ) :
    variance ν f = expectation ν (fun z => f z ^ 2) - expectation ν f ^ 2 := by
  have h : (fun z => (f z - expectation ν f) ^ 2) =
      fun z => f z ^ 2 - (2 * expectation ν f) * f z + expectation ν f ^ 2 := by
    funext z; ring
  rw [variance, h, expectation_add, expectation_sub, expectation_const_mul,
    hν.expectation_const]
  ring

/-- Expectation commutes with finite sums. -/
theorem expectation_sum {ι : Type*} (ν : Ω → ℝ) (s : Finset ι) (f : ι → Ω → ℝ) :
    expectation ν (fun z => ∑ e ∈ s, f e z) = ∑ e ∈ s, expectation ν (f e) := by
  simp only [expectation, mul_sum]
  exact sum_comm

/-- Gibbs' inequality: the relative entropy of a probability vector with respect to a positive
probability vector is non-negative. -/
theorem relEnt_nonneg {α ν : Ω → ℝ} (hα : IsProbVec α) (hν : IsProbVec ν)
    (hνpos : ∀ z, 0 < ν z) : 0 ≤ relEnt α ν := by
  have key : ∀ z, α z - ν z ≤ α z * Real.log (α z / ν z) := by
    intro z
    rcases (hα.nonneg z).eq_or_lt with h | h
    · rw [← h]; simp [(hνpos z).le]
    · have hl := Real.one_sub_inv_le_log_of_pos (div_pos h (hνpos z))
      rw [inv_div] at hl
      have : α z * (1 - ν z / α z) = α z - ν z := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hl h.le]
  calc (0 : ℝ) = ∑ z, (α z - ν z) := by
        rw [sum_sub_distrib, hα.sum_eq_one, hν.sum_eq_one, sub_self]
    _ ≤ relEnt α ν := sum_le_sum fun z _ => key z

end CycleCutoff
