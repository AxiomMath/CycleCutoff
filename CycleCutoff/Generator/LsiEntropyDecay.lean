/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.SemigroupLower
public import CycleCutoff.Generator.SemigroupSymmetric
public import CycleCutoff.Generator.SemigroupDeriv
public import CycleCutoff.Generator.DirichletFormula
public import CycleCutoff.Generator.LogMeanIneq
public import CycleCutoff.Generator.SemigroupRowsum
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Exponential decay of relative entropy under a log-Sobolev inequality

Let `𝒯` be an involution family on `Ω` satisfying the log-Sobolev inequality `Ent_u(f²) ≤ A 𝒟_𝒯(f)`
with constant `A > 0`. Then for every probability vector `α` with full support and every `t ≥ 0`,
`H(α P^𝒯_t ∣ u) ≤ e^{-4t/A} H(α ∣ u)`.

## Main results

* `CycleCutoff.ent_unif_eq_inv_card_mul_relEnt`: `Ent_u(p) = |Ω|⁻¹ H(p ∣ u)` for a positive
  probability vector `p`.
* `CycleCutoff.InvFamily.sum_sub_T_mul`: the summation-by-parts identity
  `∑_z (f(T_e z) - f(z)) g(z) = -½ ∑_z (f(T_e z) - f(z)) (g(T_e z) - g(z))`.
* `CycleCutoff.InvFamily.hasDerivAt_vecMul_semigroup_apply`: `d/dt α P^𝒯_t = L_𝒯 (α P^𝒯_t)`.
* `CycleCutoff.InvFamily.sum_generator_mul_log_le_of_lsi`: the entropy-production bound
  `∑_z (L_𝒯 p)(z) (log (p(z)/u(z)) + 1) ≤ -(4/A) H(p ∣ u)`.
* `CycleCutoff.InvFamily.relEnt_semigroup_le_of_lsi`: the exponential decay of relative entropy.
-/

public section

open Finset Matrix

namespace CycleCutoff

variable {ι Ω : Type*} [Fintype Ω]

/-- For a probability vector `p` with positive entries, the uniform entropy of `p` is
`|Ω|⁻¹ H(p ∣ u)`. -/
theorem ent_unif_eq_inv_card_mul_relEnt {p : Ω → ℝ} (hp : ∀ z, 0 < p z)
    (hsum : ∑ z, p z = 1) :
    ent (unif Ω) p = (Fintype.card Ω : ℝ)⁻¹ * relEnt p (unif Ω) := by
  have hne : Nonempty Ω :=
    univ_nonempty_iff.1 (nonempty_of_sum_ne_zero (hsum.trans_ne one_ne_zero))
  have hc : (Fintype.card Ω : ℝ)⁻¹ ≠ 0 := by positivity
  have h : ∀ z, p z * Real.log (p z / (Fintype.card Ω : ℝ)⁻¹) =
      p z * Real.log (p z) - p z * Real.log (Fintype.card Ω : ℝ)⁻¹ := fun z => by
    rw [Real.log_div (hp z).ne' hc]; ring
  simp only [ent, expectation_unif, relEnt, unif_apply, h, sum_sub_distrib, ← sum_mul, hsum,
    mul_one]
  ring

namespace InvFamily

variable (𝒯 : InvFamily ι Ω)

/-- Summation by parts along an involution:
`∑_z (f(T_e z) - f(z)) g(z) = -½ ∑_z (f(T_e z) - f(z)) (g(T_e z) - g(z))`. -/
theorem sum_sub_T_mul (e : ι) (f g : Ω → ℝ) :
    ∑ z, (f (𝒯.T e z) - f z) * g z =
      -(1 / 2) * ∑ z, (f (𝒯.T e z) - f z) * (g (𝒯.T e z) - g z) := by
  set σ := (𝒯.involutive e).toPerm _
  have h1 : ∑ z, f (𝒯.T e z) * g (𝒯.T e z) = ∑ z, f z * g z :=
    Equiv.sum_comp σ (fun z => f z * g z)
  have h2 : ∑ z, f z * g (𝒯.T e z) = ∑ z, f (𝒯.T e z) * g z := by
    simpa [σ] using Equiv.sum_comp σ (fun z => f (𝒯.T e z) * g z)
  simp only [mul_sub, sub_mul, sum_sub_distrib]
  linarith

variable [Fintype ι]

/-- **Entropy production under a log-Sobolev inequality.** If `Ent_u(f²) ≤ A 𝒟_𝒯(f)` for all `f`,
then for every probability vector `p` with positive entries,
`∑_z (L_𝒯 p)(z) (log (p(z)/u(z)) + 1) ≤ -(4/A) H(p ∣ u)`. -/
theorem sum_generator_mul_log_le_of_lsi {A : ℝ} (hA : 0 < A)
    (hLSI : ∀ f : Ω → ℝ, ent (unif Ω) (fun z => f z ^ 2) ≤ A * 𝒯.dirichletForm f)
    {p : Ω → ℝ} (hp : ∀ z, 0 < p z) (hsum : ∑ z, p z = 1) :
    ∑ z, 𝒯.generator p z * (Real.log (p z / unif Ω z) + 1) ≤
      -(4 / A) * relEnt p (unif Ω) := by
  have hne : Nonempty Ω :=
    univ_nonempty_iff.1 (nonempty_of_sum_ne_zero (hsum.trans_ne one_ne_zero))
  set c := (Fintype.card Ω : ℝ)⁻¹ with hc_def
  have hc : 0 < c := by positivity
  set s : Ω → ℝ := fun z => Real.sqrt (p z)
  set S := ∑ e, ∑ z, (s (𝒯.T e z) - s z) ^ 2 with hS_def
  set R := relEnt p (unif Ω)
  have h1 : ∑ z, 𝒯.generator p z * (Real.log (p z / unif Ω z) + 1) =
      ∑ e, -(1 / 2) * ∑ z, (p (𝒯.T e z) - p z) *
        (Real.log (p (𝒯.T e z)) - Real.log (p z)) := by
    simp only [generator, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun e _ => ?_
    rw [𝒯.sum_sub_T_mul e p (fun z => Real.log (p z / unif Ω z) + 1)]
    congr 1
    refine sum_congr rfl fun z _ => ?_
    have hu : ∀ w, unif Ω w ≠ 0 := fun w => hc.ne'
    rw [Real.log_div (hp _).ne' (hu _), Real.log_div (hp _).ne' (hu _), unif_apply, unif_apply]
    ring
  have h2 : ∀ e, -(1 / 2) * ∑ z, (p (𝒯.T e z) - p z) *
        (Real.log (p (𝒯.T e z)) - Real.log (p z)) ≤
      -(1 / 2) * ∑ z, 4 * (s (𝒯.T e z) - s z) ^ 2 := fun e =>
    mul_le_mul_of_nonpos_left
      (sum_le_sum fun z _ => four_mul_sqrt_sub_sq_le _ _ (hp _) (hp _)) (by norm_num)
  have h3 : 𝒯.dirichletForm s = (1 / 2) * c * S := by
    simp only [dirichletForm_eq, expectation_unif, hS_def, mul_sum, hc_def, mul_assoc]
  have h4 : ent (unif Ω) (fun z => s z ^ 2) = c * R := by
    have : (fun z => s z ^ 2) = p := funext fun z => Real.sq_sqrt (hp z).le
    rw [this, ent_unif_eq_inv_card_mul_relEnt hp hsum]
  have hRS : R ≤ A / 2 * S := by
    have hL := hLSI s
    rw [h4, h3] at hL
    exact le_of_mul_le_mul_left (by linarith) hc
  calc ∑ z, 𝒯.generator p z * (Real.log (p z / unif Ω z) + 1)
      ≤ ∑ e, -(1 / 2) * ∑ z, 4 * (s (𝒯.T e z) - s z) ^ 2 :=
        h1.trans_le (sum_le_sum fun e _ => h2 e)
    _ = -(4 / A) * (A / 2 * S) := by
        simp only [hS_def, ← mul_sum]
        field_simp
    _ ≤ -(4 / A) * R :=
        mul_le_mul_of_nonpos_left hRS (neg_nonpos.2 (by positivity))

variable [DecidableEq Ω]

/-- A row vector times the rate matrix is the generator applied to it: `v Q_𝒯 = L_𝒯 v`. -/
theorem vecMul_rateMatrix (v : Ω → ℝ) : v ᵥ* 𝒯.rateMatrix = 𝒯.generator v := by
  rw [← mulVec_transpose, rateMatrix_transpose, rateMatrix_mulVec]

/-- The entries of `α P^𝒯_t` satisfy `d/dt (α P^𝒯_t)(w) = L_𝒯 (α P^𝒯_t)(w)`. -/
theorem hasDerivAt_vecMul_semigroup_apply (α : Ω → ℝ) (t : ℝ) (w : Ω) :
    HasDerivAt (fun s => (α ᵥ* 𝒯.semigroup s) w) (𝒯.generator (α ᵥ* 𝒯.semigroup t) w) t := by
  rw [← vecMul_rateMatrix, vecMul_vecMul]
  simp only [vecMul, dotProduct]
  exact HasDerivAt.fun_sum fun z _ =>
    (hasDerivAt_semigroup_apply 𝒯.rateMatrix t z w).const_mul (α z)

/-- For `t ≥ 0`, `α P^𝒯_t` has positive entries when `α` does. -/
theorem vecMul_semigroup_apply_pos {α : Ω → ℝ} (hα : ∀ z, 0 < α z) {t : ℝ} (ht : 0 ≤ t)
    (w : Ω) : 0 < (α ᵥ* 𝒯.semigroup t) w := by
  have hww : 0 < 𝒯.semigroup t w w :=
    lt_of_lt_of_le (Real.exp_pos _) (by simpa using 𝒯.exp_mul_pow_le_semigroup ht 0 w w)
  simp only [vecMul, dotProduct]
  calc 0 < α w * 𝒯.semigroup t w w := mul_pos (hα w) hww
    _ ≤ ∑ z, α z * 𝒯.semigroup t z w :=
      single_le_sum (f := fun z => α z * 𝒯.semigroup t z w)
        (fun z _ => mul_nonneg (hα z).le (𝒯.semigroup_apply_nonneg ht z w)) (mem_univ w)

/-- `α P^𝒯_t` has the same total mass as `α`. -/
theorem sum_vecMul_semigroup (α : Ω → ℝ) (t : ℝ) :
    ∑ w, (α ᵥ* 𝒯.semigroup t) w = ∑ z, α z := by
  simp only [vecMul, dotProduct]
  rw [sum_comm]
  refine sum_congr rfl fun z _ => ?_
  rw [← mul_sum, 𝒯.sum_semigroup_apply, mul_one]

/-- **Exponential decay of relative entropy under a log-Sobolev inequality.** If
`Ent_u(f²) ≤ A 𝒟_𝒯(f)` for all `f`, with `A > 0`, then for every probability vector `α` with
positive entries and every `t ≥ 0`, `H(α P^𝒯_t ∣ u) ≤ e^{-4t/A} H(α ∣ u)`. -/
@[cycle_cutoff "lem_lsi_entropy_decay"]
theorem relEnt_semigroup_le_of_lsi (A : ℝ) (hA : 0 < A)
    (hLSI : ∀ f : Ω → ℝ, ent (unif Ω) (fun z => f z ^ 2) ≤ A * 𝒯.dirichletForm f)
    (α : Ω → ℝ) (hα : IsProbVec α) (hαpos : ∀ z, 0 < α z) {t : ℝ} (ht : 0 ≤ t) :
    relEnt (α ᵥ* 𝒯.semigroup t) (unif Ω) ≤ Real.exp (-4 * t / A) * relEnt α (unif Ω) := by
  have hne : Nonempty Ω :=
    univ_nonempty_iff.1 (nonempty_of_sum_ne_zero (hα.sum_eq_one.trans_ne one_ne_zero))
  have hu : ∀ w, 0 < unif Ω w := unif_pos
  set H : ℝ → ℝ := fun s => relEnt (α ᵥ* 𝒯.semigroup s) (unif Ω) with hH
  set H' : ℝ → ℝ := fun s => ∑ w, 𝒯.generator (α ᵥ* 𝒯.semigroup s) w *
      (Real.log ((α ᵥ* 𝒯.semigroup s) w / unif Ω w) + 1) with hH'
  have hderiv : ∀ s, 0 ≤ s → HasDerivAt H (H' s) s := by
    intro s hs
    simp only [hH, hH', relEnt]
    refine HasDerivAt.fun_sum fun w _ => ?_
    have hp := 𝒯.hasDerivAt_vecMul_semigroup_apply α s w
    have hpos := 𝒯.vecMul_semigroup_apply_pos hαpos hs w
    have hl := (hp.div_const (unif Ω w)).log (div_pos hpos (hu w)).ne'
    refine (hp.fun_mul hl).congr_deriv ?_
    have hu' := (hu w).ne'
    field_simp
  set G : ℝ → ℝ := fun s => Real.exp (4 * s / A) * H s with hG
  have hGderiv : ∀ s, 0 ≤ s → HasDerivAt G
      (Real.exp (4 * s / A) * (4 * 1 / A) * H s + Real.exp (4 * s / A) * H' s) s := fun s hs =>
    (((hasDerivAt_id s).const_mul 4).div_const A).exp.mul (hderiv s hs)
  have hanti : AntitoneOn G (Set.Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (f' := fun s => Real.exp (4 * s / A) * (4 * 1 / A) * H s + Real.exp (4 * s / A) * H' s)
      (fun s hs => (hGderiv s hs).continuousAt.continuousWithinAt)
      (fun s hs => ?_) (fun s hs => ?_)
    · rw [interior_Ici] at hs
      exact (hGderiv s (le_of_lt hs)).hasDerivWithinAt
    · rw [interior_Ici] at hs
      have hsum : ∑ w, (α ᵥ* 𝒯.semigroup s) w = 1 := by
        rw [sum_vecMul_semigroup, hα.sum_eq_one]
      have key := 𝒯.sum_generator_mul_log_le_of_lsi hA hLSI
        (𝒯.vecMul_semigroup_apply_pos hαpos (le_of_lt hs)) hsum
      have hexp := Real.exp_pos (4 * s / A)
      have : 4 * 1 / A * H s + H' s ≤ 0 := by
        simp only [hH, hH']
        linarith
      nlinarith
  have hGt := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  have hG0 : G 0 = relEnt α (unif Ω) := by
    simp [hG, hH, InvFamily.semigroup, semigroup_zero]
  rw [hG0] at hGt
  rwa [neg_mul, neg_div, Real.exp_neg, le_inv_mul_iff₀ (Real.exp_pos _)]

end InvFamily

end CycleCutoff
