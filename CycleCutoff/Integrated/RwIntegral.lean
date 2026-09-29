/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Integrated.Defs
public import CycleCutoff.Generator.SemigroupSymmetric
public import CycleCutoff.OneCard.DeltaInvolution
public import CycleCutoff.Generator.SemigroupDeriv
public import CycleCutoff.OneCard.HeatDeviation
public import CycleCutoff.Generator.SemigroupRowsum
public import CycleCutoff.OneCard.S2Integrable
public import CycleCutoff.OneCard.S2Bound
public import CycleCutoff.Cycle.LambdaLower
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The integrated collision sum

For `n ≥ 3`, `∫_0^∞ (S₂(t) - 1/n) dt = (n² - 1)/(24 n)`.

## Main results

* `CycleCutoff.integral_S2_sub`: `∫_{(0,∞)} (S₂(t) - 1/n) dt = (n² - 1)/(24 n)` for `n ≥ 3`.

## Implementation notes

The integral over `[0, ∞)` is taken over `Set.Ioi 0`, which differs from `Set.Ici 0` by a null set.
-/

public section

open Finset Matrix MeasureTheory Filter Topology

namespace CycleCutoff

variable {n : ℕ} [NeZero n]

/-- The corrector with `m = n` has mean zero. -/
private lemma sum_corrector_self : ∑ r : ZMod n, corrector n n r = 0 := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  simp only [corrector_apply]
  rw [sum_sub_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul, ← sum_div,
    sum_val_mul_sub_val]
  field_simp
  ring

/-- The corrector with `m = n` solves `Δu = (1/n - δ₀)/2`. -/
private lemma Delta_mulVec_corrector_self (hn : 2 ≤ n) (x : ZMod n) :
    (Delta n *ᵥ corrector n n) x = 1 / (2 * n) - if x = 0 then 1 / 2 else 0 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  have h : (n : ℝ) / (2 * n) = 1 / 2 := by
    rw [div_eq_div_iff (mul_ne_zero two_ne_zero hn0) two_ne_zero]; ring
  rw [Delta_mulVec_corrector hn, h]

/-- **Integrated collision sum**: for `n ≥ 3`, `∫_0^∞ (S₂(t) - 1/n) dt = (n² - 1)/(24 n)`. -/
@[cycle_cutoff "lem_rw_integral"]
theorem integral_S2_sub (hn : 3 ≤ n) :
    ∫ t in Set.Ioi 0, (S2 n t - 1 / (n : ℝ)) = ((n : ℝ) ^ 2 - 1) / (24 * n) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  set u := corrector n n with hu
  set F : ℝ → ℝ := fun T => ∑ x, heatKernel n (2 * T) 0 x * u x with hF
  have hderiv : ∀ T, HasDerivAt (fun T => -F T) (S2 n T - 1 / n) T := by
    intro T
    have hx : ∀ x ∈ (univ : Finset (ZMod n)), HasDerivAt (fun T => heatKernel n (2 * T) 0 x * u x)
        ((semigroup (Delta n) (2 * T) * Delta n) 0 x * (2 * 1) * u x) T := fun x _ =>
      ((hasDerivAt_semigroup_apply (Delta n) (2 * T) 0 x).comp T
        ((hasDerivAt_id T).const_mul 2)).mul_const (u x)
    refine (HasDerivAt.fun_sum hx).neg.congr_deriv ?_
    have hsum : ∑ x, (semigroup (Delta n) (2 * T) * Delta n) 0 x * u x =
        ((semigroup (Delta n) (2 * T) * Delta n) *ᵥ u) 0 :=
      rfl
    simp only [mul_one, mul_comm _ (2 : ℝ), mul_assoc, ← mul_sum]
    rw [hsum, ← mulVec_mulVec]
    have hΔ : Delta n *ᵥ u = fun y : ZMod n => 1 / (2 * (n : ℝ)) - if y = 0 then 1 / 2 else 0 :=
      funext fun x => by rw [hu]; exact Delta_mulVec_corrector_self (by omega) x
    rw [hΔ]
    simp only [mulVec, dotProduct, mul_sub, sum_sub_distrib, mul_ite, mul_zero, sum_ite_eq',
      mem_univ, if_true, ← sum_mul]
    rw [show ∑ x, semigroup (Delta n) (2 * T) 0 x = 1 from sum_heatKernel (2 * T) 0,
      S2_eq_heatKernel_two_mul, heatKernel_def]
    field_simp
    ring
  have hFTC : ∀ T, ∫ t in (0 : ℝ)..T, (S2 n t - 1 / (n : ℝ)) = u 0 - F T := by
    intro T
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      ((continuous_S2.sub continuous_const).intervalIntegrable _ _)]
    have hF0 : F 0 = u 0 := by
      simp [hF, heatKernel_def, semigroup_zero, Matrix.one_apply]
    rw [hF0]
    ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    obtain ⟨c, -, hc⟩ := exists_abs_mul_heatKernel_sub_one_le
    have hlam : 0 < lambdaN n :=
      lt_of_lt_of_le (by positivity) (sixteen_div_sq_le_lambdaN (by omega))
    have hp : ∀ x : ZMod n, Tendsto (fun t => heatKernel n t 0 x) atTop (𝓝 (1 / n)) := by
      intro x
      have hexp : Tendsto (fun t => c * Real.exp (-lambdaN n * t)) atTop (𝓝 0) := by
        simpa [neg_mul] using
          (Real.tendsto_exp_neg_atTop_nhds_zero.comp
            (tendsto_id.const_mul_atTop hlam)).const_mul c
      have hg : Tendsto (fun t => (n : ℝ) * heatKernel n t 0 x - 1) atTop (𝓝 0) := by
        refine squeeze_zero_norm' ?_ hexp
        filter_upwards [eventually_ge_atTop (a0 / lambdaN n)] with t ht
        exact hc n hn t ht x
      have := (hg.add_const 1).div_const (n : ℝ)
      refine (this.congr fun t => ?_).trans (by rw [zero_add])
      field_simp
      ring
    have hsum := tendsto_finsetSum (univ : Finset (ZMod n)) fun x _ =>
      ((hp x).comp (tendsto_id.const_mul_atTop two_pos)).mul_const (u x)
    rw [← mul_sum, sum_corrector_self, mul_zero] at hsum
    exact hsum
  have h1 := intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_S2_sub hn) tendsto_id
  have h2 : Tendsto (fun T => ∫ t in (0 : ℝ)..T, (S2 n t - 1 / (n : ℝ))) atTop (𝓝 (u 0)) := by
    have h := (tendsto_const_nhds (x := u 0)).sub hlim
    rw [sub_zero] at h
    exact h.congr fun T => (hFTC T).symm
  rw [tendsto_nhds_unique h1 h2, hu, corrector_apply, ZMod.val_zero]
  field_simp
  ring

end CycleCutoff
