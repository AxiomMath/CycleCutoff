/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.OneCard.Defs
public import CycleCutoff.OneCard.BIntegrandNonneg
public import CycleCutoff.Generator.SemigroupDeriv
public import CycleCutoff.Cycle.LambdaLower
public import CycleCutoff.OneCard.S2Bound
public import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Integrability of the collision sum

For `n ≥ 3`, the function `t ↦ S₂(t) - 1/n` is integrable on `(0, ∞)`.

## Main results

* `CycleCutoff.continuous_S2`: `t ↦ S₂(t)` is continuous.
* `CycleCutoff.one_div_le_S2`: `1/n ≤ S₂(t)`.
* `CycleCutoff.integrableOn_S2_sub`: `t ↦ S₂(t) - 1/n` is integrable on `(0, ∞)`.
-/

public section

open Finset MeasureTheory Real

namespace CycleCutoff

variable {n : ℕ} [NeZero n]

/-- The collision sum `S₂` is continuous in time. -/
theorem continuous_S2 : Continuous (S2 n) := by
  have h : ∀ x : ZMod n, Continuous fun t => heatKernel n t 0 x := fun x =>
    continuous_iff_continuousAt.2 fun t =>
      (hasDerivAt_semigroup_apply (Delta n) t 0 x).continuousAt
  exact continuous_finsetSum _ fun x _ => (h x).pow 2

/-- The collision sum is at least that of the uniform distribution: `1/n ≤ S₂(t)`. -/
theorem one_div_le_S2 (t : ℝ) : 1 / (n : ℝ) ≤ S2 n t := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_neZero n)
  have h := sq_sum_le_card_mul_sum_sq (s := univ) (f := heatKernel n t 0)
  rw [sum_heatKernel t 0, one_pow, card_univ, ZMod.card] at h
  rwa [div_le_iff₀ hn, mul_comm]

/-- **Integrability of the collision sum**: for `n ≥ 3`, `t ↦ S₂(t) - 1/n` is integrable
on `(0, ∞)`. -/
@[cycle_cutoff "lem_S2_integrable"]
theorem integrableOn_S2_sub (hn : 3 ≤ n) :
    IntegrableOn (fun t => S2 n t - 1 / n) (Set.Ioi 0) := by
  obtain ⟨c, -, hc⟩ := exists_mul_S2_sub_one_le
  have hlam : 0 < lambdaN n :=
    lt_of_lt_of_le (by positivity) (sixteen_div_sq_le_lambdaN (by omega))
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_neZero n)
  set T₀ := a0 / lambdaN n with hT₀
  have hT₀0 : 0 ≤ T₀ := div_nonneg (by norm_num [a0]) hlam.le
  have hcont : Continuous fun t => S2 n t - 1 / n := continuous_S2.sub continuous_const
  rw [← Set.Ioc_union_Ioi_eq_Ioi hT₀0]
  refine IntegrableOn.union ?_ ?_
  · exact (hcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  · have hexp : IntegrableOn (fun t => c / n * Real.exp (-(2 * lambdaN n) * t)) (Set.Ioi T₀) :=
      (exp_neg_integrableOn_Ioi T₀ (by positivity)).const_mul _
    refine Integrable.mono' hexp hcont.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t (ht : T₀ < t) => ?_
    have h0 : 0 ≤ S2 n t - 1 / n := sub_nonneg.2 (one_div_le_S2 t)
    rw [Real.norm_of_nonneg h0, div_mul_eq_mul_div, le_div_iff₀ hn0, sub_mul,
      one_div_mul_cancel hn0.ne', mul_comm,
      show -(2 * lambdaN n) * t = -2 * lambdaN n * t by ring]
    exact hc n hn t ht.le

end CycleCutoff
