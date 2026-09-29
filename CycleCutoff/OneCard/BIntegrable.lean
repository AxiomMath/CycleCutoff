/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.OneCard.Defs
public import CycleCutoff.OneCard.BIntegrandNonneg
public import CycleCutoff.OneCard.BTail
public import CycleCutoff.OneCard.S2Integrable
public import CycleCutoff.Generator.SemigroupDeriv
public import CycleCutoff.Cycle.LambdaLower
public import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Integrability of the integrand of `B_n`

For `n ≥ 3`, the function `t ↦ S₃(t) - S₂(t)/n` is integrable on `(0, ∞)`.

## Main results

* `CycleCutoff.continuous_S3`: `t ↦ S₃(t)` is continuous.
* `CycleCutoff.integrableOn_S3_sub_S2_div`: `t ↦ S₃(t) - S₂(t)/n` is integrable on `(0, ∞)`.
-/

public section

open Finset MeasureTheory Real

namespace CycleCutoff

variable {n : ℕ} [NeZero n]

/-- The cubic sum `S₃` is continuous in time. -/
theorem continuous_S3 : Continuous (S3 n) := by
  have h : ∀ x : ZMod n, Continuous fun t => heatKernel n t 0 x := fun x =>
    continuous_iff_continuousAt.2 fun t =>
      (hasDerivAt_semigroup_apply (Delta n) t 0 x).continuousAt
  exact continuous_finsetSum _ fun x _ => (h x).pow 3

/-- **Integrability of the integrand of `B_n`**: for `n ≥ 3`, `t ↦ S₃(t) - S₂(t)/n` is
integrable on `(0, ∞)`. -/
@[cycle_cutoff "lem_B_integrable"]
theorem integrableOn_S3_sub_S2_div (hn : 3 ≤ n) :
    IntegrableOn (fun t => S3 n t - S2 n t / n) (Set.Ioi 0) := by
  obtain ⟨K, -, hK⟩ := exists_S3_sub_S2_div_le
  have hlam : 0 < lambdaN n :=
    lt_of_lt_of_le (by positivity) (sixteen_div_sq_le_lambdaN (by omega))
  have hcont : Continuous fun t => S3 n t - S2 n t / n :=
    continuous_S3.sub (continuous_S2.div_const _)
  rw [← Set.Ioc_union_Ioi_eq_Ioi (sq_nonneg (n : ℝ))]
  refine IntegrableOn.union ?_ ?_
  · exact (hcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  · have hexp : IntegrableOn (fun t => K / (n : ℝ) ^ 2 * Real.exp (-(2 * lambdaN n) * t))
        (Set.Ioi ((n : ℝ) ^ 2)) :=
      (exp_neg_integrableOn_Ioi _ (by positivity)).const_mul _
    refine Integrable.mono' hexp hcont.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t (ht : (n : ℝ) ^ 2 < t) => ?_
    have h0 : 0 ≤ S3 n t - S2 n t / n := S2_div_le_S3 ((sq_nonneg _).trans ht.le)
    rw [Real.norm_of_nonneg h0, div_mul_eq_mul_div, mul_comm,
      show -(2 * lambdaN n) * t = -2 * lambdaN n * t by ring, mul_comm]
    exact hK n hn t ht.le

end CycleCutoff
