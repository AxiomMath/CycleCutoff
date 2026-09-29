/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.OneCard.Defs
public import CycleCutoff.OneCard.BIntegrable
public import CycleCutoff.OneCard.BIntegrandNonneg
public import CycleCutoff.OneCard.HeatSup
public import CycleCutoff.OneCard.BTail
public import CycleCutoff.Cycle.LambdaLower
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# The bound `B_n = O(log n)`

There is an absolute constant `c > 0` such that `B_n ≤ c (1 + log n)` for all `n ≥ 3`, where
`B_n = ∫_{(0, ∞)} (S₃(t) - S₂(t)/n) dt`.

## Main results

* `CycleCutoff.S3_le_sq`: if `p_t(0, x) ≤ M` for all `x`, then `S₃(t) ≤ M²` (`t ≥ 0`).
* `CycleCutoff.exists_Bn_le`: `B_n ≤ c (1 + log n)` for `n ≥ 3`.
-/

public section

open Finset MeasureTheory Real

namespace CycleCutoff

variable {n : ℕ} [NeZero n]

/-- For `t ≥ 0`, if every entry of the row `p_t(0, ·)` is at most `M`, then `S₃(t) ≤ M²`. -/
theorem S3_le_sq {t : ℝ} (ht : 0 ≤ t) {M : ℝ} (hM : ∀ x, heatKernel n t 0 x ≤ M) :
    S3 n t ≤ M ^ 2 := by
  calc S3 n t = ∑ x : ZMod n, heatKernel n t 0 x * heatKernel n t 0 x ^ 2 := by
        simp only [S3]; congr 1; ext x; ring
    _ ≤ ∑ x : ZMod n, heatKernel n t 0 x * M ^ 2 := by
        refine sum_le_sum fun x _ => ?_
        have h0 := heatKernel_nonneg (n := n) ht 0 x
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (hM x) 2) h0
    _ = M ^ 2 := by rw [← sum_mul, sum_heatKernel, one_mul]

/-- **`B_n = O(log n)`**: there is an absolute constant `c > 0` with `B_n ≤ c (1 + log n)`
for all `n ≥ 3`. -/
@[cycle_cutoff "lem_B_bound"]
theorem exists_Bn_le :
    ∃ c > (0 : ℝ), ∀ (n : ℕ) [NeZero n], 3 ≤ n → Bn n ≤ c * (1 + Real.log n) := by
  obtain ⟨c, hc, hsup⟩ := exists_heatKernel_le
  obtain ⟨K, hK, htail⟩ := exists_S3_sub_S2_div_le
  refine ⟨4 * c ^ 2 + K / 32, by positivity, fun n _ hn => ?_⟩
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_neZero n)
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  set N : ℝ := (n : ℝ) ^ 2 with hN
  have hNpos : 0 < N := by positivity
  have hint := integrableOn_S3_sub_S2_div hn
  have hlam16 := sixteen_div_sq_le_lambdaN (n := n) (by omega)
  have hlpos : 0 < lambdaN n := lt_of_lt_of_le (by positivity) hlam16
  have h16 : 16 ≤ lambdaN n * N := by
    rw [div_le_iff₀ hNpos] at hlam16; linarith
  have hsplit : Bn n = (∫ t in Set.Ioc 0 N, (S3 n t - S2 n t / n)) +
      ∫ t in Set.Ioi N, (S3 n t - S2 n t / n) := by
    rw [Bn, ← Set.Ioc_union_Ioi_eq_Ioi hNpos.le]
    exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Set.Ioc_subset_Ioi_self) (hint.mono_set (Set.Ioi_subset_Ioi hNpos.le))
  have hhead : (∫ t in Set.Ioc 0 N, (S3 n t - S2 n t / n)) ≤
      2 * c ^ 2 * Real.log (1 + N) + 2 * c ^ 2 := by
    have hmaj : IntegrableOn (fun t : ℝ => 2 * c ^ 2 * (1 + t)⁻¹ + 2 * c ^ 2 / N)
        (Set.Ioc 0 N) := by
      refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
      refine ContinuousOn.add (continuousOn_const.mul ?_) continuousOn_const
      exact ContinuousOn.inv₀ (by fun_prop) fun t ht => by
        simp only [Set.mem_Icc] at ht; linarith [ht.1]
    calc (∫ t in Set.Ioc 0 N, (S3 n t - S2 n t / n))
        ≤ ∫ t in Set.Ioc 0 N, (2 * c ^ 2 * (1 + t)⁻¹ + 2 * c ^ 2 / N) := by
          refine setIntegral_mono_on (hint.mono_set Set.Ioc_subset_Ioi_self) hmaj
            measurableSet_Ioc fun t ht => ?_
          have ht0 : 0 ≤ t := ht.1.le
          have hS2 : 0 ≤ S2 n t / n :=
            div_nonneg (sum_nonneg fun x _ => sq_nonneg _) hn0.le
          have hS3 := S3_le_sq ht0 (hsup n hn t ht0)
          have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + t by linarith)
          have ha : (c / √(1 + t)) ^ 2 = c ^ 2 * (1 + t)⁻¹ := by
            rw [div_pow, hs, div_eq_mul_inv]
          have hb : (c / (n : ℝ)) ^ 2 = c ^ 2 / N := by rw [div_pow]
          have hab : (c / √(1 + t) + c / n) ^ 2 ≤
              2 * (c / √(1 + t)) ^ 2 + 2 * (c / (n : ℝ)) ^ 2 := by
            nlinarith [sq_nonneg (c / √(1 + t) - c / n)]
          rw [ha, hb] at hab
          calc S3 n t - S2 n t / n ≤ S3 n t := by linarith
            _ ≤ _ := hS3.trans hab
            _ = _ := by ring
      _ = 2 * c ^ 2 * Real.log (1 + N) + 2 * c ^ 2 := by
          rw [← intervalIntegral.integral_of_le hNpos.le, intervalIntegral.integral_add,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
            intervalIntegral.integral_comp_add_left (fun x => x⁻¹),
            integral_inv_of_pos (by norm_num) (by linarith)]
          · simp only [add_zero, div_one, sub_zero, smul_eq_mul]
            field_simp
          · refine (continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop)
              fun t ht => ?_)).intervalIntegrable
            rw [Set.uIcc_of_le hNpos.le] at ht
            linarith [ht.1]
          · exact intervalIntegrable_const
  have htl : ∫ t in Set.Ioi N, (S3 n t - S2 n t / n) ≤ K / 32 := by
    have hexp : IntegrableOn (fun t => K / N * Real.exp (-(2 * lambdaN n) * t))
        (Set.Ioi N) := (exp_neg_integrableOn_Ioi _ (by positivity)).const_mul _
    calc ∫ t in Set.Ioi N, (S3 n t - S2 n t / n)
        ≤ ∫ t in Set.Ioi N, K / N * Real.exp (-(2 * lambdaN n) * t) := by
          refine setIntegral_mono_on (hint.mono_set (Set.Ioi_subset_Ioi hNpos.le)) hexp
            measurableSet_Ioi fun t ht => ?_
          rw [show -(2 * lambdaN n) * t = -2 * lambdaN n * t by ring]
          exact (htail n hn t ht.le).trans_eq (by ring)
      _ = K * Real.exp (-(2 * lambdaN n) * N) / (2 * (lambdaN n * N)) := by
          rw [integral_const_mul, integral_exp_mul_Ioi (by linarith)]
          field_simp
      _ ≤ K * 1 / 32 := by
          refine div_le_div₀ (by positivity) ?_ (by norm_num) (by linarith)
          exact mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (by nlinarith)) hK.le
      _ = K / 32 := by ring
  have hlog : Real.log (1 + N) ≤ 1 + 2 * Real.log n := by
    have h1 : Real.log (1 + N) ≤ Real.log (2 * N) :=
      Real.log_le_log (by positivity) (by nlinarith)
    have h2 : Real.log (2 * N) = Real.log 2 + 2 * Real.log n := by
      rw [Real.log_mul (by norm_num) hNpos.ne', hN, Real.log_pow]; push_cast; ring
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    linarith
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  rw [hsplit]
  nlinarith [sq_nonneg c]

end CycleCutoff
