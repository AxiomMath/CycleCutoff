/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.OneCard.Defs
public import CycleCutoff.OneCard.HeatFourier
public import CycleCutoff.OneCard.EigenvalueLower
public import CycleCutoff.OneCard.BIntegrandNonneg
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SumIntegralComparisons

/-!
# A uniform bound on the heat kernel

There is an absolute constant `c₁₁ > 0` such that for all `n ≥ 3`, `t ≥ 0` and `x`,
`p_t(0, x) ≤ c₁₁ / √(1 + t) + c₁₁ / n`; one may take `c₁₁ = 2`.

## Main results

* `CycleCutoff.sum_exp_neg_mul_sq_le`: `∑_{r=1}^{m} e^{-c r²} ≤ √(π / c) / 2` for `c > 0`.
* `CycleCutoff.heatKernel_zero_le_of_pos`: `p_t(0, x) ≤ 1/n + √π / (4 √t)` for `t > 0`.
* `CycleCutoff.exists_heatKernel_le`: the uniform bound with `c₁₁ = 2`.
-/

public section

open Finset Real MeasureTheory

namespace CycleCutoff

/-- Comparison of a Gaussian sum with the half-line Gaussian integral:
`∑_{r=1}^{m} e^{-c r²} ≤ √(π / c) / 2` for `c > 0`. -/
theorem sum_exp_neg_mul_sq_le {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∑ r ∈ range m, Real.exp (-c * ((r + 1 : ℕ) : ℝ) ^ 2) ≤ √(π / c) / 2 := by
  have hanti : AntitoneOn (fun u : ℝ => Real.exp (-c * u ^ 2)) (Set.Icc 0 (0 + m)) := by
    intro a ha b _ hab
    simp only
    apply Real.exp_le_exp.2
    have : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.1 hab 2
    nlinarith
  have h := hanti.sum_le_integral
  simp only [zero_add] at h
  refine h.trans ?_
  rw [intervalIntegral.integral_of_le (Nat.cast_nonneg m), ← integral_gaussian_Ioi c]
  exact setIntegral_mono_set (integrable_exp_neg_mul_sq hc).integrableOn
    (ae_of_all _ fun x => (Real.exp_pos _).le) Set.Ioc_subset_Ioi_self.eventuallyLE

variable {n : ℕ} [NeZero n]

/-- For `t > 0`, `p_t(0, x) ≤ 1/n + √π / (4 √t)`. -/
theorem heatKernel_zero_le_of_pos {t : ℝ} (ht : 0 < t) (x : ZMod n) :
    heatKernel n t 0 x ≤ 1 / n + √π / (4 * √t) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_neZero n)
  have hx : x = (((x.val : ℕ) : ℤ) : ZMod n) := by simp
  rw [hx, heatKernel_zero_intCast_eq]
  set c : ℝ := 16 * t / (n : ℝ) ^ 2 with hc_def
  have hc : 0 < c := by positivity
  set g : ℕ → ℝ := fun r => Real.exp (-c * ((r + 1 : ℕ) : ℝ) ^ 2) with hg
  set S : ℝ := √(π / c) / 2 with hS
  have hterm : ∀ j ∈ range n, Real.exp (-lambdaNJ n j * t) *
      Real.cos (2 * π * j * ((x.val : ℕ) : ℤ) / n) ≤
      Real.exp (-c * (j : ℝ) ^ 2) + Real.exp (-c * ((n - j : ℕ) : ℝ) ^ 2) := by
    intro j hj
    have hj' := mem_range.1 hj
    have hl := sixteen_mul_sq_div_sq_le_lambdaNJ hj'
    calc _ ≤ Real.exp (-lambdaNJ n j * t) :=
          mul_le_of_le_one_right (Real.exp_pos _).le (Real.cos_le_one _)
      _ ≤ Real.exp (-c * ((min j (n - j) : ℕ) : ℝ) ^ 2) := by
          apply Real.exp_le_exp.2
          have := mul_le_mul_of_nonneg_right hl ht.le
          have heq : c * ((min j (n - j) : ℕ) : ℝ) ^ 2 =
              16 * ((min j (n - j) : ℕ) : ℝ) ^ 2 / (n : ℝ) ^ 2 * t := by
            rw [hc_def]; ring
          nlinarith
      _ ≤ _ := by
          rcases min_choice j (n - j) with h | h <;> rw [h] <;>
            linarith [Real.exp_pos (-c * (j : ℝ) ^ 2),
              Real.exp_pos (-c * ((n - j : ℕ) : ℝ) ^ 2)]
  have hsum1 : ∑ j ∈ range n, Real.exp (-c * (j : ℝ) ^ 2) = ∑ i ∈ range (n - 1), g i + 1 := by
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := NeZero.ne n; omega⟩
    rw [hk, sum_range_succ', Nat.add_sub_cancel]
    simp [hg]
  have hsum2 : ∑ j ∈ range n, Real.exp (-c * ((n - j : ℕ) : ℝ) ^ 2) = ∑ i ∈ range n, g i := by
    rw [← sum_range_reflect g n]
    refine sum_congr rfl fun j hj => ?_
    have hj' := mem_range.1 hj
    simp only [hg]
    congr 4
    omega
  have hg1 : ∑ i ∈ range (n - 1), g i ≤ S := sum_exp_neg_mul_sq_le hc _
  have hg2 : ∑ i ∈ range n, g i ≤ S := sum_exp_neg_mul_sq_le hc _
  have htot := sum_le_sum hterm
  rw [sum_add_distrib, hsum1, hsum2] at htot
  have hSval : S = n * √π / (8 * √t) := by
    have hst : 0 < √t := Real.sqrt_pos.2 ht
    have hpc : π / c = (n * √π / (4 * √t)) ^ 2 := by
      rw [hc_def, div_pow, mul_pow, mul_pow, Real.sq_sqrt pi_pos.le, Real.sq_sqrt ht.le]
      field_simp
      ring
    rw [hS, hpc, Real.sqrt_sq (by positivity)]
    field_simp
    ring
  calc 1 / (n : ℝ) * ∑ j ∈ range n, Real.exp (-lambdaNJ n j * t) *
        Real.cos (2 * π * j * ((x.val : ℕ) : ℤ) / n)
      ≤ 1 / (n : ℝ) * (1 + 2 * S) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = 1 / n + √π / (4 * √t) := by
        rw [hSval]
        have hst : 0 < √t := Real.sqrt_pos.2 ht
        field_simp
        ring

/-- **Uniform bound on the heat kernel**: `p_t(0, x) ≤ c₁₁ / √(1 + t) + c₁₁ / n` for all
`n ≥ 3`, `t ≥ 0` and `x`, with the absolute constant `c₁₁ = 2`. -/
@[cycle_cutoff "lem_heat_sup"]
theorem exists_heatKernel_le :
    ∃ c₁₁ > (0 : ℝ), ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ t : ℝ, 0 ≤ t → ∀ x : ZMod n,
      heatKernel n t 0 x ≤ c₁₁ / Real.sqrt (1 + t) + c₁₁ / n := by
  refine ⟨2, two_pos, fun n _ _ t ht x => ?_⟩
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_neZero n)
  have hs : 0 < √(1 + t) := Real.sqrt_pos.2 (by linarith)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + t by linarith)
  have h2n : 0 ≤ 2 / (n : ℝ) := by positivity
  rcases le_or_gt t 1 with h | h
  · have hp : heatKernel n t 0 x ≤ 1 := by
      have := single_le_sum (fun y _ => heatKernel_nonneg ht 0 y) (mem_univ x)
      rwa [sum_heatKernel] at this
    have h1 : 1 ≤ 2 / √(1 + t) := by
      rw [le_div_iff₀ hs]
      nlinarith
    linarith
  · have hp := heatKernel_zero_le_of_pos (by linarith : 0 < t) x
    have hst : 0 < √t := Real.sqrt_pos.2 (by linarith)
    have hπ : √π ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      linarith [pi_le_four]
    have hb : √(1 + t) ≤ 2 * √t := by
      rw [show 2 * √t = √(4 * t) by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    have h1 : √π / (4 * √t) ≤ 2 / √(1 + t) := by
      rw [div_le_div_iff₀ (by positivity) hs]
      nlinarith [Real.sqrt_nonneg π, Real.sqrt_nonneg (1 + t)]
    have h3 : 1 / (n : ℝ) ≤ 2 / n := div_le_div_of_nonneg_right (by norm_num) hn.le
    linarith

end CycleCutoff
