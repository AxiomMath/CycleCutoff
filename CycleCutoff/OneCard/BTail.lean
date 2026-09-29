/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.OneCard.Defs
public import CycleCutoff.Cycle.LambdaLower
public import CycleCutoff.OneCard.HeatDeviation
public import CycleCutoff.OneCard.BIntegrandNonneg

/-!
# The tail of the integrand of `B_n`

There is an absolute constant `K > 0` such that for all `n ≥ 3` and `t ≥ n²`,
`S₃(t) - S₂(t)/n ≤ K e^{-2λ_n t} / n²`.

## Main results

* `CycleCutoff.exists_S3_sub_S2_div_le`: the tail bound.
-/

public section

open Finset Real

namespace CycleCutoff

/-- **Tail of the integrand of `B_n`**: for `n ≥ 3` and `t ≥ n²`,
`S₃(t) - S₂(t)/n ≤ K e^{-2λ_n t} / n²` for an absolute constant `K > 0`. -/
@[cycle_cutoff "lem_B_tail"]
theorem exists_S3_sub_S2_div_le :
    ∃ K > (0 : ℝ), ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ t : ℝ, (n : ℝ) ^ 2 ≤ t →
      S3 n t - S2 n t / n ≤ K * Real.exp (-2 * lambdaN n * t) / (n : ℝ) ^ 2 := by
  obtain ⟨c, hc, hdev⟩ := exists_abs_mul_heatKernel_sub_one_le
  refine ⟨(2 + c) * c ^ 2, by positivity, fun n _ hn t ht => ?_⟩
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hlow := sixteen_div_sq_le_lambdaN (by omega : 2 ≤ n)
  have hlpos : 0 < lambdaN n := lt_of_lt_of_le (by positivity) hlow
  have h16 : 16 ≤ lambdaN n * (n : ℝ) ^ 2 := by
    rwa [div_le_iff₀ (by positivity)] at hlow
  have hlt : lambdaN n * (n : ℝ) ^ 2 ≤ lambdaN n * t := mul_le_mul_of_nonneg_left ht hlpos.le
  have ht' : a0 / lambdaN n ≤ t := by
    rw [div_le_iff₀ hlpos, show a0 = 5 from rfl]
    linarith
  set E := Real.exp (-lambdaN n * t) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hE2 : Real.exp (-2 * lambdaN n * t) = E ^ 2 := by
    rw [hE, ← Real.exp_nat_mul]
    ring_nf
  set p := heatKernel n t 0 with hp
  have hsum : ∑ x, p x = 1 := sum_heatKernel t 0
  have hpt : ∀ x, p x ^ 3 - p x ^ 2 / n ≤
      ((n * p x - 1) + (2 + c) * c ^ 2 * E ^ 2) / (n : ℝ) ^ 3 := by
    intro x
    set r := (n : ℝ) * p x - 1 with hr
    have hpx : p x = (1 + r) / n := by
      rw [hr]
      field_simp
      ring
    have hb : |r| ≤ c * E := hdev n hn t ht' x
    have hr2 : r ^ 2 ≤ (c * E) ^ 2 := sq_le_sq' (abs_le.1 hb).1 (abs_le.1 hb).2
    have hr3 : r ^ 3 ≤ c * r ^ 2 := by
      have hrc : r ≤ c := by linarith [(abs_le.1 hb).2, mul_le_of_le_one_right hc.le hE1]
      nlinarith [sq_nonneg r]
    have hkey : 2 * r ^ 2 + r ^ 3 ≤ (2 + c) * c ^ 2 * E ^ 2 := by
      nlinarith
    have hexp : p x ^ 3 - p x ^ 2 / n = (r + (2 * r ^ 2 + r ^ 3)) / (n : ℝ) ^ 3 := by
      rw [hpx]
      field_simp
      ring
    rw [hexp]
    gcongr
  calc S3 n t - S2 n t / n = ∑ x, (p x ^ 3 - p x ^ 2 / n) := by
        simp only [S3, S2, sum_sub_distrib, sum_div, hp]
    _ ≤ ∑ x, ((n * p x - 1) + (2 + c) * c ^ 2 * E ^ 2) / (n : ℝ) ^ 3 :=
        sum_le_sum fun x _ => hpt x
    _ = (n * ∑ x, p x - n + n * ((2 + c) * c ^ 2 * E ^ 2)) / (n : ℝ) ^ 3 := by
        rw [← sum_div, sum_add_distrib, sum_sub_distrib, ← mul_sum]
        simp
    _ = (2 + c) * c ^ 2 * Real.exp (-2 * lambdaN n * t) / (n : ℝ) ^ 2 := by
        rw [hsum, hE2]
        field_simp
        ring

end CycleCutoff
