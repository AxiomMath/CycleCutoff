/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.OneCard.Defs
public import CycleCutoff.Generator.SemigroupSymmetric
public import CycleCutoff.OneCard.DeltaInvolution
public import CycleCutoff.OneCard.HeatFourier
public import CycleCutoff.OneCard.HeatDeviation
public import CycleCutoff.OneCard.EigenvalueRatio
public import CycleCutoff.Cycle.LambdaLower
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The collision sum decays at twice the spectral gap

There is an absolute constant `c₁₀ > 0` such that for all `n ≥ 3` and `t ≥ a₀/λ_n`,
`n S₂(t) - 1 ≤ c₁₀ e^{-2λ_n t}`; one may take `c₁₀ = 4`.

## Main results

* `CycleCutoff.S2_eq_heatKernel_two_mul`: `S₂(t) = p_{2t}(0, 0)`.
* `CycleCutoff.exists_mul_S2_sub_one_le`: `n S₂(t) - 1 ≤ c₁₀ e^{-2λ_n t}` for `t ≥ a₀/λ_n`.
-/

public section

open Finset Real

namespace CycleCutoff

variable {n : ℕ} [NeZero n]

/-- The heat kernel is symmetric: `p_t(x, y) = p_t(y, x)`. -/
private lemma heatKernel_comm (t : ℝ) (x y : ZMod n) :
    heatKernel n t x y = heatKernel n t y x := by
  simp only [heatKernel_def, Delta_eq_rateMatrix]
  exact ((oneCardFamily n).isSymm_rateMatrix.semigroup t).apply y x

/-- The collision sum is the return probability at twice the time: `S₂(t) = p_{2t}(0, 0)`. -/
theorem S2_eq_heatKernel_two_mul (t : ℝ) : S2 n t = heatKernel n (2 * t) 0 0 := by
  rw [S2, two_mul, heatKernel_def, semigroup_add, Matrix.mul_apply]
  refine sum_congr rfl fun x _ => ?_
  rw [sq]
  congr 1
  exact heatKernel_comm t 0 x

/-- The Fourier expansion of the collision sum: `n S₂(t) = ∑_{j<n} e^{-2λ_{n,j} t}`. -/
private lemma mul_S2_eq (t : ℝ) :
    (n : ℝ) * S2 n t = ∑ j ∈ range n, Real.exp (-2 * lambdaNJ n j * t) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have h := heatKernel_zero_intCast_eq (n := n) (2 * t) 0
  rw [Int.cast_zero] at h
  rw [S2_eq_heatKernel_two_mul, h, ← mul_assoc, mul_one_div_cancel hn, one_mul]
  refine sum_congr rfl fun j _ => ?_
  simp only [Int.cast_zero, mul_zero, zero_div, Real.cos_zero, mul_one]
  ring_nf

omit [NeZero n] in
/-- The per-mode bound: if `λ_n t ≥ 5`, then for `1 ≤ j ≤ n - 1`,
`e^{-2λ_{n,j} t} ≤ e^{-2λ_n t} e^{1 - min(j, n - j)}`. -/
private lemma exp_neg_two_lambdaNJ_le {j : ℕ} (hj₁ : 1 ≤ j) (hj₂ : j ≤ n - 1) {t : ℝ}
    (hL : 5 ≤ lambdaN n * t) :
    Real.exp (-2 * lambdaNJ n j * t) ≤
      Real.exp (-2 * lambdaN n * t) * Real.exp (1 - ((min j (n - j) : ℕ) : ℝ)) := by
  have h := exp_neg_lambdaNJ_mul_le (t := 2 * t) hj₁ hj₂
    (by rw [show a0 = 5 from rfl]; nlinarith)
  calc Real.exp (-2 * lambdaNJ n j * t) = Real.exp (-lambdaNJ n j * (2 * t)) := by ring_nf
    _ ≤ _ := h
    _ = _ := by
      rw [mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
      ring_nf

/-- `e^{1 - min(j, n - j)}` is at most `e^{-(j-1)} + e^{-(n-1-j)}`, written for `j + 1`,
`n = N + 1` as `r^j + r^{N-1-j}` with `r = e^{-1}`. -/
private lemma exp_one_sub_min_le (N j : ℕ) (hj : j < N) :
    Real.exp (1 - ((min (j + 1) (N + 1 - (j + 1)) : ℕ) : ℝ)) ≤
      Real.exp (-1) ^ j + Real.exp (-1) ^ (N - 1 - j) := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  have h1 : 0 ≤ Real.exp ((j : ℝ) * -1) := (Real.exp_pos _).le
  have h2 : 0 ≤ Real.exp (((N - 1 - j : ℕ) : ℝ) * -1) := (Real.exp_pos _).le
  rcases min_choice (j + 1) (N + 1 - (j + 1)) with h | h
  · rw [h]
    have : Real.exp (1 - ((j + 1 : ℕ) : ℝ)) = Real.exp ((j : ℝ) * -1) := by
      congr 1; push_cast; ring
    linarith
  · rw [h]
    have : Real.exp (1 - ((N + 1 - (j + 1) : ℕ) : ℝ)) = Real.exp (((N - 1 - j : ℕ) : ℝ) * -1) := by
      congr 1
      rw [show N + 1 - (j + 1) = (N - 1 - j) + 1 by omega]
      push_cast; ring
    linarith

/-- **The collision sum bound**: there is an absolute constant `c₁₀ > 0` such that for all
`n ≥ 3` and `t ≥ a₀/λ_n`, `n S₂(t) - 1 ≤ c₁₀ e^{-2λ_n t}`. -/
@[cycle_cutoff "lem_S2_bound"]
theorem exists_mul_S2_sub_one_le :
    ∃ c₁₀ > (0 : ℝ), ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ t : ℝ, a0 / lambdaN n ≤ t →
      (n : ℝ) * S2 n t - 1 ≤ c₁₀ * Real.exp (-2 * lambdaN n * t) := by
  refine ⟨4, by norm_num, fun n _ hn t ht => ?_⟩
  have hlam : 0 < lambdaN n := lt_of_lt_of_le (by positivity) (sixteen_div_sq_le_lambdaN (by omega))
  have ha0 : a0 = 5 := rfl
  have hL : 5 ≤ lambdaN n * t := by
    rw [ha0, div_le_iff₀ hlam] at ht; linarith
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  set r := Real.exp (-1) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by rw [hr, ← Real.exp_zero, Real.exp_lt_exp]; norm_num
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [mul_S2_eq, sum_range_succ', show lambdaNJ (N + 1) 0 = 0 by simp [lambdaNJ],
    mul_zero, zero_mul, Real.exp_zero, add_sub_cancel_right]
  set E := Real.exp (-2 * lambdaN (N + 1) * t) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hterm : ∀ j ∈ range N, Real.exp (-2 * lambdaNJ (N + 1) (j + 1) * t) ≤
      E * (r ^ j + r ^ (N - 1 - j)) := by
    intro j hj
    rw [mem_range] at hj
    refine (exp_neg_two_lambdaNJ_le (n := N + 1) (by omega) (by omega) hL).trans ?_
    exact mul_le_mul_of_nonneg_left (exp_one_sub_min_le N j hj) hE0
  have hgeom : ∑ j ∈ range N, r ^ j ≤ 1 / (1 - r) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := N) hr0 hr1
    rwa [pow_zero, ← Finset.range_eq_Ico] at this
  have hrefl : ∑ j ∈ range N, r ^ (N - 1 - j) = ∑ j ∈ range N, r ^ j :=
    sum_range_reflect (fun j => r ^ j) N
  have hr' : r * Real.exp 1 = 1 := by rw [hr, ← Real.exp_add]; norm_num
  have h2 : 2 * (1 / (1 - r)) ≤ 4 := by
    rw [mul_one_div, div_le_iff₀ (by linarith)]
    nlinarith
  calc ∑ j ∈ range N, Real.exp (-2 * lambdaNJ (N + 1) (j + 1) * t)
      ≤ ∑ j ∈ range N, E * (r ^ j + r ^ (N - 1 - j)) := sum_le_sum hterm
    _ = E * (2 * ∑ j ∈ range N, r ^ j) := by
        rw [← mul_sum, sum_add_distrib, hrefl, two_mul]
    _ ≤ E * (2 * (1 / (1 - r))) := by gcongr
    _ ≤ 4 * E := by
        rw [mul_comm]; gcongr

end CycleCutoff
