/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.FiniteProbability.PsiPointwise
public import CycleCutoff.FiniteProbability.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Entropy of a square is bounded by the variance

Let `ν` be a probability vector on a finite type `Ω` whose weights are all at least
`ν_* > 0`. For every `f : Ω → ℝ`,
`Ent_ν(f²) ≤ 6 (1 + log(1/ν_*)) Var_ν(f)`.

Writing `E = 𝔼_ν[f²]`, `s = √E` and `t = |f(z)| / s`, the pointwise bound
`t² log t² - t² + 1 ≤ 3 (t - 1)² (1 + max(0, log t²))` together with
`ν(z) f(z)² ≤ E`, which gives `log t² ≤ log(1/ν_*)`, yields after multiplication by `E` and
averaging `Ent_ν(f²) ≤ 3 (1 + log(1/ν_*)) 𝔼_ν[(|f| - s)²] = 6 (1 + log(1/ν_*)) (E - s 𝔼_ν|f|)`.
Finally `(𝔼_ν f)² ≤ (𝔼_ν|f|)² ≤ s 𝔼_ν|f|`, so `E - s 𝔼_ν|f| ≤ Var_ν(f)`.

## Main results

* `CycleCutoff.ent_sq_le_variance`: `Ent_ν(f²) ≤ 6 (1 + log(1/ν_*)) Var_ν(f)`.
-/

public section

open Finset

namespace CycleCutoff

variable {Ω : Type*} [Fintype Ω]

/-- **Entropy of a square is bounded by the variance.** If every weight of the probability
vector `ν` is at least `ν_* > 0`, then `Ent_ν(f²) ≤ 6 (1 + log(1/ν_*)) Var_ν(f)`. -/
@[cycle_cutoff "lem_ent_var_bound"]
theorem ent_sq_le_variance (ν : Ω → ℝ) (hν : IsProbVec ν) (νs : ℝ)
    (hνs : 0 < νs) (hmin : ∀ z, νs ≤ ν z) (f : Ω → ℝ) :
    ent ν (fun z => f z ^ 2) ≤ 6 * (1 + Real.log (1 / νs)) * variance ν f := by
  obtain ⟨z₀⟩ : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hν.sum_eq_one
    simp at this
  have hν1 : ∀ z, ν z ≤ 1 := fun z => by
    rw [← hν.sum_eq_one]
    exact single_le_sum (fun w _ => hν.nonneg w) (mem_univ z)
  set L := Real.log (1 / νs) with hLdef
  have hL : 0 ≤ L := Real.log_nonneg (one_le_one_div hνs ((hmin z₀).trans (hν1 z₀)))
  set E := expectation ν (fun z => f z ^ 2) with hEdef
  set m := expectation ν (fun z => |f z|) with hmdef
  set e := expectation ν f with hedef
  have hvar := variance_eq_of_isProbVec hν f
  have hvar0 : 0 ≤ variance ν f :=
    expectation_nonneg hν.nonneg fun z => sq_nonneg _
  have hE0 : 0 ≤ E := expectation_nonneg hν.nonneg fun z => sq_nonneg _
  have hm0 : 0 ≤ m := expectation_nonneg hν.nonneg fun z => abs_nonneg _
  have hem : |e| ≤ m := by
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    exact sum_congr rfl fun z _ => by rw [abs_mul, abs_of_nonneg (hν.nonneg z)]
  have hmE : m ^ 2 ≤ E := by
    have h := variance_eq_of_isProbVec hν (fun z => |f z|)
    simp only [sq_abs] at h
    have : 0 ≤ variance ν (fun z => |f z|) :=
      expectation_nonneg hν.nonneg fun z => sq_nonneg _
    linarith
  have hpt : ∀ z, ν z * f z ^ 2 ≤ E := fun z =>
    single_le_sum (f := fun w => ν w * f w ^ 2)
      (fun w _ => mul_nonneg (hν.nonneg w) (sq_nonneg _)) (mem_univ z)
  rcases hE0.eq_or_lt with hE | hE
  · have hf : ∀ z, f z = 0 := fun z => by
      have h1 := hpt z
      rw [← hE] at h1
      have h2 : 0 < ν z := hνs.trans_le (hmin z)
      have : f z ^ 2 ≤ 0 := by nlinarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg _))
    have : ent ν (fun z => f z ^ 2) = 0 := by
      simp [ent, expectation, hf]
    rw [this]
    positivity
  set s := Real.sqrt E with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.2 hE
  have hss : s ^ 2 = E := Real.sq_sqrt hE0
  have hms : m ≤ s := Real.le_sqrt_of_sq_le hmE
  have key : ∀ z, f z ^ 2 * Real.log (f z ^ 2) - f z ^ 2 * Real.log E - f z ^ 2 + E ≤
      3 * (1 + L) * (|f z| - s) ^ 2 := fun z => by
    set t := |f z| / s with htdef
    have ht0 : 0 ≤ t := div_nonneg (abs_nonneg _) hs0.le
    have ht2 : t ^ 2 = f z ^ 2 / E := by rw [htdef, div_pow, sq_abs, hss]
    have hlogt : Real.log (t ^ 2) ≤ L := by
      rcases (sq_nonneg t).eq_or_lt with h0 | h0
      · rw [← h0, Real.log_zero]; exact hL
      · refine Real.log_le_log h0 ?_
        rw [ht2, div_le_div_iff₀ hE hνs, one_mul]
        calc f z ^ 2 * νs ≤ ν z * f z ^ 2 := by
              rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hmin z) (sq_nonneg _)
          _ ≤ E := hpt z
    have hψ := sq_mul_log_sq_sub_sq_add_one_le t ht0
    have hmax : max 0 (Real.log (t ^ 2)) ≤ L := max_le hL hlogt
    have hψ' : t ^ 2 * Real.log (t ^ 2) - t ^ 2 + 1 ≤ 3 * (t - 1) ^ 2 * (1 + L) :=
      hψ.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    have hmul := mul_le_mul_of_nonneg_left hψ' hE0
    have hlog : f z ^ 2 * Real.log (t ^ 2) = f z ^ 2 * Real.log (f z ^ 2) -
        f z ^ 2 * Real.log E := by
      rcases eq_or_ne (f z) 0 with h | h
      · simp [h]
      · rw [ht2, Real.log_div (by positivity) hE.ne']
        ring
    have h1 : E * (t ^ 2 * Real.log (t ^ 2) - t ^ 2 + 1) =
        f z ^ 2 * Real.log (f z ^ 2) - f z ^ 2 * Real.log E - f z ^ 2 + E := by
      rw [← hlog, ht2]
      field_simp
    have h2 : E * (3 * (t - 1) ^ 2 * (1 + L)) = 3 * (1 + L) * (|f z| - s) ^ 2 := by
      rw [htdef, ← hss]
      field_simp
    rw [← h1, ← h2]
    exact hmul
  have hsum := expectation_mono hν.nonneg key
  have hlhs : expectation ν (fun z => f z ^ 2 * Real.log (f z ^ 2) - f z ^ 2 * Real.log E -
      f z ^ 2 + E) = ent ν (fun z => f z ^ 2) := by
    rw [expectation_add, expectation_sub, expectation_sub, expectation_mul_const,
      hν.expectation_const, ent]
    ring
  have hrhs : expectation ν (fun z => 3 * (1 + L) * (|f z| - s) ^ 2) =
      3 * (1 + L) * (2 * E - 2 * s * m) := by
    have h : (fun z => 3 * (1 + L) * (|f z| - s) ^ 2) =
        fun z => 3 * (1 + L) * (f z ^ 2 - (2 * s) * |f z| + s ^ 2) := by
      funext z; rw [← sq_abs (f z)]; ring
    rw [h, expectation_const_mul, expectation_add, expectation_sub, expectation_const_mul,
      hν.expectation_const, hss]
    ring
  rw [hlhs, hrhs] at hsum
  have he2 : e ^ 2 ≤ s * m := by
    have : e ^ 2 ≤ m ^ 2 := by
      rw [← sq_abs e]; exact pow_le_pow_left₀ (abs_nonneg _) hem 2
    nlinarith
  rw [hvar]
  nlinarith

end CycleCutoff
