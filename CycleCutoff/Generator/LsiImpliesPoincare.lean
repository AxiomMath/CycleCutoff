/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.DirichletFormula
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# A log-Sobolev inequality implies a Poincaré inequality

Let `𝒯` be an involution family on a finite set `Ω` and suppose that `Ent_{u_Ω}(f²) ≤ A 𝒟_𝒯(f)` for
every `f : Ω → ℝ`. Then `Var_{u_Ω}(h) ≤ (A / 2) 𝒟_𝒯(h)` for every `h : Ω → ℝ`.

## Main results

* `CycleCutoff.InvFamily.variance_le_of_lsi`: the Poincaré inequality with constant `A / 2` deduced
  from the log-Sobolev inequality with constant `A`.
-/

public section

open Finset

namespace CycleCutoff

/-- A lower bound for `x log x` at `x = (1 + y)²`, accurate to second order in `y`. -/
private lemma sq_mul_log_sq_ge {y : ℝ} (hy : |y| ≤ 1 / 2) :
    2 * y + 3 * y ^ 2 - y ^ 4 - 9 * |y| ^ 3 ≤ (1 + y) ^ 2 * Real.log ((1 + y) ^ 2) := by
  have h1 : |-y| < 1 := by rw [abs_neg]; linarith
  have hE := Real.abs_log_sub_add_sum_range_le h1 2
  simp only [sum_range_succ, sum_range_zero, abs_neg, sub_neg_eq_add] at hE
  norm_num at hE
  have ha : 0 ≤ |y| := abs_nonneg y
  have h3 : 0 ≤ |y| ^ 3 := pow_nonneg ha 3
  have hE' : |-y + y ^ 2 / 2 + Real.log (1 + y)| ≤ 2 * |y| ^ 3 := by
    refine hE.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hlo := neg_abs_le (-y + y ^ 2 / 2 + Real.log (1 + y))
  have hsq : (1 + y) ^ 2 ≤ 9 / 4 := by
    have := abs_le.1 hy
    nlinarith
  rw [Real.log_pow]
  push_cast
  have key : (1 + y) ^ 2 * (2 * Real.log (1 + y)) - (2 * y + 3 * y ^ 2 - y ^ 4)
      = 2 * (1 + y) ^ 2 * (-y + y ^ 2 / 2 + Real.log (1 + y)) := by ring
  nlinarith [mul_le_mul_of_nonneg_left (hlo.trans' (neg_le_neg hE')) (sq_nonneg (1 + y)),
    mul_le_mul_of_nonneg_right hsq h3]

namespace InvFamily

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] (𝒯 : InvFamily ι Ω)

/-- **LSI implies Poincaré.** If `Ent_{u_Ω}(f²) ≤ A 𝒟_𝒯(f)` for all `f`, then
`Var_{u_Ω}(h) ≤ (A / 2) 𝒟_𝒯(h)` for all `h`. -/
@[cycle_cutoff "lem_lsi_implies_poincare"]
theorem variance_le_of_lsi (A : ℝ)
    (hLSI : ∀ f : Ω → ℝ, ent (unif Ω) (fun z => f z ^ 2) ≤ A * 𝒯.dirichletForm f)
    (h : Ω → ℝ) :
    variance (unif Ω) h ≤ A / 2 * 𝒯.dirichletForm h := by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · simp [variance, expectation, dirichletForm, innerP]
  set u : Ω → ℝ := fun z => h z - expectation (unif Ω) h
  have hu : expectation (unif Ω) u = 0 := by
    simp [u, isProbVec_unif.expectation_const]
  set m := expectation (unif Ω) (fun z => u z ^ 2)
  set M3 := expectation (unif Ω) (fun z => |u z| ^ 3)
  set M4 := expectation (unif Ω) (fun z => u z ^ 4)
  set D := 𝒯.dirichletForm h
  have hν := (isProbVec_unif (Ω := Ω)).nonneg
  have hDε : ∀ ε : ℝ, 𝒯.dirichletForm (fun z => 1 + ε * u z) = ε ^ 2 * D := by
    intro ε
    simp only [D, dirichletForm_eq, u, mul_sum, ← expectation_const_mul]
    refine sum_congr rfl fun e _ => ?_
    congr 1
    funext z
    ring
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 < B ∧ ∀ z, |u z| ≤ B :=
    ⟨∑ z, |u z| + 1, by positivity, fun z => by
      have := Finset.single_le_sum (f := fun z => |u z|) (fun z _ => abs_nonneg _) (mem_univ z)
      linarith⟩
  have hm0 : 0 ≤ m := expectation_nonneg hν fun z => sq_nonneg _
  have hM3 : 0 ≤ M3 := expectation_nonneg hν fun z => by positivity
  have hM4 : 0 ≤ M4 := expectation_nonneg hν fun z => by positivity
  set K := 9 * M3 + M4 + m ^ 2
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ε * B ≤ 1 / 2 → 2 * m - ε * K ≤ A * D := by
    intro ε hε hε1 hεB
    have hL := hLSI (fun z => 1 + ε * u z)
    rw [hDε] at hL
    have hglog : 3 * ε ^ 2 * m - ε ^ 4 * M4 - 9 * ε ^ 3 * M3 ≤
        expectation (unif Ω) (fun z => (1 + ε * u z) ^ 2 * Real.log ((1 + ε * u z) ^ 2)) := by
      have hmono := expectation_mono hν (f := fun z => 2 * ε * u z + 3 * ε ^ 2 * u z ^ 2 -
          ε ^ 4 * u z ^ 4 - 9 * ε ^ 3 * |u z| ^ 3)
        (g := fun z => (1 + ε * u z) ^ 2 * Real.log ((1 + ε * u z) ^ 2)) fun z => by
          have hy : |ε * u z| ≤ 1 / 2 := by
            rw [abs_mul, abs_of_pos hε]
            nlinarith [hB z]
          have := sq_mul_log_sq_ge hy
          rw [abs_mul, abs_of_pos hε] at this
          convert this using 1
          ring
      simp only [expectation_sub, expectation_add, expectation_const_mul, hu] at hmono
      linarith
    have hg : expectation (unif Ω) (fun z => (1 + ε * u z) ^ 2) = 1 + ε ^ 2 * m := by
      have : (fun z => (1 + ε * u z) ^ 2) = fun z => 1 + (2 * ε * u z + ε ^ 2 * u z ^ 2) := by
        funext z; ring
      rw [this, expectation_add (f := fun _ => 1), expectation_add, expectation_const_mul,
        expectation_const_mul, isProbVec_unif.expectation_const, hu]
      ring
    have hx : (1 + ε ^ 2 * m) * Real.log (1 + ε ^ 2 * m) ≤ (1 + ε ^ 2 * m) * (ε ^ 2 * m) := by
      have hpos : 0 < 1 + ε ^ 2 * m := by positivity
      have := Real.log_le_sub_one_of_pos hpos
      exact mul_le_mul_of_nonneg_left (by linarith) hpos.le
    unfold ent at hL
    rw [hg] at hL
    have hε2 : 0 < ε ^ 2 := by positivity
    have hbound : ε ^ 2 * (2 * m - ε * K) ≤ ε ^ 2 * (A * D) := by
      have h4 : ε ^ 4 * M4 ≤ ε ^ 3 * M4 := by
        have : ε ^ 4 ≤ ε ^ 3 := by
          rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) hε1
        exact mul_le_mul_of_nonneg_right this hM4
      have h4' : ε ^ 4 * m ^ 2 ≤ ε ^ 3 * m ^ 2 := by
        have : ε ^ 4 ≤ ε ^ 3 := by
          rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) hε1
        exact mul_le_mul_of_nonneg_right this (sq_nonneg m)
      simp only [K]
      nlinarith
    exact le_of_mul_le_mul_left hbound hε2
  have hvar : variance (unif Ω) h = m := rfl
  rw [hvar]
  have h2m : 2 * m ≤ A * D := by
    have hK : 0 ≤ K := by positivity
    refine le_of_forall_sub_le fun δ hδ => ?_
    set ε := min (min 1 (1 / (2 * B))) (δ / (K + 1))
    have hε : 0 < ε := by positivity
    have hε1 : ε ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
    have hεB : ε * B ≤ 1 / 2 := by
      have : ε ≤ 1 / (2 * B) := (min_le_left _ _).trans (min_le_right _ _)
      calc ε * B ≤ 1 / (2 * B) * B := mul_le_mul_of_nonneg_right this hB0.le
        _ = 1 / 2 := by field_simp
    have hεK : ε * K ≤ δ := by
      have : ε ≤ δ / (K + 1) := min_le_right _ _
      calc ε * K ≤ δ / (K + 1) * K := mul_le_mul_of_nonneg_right this hK
        _ ≤ δ := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
    linarith [key ε hε hε1 hεB]
  linarith

end InvFamily

end CycleCutoff
