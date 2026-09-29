/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.OneCard.Defs
public import CycleCutoff.TwoCopy.Defs
public import CycleCutoff.Integrated.Defs
public import CycleCutoff.Integrated.IntegratedError
public import CycleCutoff.Multiscale.Resolvent
public import CycleCutoff.OneCard.BBound
public import CycleCutoff.OneCard.BIntegrandNonneg
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The total integrated error

There is an absolute constant `K > 0` such that for every `n ≥ 3`,
`∑_{m=1}^n m ∫_0^∞ ℰ_{n,m}(t) dt ≤ K n² (1 + log n)³`.

## Main results

* `CycleCutoff.exists_sum_mul_integral_paperError_le`: the bound on the total integrated error.

## References

* C. Defant, *Cutoff for the Adjacent Transposition Shuffle on a Cycle*, Lemma 7.1.
-/

public section

open Finset Real MeasureTheory

namespace CycleCutoff

/-- The constant `B_n` is nonnegative. -/
private lemma Bn_nonneg (n : ℕ) [NeZero n] : 0 ≤ Bn n :=
  setIntegral_nonneg measurableSet_Ioi fun _ ht => S2_div_le_S3 (le_of_lt ht)

/-- **Total integrated error**: there is an absolute constant `K > 0` such that for every
`n ≥ 3`, `∑_{m=1}^n m ∫_0^∞ ℰ_{n,m}(t) dt ≤ K n² (1 + log n)³`. -/
@[cycle_cutoff "lem_total_error"]
theorem exists_sum_mul_integral_paperError_le :
    ∃ K > (0 : ℝ), ∀ (n : ℕ) [NeZero n], 3 ≤ n →
      ∑ m ∈ Finset.Icc 1 n, (m : ℝ) * ∫ t in Set.Ioi 0, paperError n m t ≤
        K * (n : ℝ) ^ 2 * (1 + Real.log n) ^ 3 := by
  obtain ⟨K₃, hK₃, hres⟩ := exists_resolventQuantity_le
  obtain ⟨c, hc, hB⟩ := exists_Bn_le
  refine ⟨K₃ / 4 + c, by positivity, fun n _ hn => ?_⟩
  set L := 1 + Real.log n with hL
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hL1 : 1 ≤ L := by
    have := Real.log_nonneg hn1.le
    linarith
  have hB0 := Bn_nonneg n
  have hBn := hB n hn
  have key : ∀ m ∈ Finset.Icc 1 n, (m : ℝ) * ∫ t in Set.Ioi 0, paperError n m t ≤
      ((n : ℝ) ^ 2 / 4 * K₃ * L ^ 2 + (n : ℝ) ^ 2 * Bn n) * (m : ℝ)⁻¹ := by
    intro m hm
    obtain ⟨hm1, hmn⟩ := Finset.mem_Icc.1 hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    rw [integral_paperError hn hm1 hmn]
    have hR := hres n hn m hm1 hmn
    have h1 : (m : ℝ) * (-(((n : ℝ) + 1) * ((n : ℝ) - m)) / (24 * (m : ℝ) ^ 2)) ≤ 0 := by
      have : 0 ≤ ((n : ℝ) + 1) * ((n : ℝ) - m) / (24 * (m : ℝ) ^ 2) := by
        apply div_nonneg
        · nlinarith
        · positivity
      rw [neg_div]
      nlinarith
    have hfrac : (1 - (m : ℝ) / n) / m ≤ (m : ℝ)⁻¹ := by
      rw [div_eq_mul_inv]
      have : 0 ≤ (m : ℝ) / n := by positivity
      have : 0 < (m : ℝ)⁻¹ := by positivity
      nlinarith
    have h2 : (m : ℝ) * (((n : ℝ) - 1) ^ 2 / (4 * m) * resolventQuantity n m) ≤
        (n : ℝ) ^ 2 / 4 * K₃ * L ^ 2 * (m : ℝ)⁻¹ := by
      have e : (m : ℝ) * (((n : ℝ) - 1) ^ 2 / (4 * m) * resolventQuantity n m) =
          ((n : ℝ) - 1) ^ 2 / 4 * resolventQuantity n m := by
        field_simp
      rw [e]
      have hsq : ((n : ℝ) - 1) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
      have hRle : resolventQuantity n m ≤ K₃ * L ^ 2 * (m : ℝ)⁻¹ := by
        calc resolventQuantity n m ≤ K₃ * ((1 - (m : ℝ) / n) / m) * L ^ 2 := hR
          _ ≤ K₃ * (m : ℝ)⁻¹ * L ^ 2 := by gcongr
          _ = K₃ * L ^ 2 * (m : ℝ)⁻¹ := by ring
      have hpos : 0 ≤ K₃ * L ^ 2 * (m : ℝ)⁻¹ := by positivity
      calc ((n : ℝ) - 1) ^ 2 / 4 * resolventQuantity n m
          ≤ ((n : ℝ) - 1) ^ 2 / 4 * (K₃ * L ^ 2 * (m : ℝ)⁻¹) := by gcongr
        _ ≤ (n : ℝ) ^ 2 / 4 * (K₃ * L ^ 2 * (m : ℝ)⁻¹) := by gcongr
        _ = (n : ℝ) ^ 2 / 4 * K₃ * L ^ 2 * (m : ℝ)⁻¹ := by ring
    have h3 : (m : ℝ) * (((n : ℝ) / m) ^ 2 * (((n : ℝ) - m) / ((n : ℝ) - 1)) * Bn n) ≤
        (n : ℝ) ^ 2 * Bn n * (m : ℝ)⁻¹ := by
      have e : (m : ℝ) * (((n : ℝ) / m) ^ 2 * (((n : ℝ) - m) / ((n : ℝ) - 1)) * Bn n) =
          (n : ℝ) ^ 2 * Bn n * (m : ℝ)⁻¹ * (((n : ℝ) - m) / ((n : ℝ) - 1)) := by
        field_simp
      rw [e]
      have hq : ((n : ℝ) - m) / ((n : ℝ) - 1) ≤ 1 := by
        rw [div_le_one (by linarith)]
        have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
        linarith
      have hpos : 0 ≤ (n : ℝ) ^ 2 * Bn n * (m : ℝ)⁻¹ := by positivity
      calc (n : ℝ) ^ 2 * Bn n * (m : ℝ)⁻¹ * (((n : ℝ) - m) / ((n : ℝ) - 1))
          ≤ (n : ℝ) ^ 2 * Bn n * (m : ℝ)⁻¹ * 1 := by gcongr
        _ = _ := mul_one _
    calc (m : ℝ) * (-(((n : ℝ) + 1) * ((n : ℝ) - m)) / (24 * (m : ℝ) ^ 2) +
          ((n : ℝ) - 1) ^ 2 / (4 * m) * resolventQuantity n m +
          ((n : ℝ) / m) ^ 2 * (((n : ℝ) - m) / ((n : ℝ) - 1)) * Bn n)
        = (m : ℝ) * (-(((n : ℝ) + 1) * ((n : ℝ) - m)) / (24 * (m : ℝ) ^ 2)) +
          (m : ℝ) * (((n : ℝ) - 1) ^ 2 / (4 * m) * resolventQuantity n m) +
          (m : ℝ) * (((n : ℝ) / m) ^ 2 * (((n : ℝ) - m) / ((n : ℝ) - 1)) * Bn n) := by ring
      _ ≤ 0 + (n : ℝ) ^ 2 / 4 * K₃ * L ^ 2 * (m : ℝ)⁻¹ + (n : ℝ) ^ 2 * Bn n * (m : ℝ)⁻¹ := by
          gcongr
      _ = _ := by ring
  have hH : ∑ m ∈ Finset.Icc 1 n, (m : ℝ)⁻¹ ≤ L := by
    have := harmonic_le_one_add_log n
    simpa [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using this
  have hA : 0 ≤ (n : ℝ) ^ 2 / 4 * K₃ * L ^ 2 + (n : ℝ) ^ 2 * Bn n := by positivity
  calc ∑ m ∈ Finset.Icc 1 n, (m : ℝ) * ∫ t in Set.Ioi 0, paperError n m t
      ≤ ∑ m ∈ Finset.Icc 1 n,
          ((n : ℝ) ^ 2 / 4 * K₃ * L ^ 2 + (n : ℝ) ^ 2 * Bn n) * (m : ℝ)⁻¹ :=
        Finset.sum_le_sum key
    _ = ((n : ℝ) ^ 2 / 4 * K₃ * L ^ 2 + (n : ℝ) ^ 2 * Bn n) *
          ∑ m ∈ Finset.Icc 1 n, (m : ℝ)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ ((n : ℝ) ^ 2 / 4 * K₃ * L ^ 2 + (n : ℝ) ^ 2 * (c * L)) * L := by gcongr
    _ ≤ ((n : ℝ) ^ 2 / 4 * K₃ * L ^ 2 + (n : ℝ) ^ 2 * (c * L ^ 2)) * L := by
        gcongr
        nlinarith
    _ = (K₃ / 4 + c) * (n : ℝ) ^ 2 * L ^ 3 := by ring

end CycleCutoff
