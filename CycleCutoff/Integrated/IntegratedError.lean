/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Integrated.Defs
public import CycleCutoff.Integrated.CoincidenceIntegrable
public import CycleCutoff.OneCard.S2Integrable
public import CycleCutoff.OneCard.BIntegrable
public import CycleCutoff.Integrated.ReturnIntegral
public import CycleCutoff.Integrated.RwIntegral
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# The integrated error

For `n ≥ 3` and `1 ≤ m ≤ n`, the explicit error `ℰ_{n,m}` integrates to
`∫_0^∞ ℰ_{n,m}(t) dt = -(n+1)(n-m)/(24m²) + (n-1)²/(4m) 𝓡_{n,m} + (n/m)² (n-m)/(n-1) B_n`.

## Main results

* `CycleCutoff.integral_paperError`: the integral of `ℰ_{n,m}` over `(0, ∞)`.

## Implementation notes

The integral over `[0, ∞)` is taken over `Set.Ioi 0`, which differs from `Set.Ici 0` by a null set.

## References

* C. Defant, *Cutoff for the Adjacent Transposition Shuffle on a Cycle*, Proposition 4.2.
-/

public section

open Finset Matrix MeasureTheory

namespace CycleCutoff

variable {n : ℕ} [NeZero n] {m : ℕ}

/-- The error `ℰ_{n,m}` as a linear combination of the three centred integrands. -/
private lemma paperError_eq_centred :
    (fun t => paperError n m t) = fun t =>
      (coincidenceProb n m t - 1 / (m : ℝ)) - (n : ℝ) / m * (S2 n t - 1 / (n : ℝ)) +
        ((n : ℝ) / m) ^ 2 * (((n : ℝ) - m) / ((n : ℝ) - 1)) * (S3 n t - S2 n t / n) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  have h : (n : ℝ) / m * (1 / n) = 1 / m := by field_simp
  funext t
  rw [paperError]
  linear_combination -h

/-- **Integrated error.** For `n ≥ 3` and `1 ≤ m ≤ n`,
`∫_0^∞ ℰ_{n,m}(t) dt = -(n+1)(n-m)/(24m²) + (n-1)²/(4m) 𝓡_{n,m} + (n/m)² (n-m)/(n-1) B_n`. -/
@[cycle_cutoff "prop_integrated"]
theorem integral_paperError (hn : 3 ≤ n) (hm₁ : 1 ≤ m) (hm : m ≤ n) :
    ∫ t in Set.Ioi 0, paperError n m t =
      -(((n : ℝ) + 1) * ((n : ℝ) - m)) / (24 * (m : ℝ) ^ 2) +
        ((n : ℝ) - 1) ^ 2 / (4 * m) * resolventQuantity n m +
        ((n : ℝ) / m) ^ 2 * (((n : ℝ) - m) / ((n : ℝ) - 1)) * Bn n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hC := integrableOn_coincidenceProb_sub (n := n) hm
  have hS := integrableOn_S2_sub hn
  have key : (n : ℝ) * ((m : ℝ) - 1) * ((n : ℝ) + 1) / (24 * (m : ℝ) ^ 2) -
      (n : ℝ) / m * (((n : ℝ) ^ 2 - 1) / (24 * n)) =
        -(((n : ℝ) + 1) * ((n : ℝ) - m)) / (24 * (m : ℝ) ^ 2) := by
    field_simp
    ring
  rw [paperError_eq_centred, integral_add ?_ ((integrableOn_S3_sub_S2_div hn).const_mul _),
    integral_sub hC (hS.const_mul _), integral_const_mul, integral_const_mul,
    integral_coincidenceProb_sub hn hm₁ hm, integral_S2_sub hn, ← Bn]
  · linear_combination key
  · exact hC.sub (hS.const_mul _)

end CycleCutoff
