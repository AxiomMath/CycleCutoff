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
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Integrability of the explicit error

For `n ≥ 3` and `m ≤ n`, the explicit error `t ↦ ℰ_{n,m}(t)` is integrable on `[0, ∞)`.

## Main results

* `CycleCutoff.integrableOn_paperError`: the integrability of `t ↦ ℰ_{n,m}(t)`.

## Implementation notes

Integrability on `[0, ∞)` is stated on `Set.Ioi 0`, which differs from `Set.Ici 0` by a null set.
No lower bound on `m` is assumed: with real division by zero the identity `(n/m)(1/n) = 1/m` also
holds for `m = 0`.
-/

public section

open Finset Matrix MeasureTheory

namespace CycleCutoff

variable {n : ℕ} [NeZero n] {m : ℕ}

/-- The explicit error `ℰ_{n,m}` is integrable on `[0, ∞)`. -/
@[cycle_cutoff "lem_paper_error_integrable"]
theorem integrableOn_paperError (hn : 3 ≤ n) (hm : m ≤ n) :
    IntegrableOn (fun t => paperError n m t) (Set.Ioi 0) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  have h := (((integrableOn_coincidenceProb_sub (n := n) hm).sub
    ((integrableOn_S2_sub hn).const_mul ((n : ℝ) / m))).add
    ((integrableOn_S3_sub_S2_div hn).const_mul
      (((n : ℝ) / m) ^ 2 * (((n : ℝ) - m) / ((n : ℝ) - 1)))))
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  have hc : (n : ℝ) / m * (1 / n) = 1 / m := by
    rw [div_mul_div_comm, mul_one, mul_comm, ← div_div, div_self hn0]
  simp only [paperError, Pi.add_apply, Pi.sub_apply]
  linear_combination hc

end CycleCutoff
