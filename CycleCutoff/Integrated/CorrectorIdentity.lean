/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Integrated.Defs
public import CycleCutoff.Integrated.SeparationGenerator

/-!
# The corrector identity

The corrector `φ(r) = n(m-1)(n+1)/(24m²) - r(n-r)/(4m)` solves the Poisson equation
`-L_{n,m}[φ(X - Y)] = v + (n-1)/(2m) · b`, where `v = 1[X = Y] - 1/m` is the centred coincidence
indicator and `b = 1[X = Y] (w - 2(m-1)/(n-1))` is the source.

## Main results

* `CycleCutoff.neg_twoCopy_generator_corrector`: `-L_{n,m}[φ(X - Y)] = v + (n-1)/(2m) · b`.

## Implementation notes

The hypotheses are `3 ≤ n` and `1 ≤ m`; the latter is needed since `1/m` and the corrector are real
divisions by `m`. No upper bound `m ≤ n` is assumed.
-/

public section

open Finset Matrix

namespace CycleCutoff

variable {n : ℕ} [NeZero n] {m : ℕ}

/-- **The corrector identity.** The corrector `φ` satisfies
`-L_{n,m}[φ(X - Y)] = v + (n-1)/(2m) · b`. -/
@[cycle_cutoff "lem_corrector_identity"]
theorem neg_twoCopy_generator_corrector (hn : 3 ≤ n) (hm₁ : 1 ≤ m) :
    (fun w => -(twoCopy n m).generator (fun w' => corrector n m (w'.x - w'.y)) w) = fun w =>
      centredCoincidence n m w + ((n : ℝ) - 1) / (2 * m) * twoCopySource n m w := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [twoCopy_generator_comp_sub hn]
  funext w
  simp only [Delta_mulVec_corrector (by omega : 2 ≤ n), centredCoincidence_apply,
    twoCopySource_apply, if_true]
  by_cases hxy : w.x = w.y
  · simp only [hxy, sub_self, if_true]
    field_simp
    ring
  · have : w.x - w.y ≠ 0 := sub_ne_zero.2 hxy
    simp only [hxy, this, if_false]
    field_simp
    ring

end CycleCutoff
