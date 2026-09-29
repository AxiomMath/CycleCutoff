/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Integrated.Defs
public import CycleCutoff.LocalGap.CycleTwoCopyPoincare
public import CycleCutoff.Integrated.SeparationLaw
public import CycleCutoff.Generator.CorrelationIntegrable
public import CycleCutoff.Integrated.CoincidenceCorrelation
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Integrability of the coincidence probability

The function `t ↦ C_{n,m}(t) - 1/m` is integrable on `[0, ∞)`, and the centred coincidence
indicator `v = 1[X = Y] - 1/m` has mean zero under `ϖ_{n,m}`.

## Main results

* `CycleCutoff.expectation_centredCoincidence`: `𝔼_ϖ[v] = 0`.
* `CycleCutoff.integrableOn_coincidenceProb_sub`: the integrability of `t ↦ C_{n,m}(t) - 1/m`.

## Implementation notes

Integrability on `[0, ∞)` is stated on `Set.Ioi 0`, which differs from `Set.Ici 0` by a null set.
The only hypothesis is `m ≤ n`; for `m = 0` the state space is empty and every expectation
vanishes.
-/

public section

open Finset Matrix MeasureTheory

namespace CycleCutoff

variable {n : ℕ} [NeZero n] {m : ℕ}

/-- The centred coincidence indicator `v = 1[X = Y] - 1/m` has mean zero under `ϖ_{n,m}`. -/
theorem expectation_centredCoincidence (hm : m ≤ n) :
    expectation (unif (TwoCopyState (ZMod n) m)) (centredCoincidence n m) = 0 := by
  rcases isEmpty_or_nonempty (TwoCopyState (ZMod n) m) with h | h
  · simp [expectation]
  have hsep := expectation_indicator_x_sub_y_eq hm 0
  simp only [sub_eq_zero, if_true] at hsep
  have hv : centredCoincidence n m =
      fun w => (if w.x = w.y then (1 : ℝ) else 0) - 1 / (m : ℝ) :=
    funext centredCoincidence_apply
  rw [hv, expectation_sub, hsep, isProbVec_unif.expectation_const, sub_self]

/-- **Integrability of the coincidence probability**: `t ↦ C_{n,m}(t) - 1/m` is integrable on
`[0, ∞)`. -/
@[cycle_cutoff "lem_coincidence_integrable"]
theorem integrableOn_coincidenceProb_sub (hm : m ≤ n) :
    IntegrableOn (fun t => coincidenceProb n m t - 1 / (m : ℝ)) (Set.Ioi 0) := by
  obtain ⟨K, hK, hP⟩ := exists_variance_le_twoCopy
  have hA : 0 < K * (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    positivity
  have hint : IntegrableOn (fun t => (m : ℝ) * innerP (unif (TwoCopyState (ZMod n) m))
      (centredCoincidence n m) ((twoCopy n m).semigroup t *ᵥ centredCoincidence n m))
      (Set.Ioi 0) :=
    ((twoCopy n m).integrableOn_innerP_semigroup _ hA (hP n m) (centredCoincidence n m)
      (expectation_centredCoincidence hm)).const_mul (m : ℝ)
  exact hint.congr_fun (fun t _ => (coincidenceProb_sub_eq_innerP hm t).symm) measurableSet_Ioi

end CycleCutoff
