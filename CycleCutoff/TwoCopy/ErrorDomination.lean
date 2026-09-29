/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.TwoCopy.CoincidenceDomination
public import CycleCutoff.Exposure.PredErrorExpansion

/-!
# Error domination

For `2 ≤ n`, `1 ≤ m ≤ n` and `t ≥ 0`, the prediction error is dominated by the explicit error:
`𝔈_{n,m}(t) ≤ ℰ_{n,m}(t)`. It plays the role of Lemma 4.1 of the paper.

## Main results

* `CycleCutoff.predictionError_le_paperError`: `𝔈_{n,m}(t) ≤ ℰ_{n,m}(t)`.

## Implementation notes

The paper states the lemma for `n ≥ 3`; it is stated here for `n ≥ 2`.
-/

public section

open Finset

namespace CycleCutoff

/-- **Error domination.** For `2 ≤ n`, `1 ≤ m ≤ n` and `t ≥ 0`, `𝔈_{n,m}(t) ≤ ℰ_{n,m}(t)`. -/
@[cycle_cutoff "lem_error_domination"]
theorem predictionError_le_paperError {n : ℕ} [NeZero n] (hn : 2 ≤ n) {m : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    predictionError n m t ≤ paperError n m t := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by lia)
  have hn1 : (n : ℝ) - 1 ≠ 0 := sub_ne_zero.2 (mod_cast (by lia : n ≠ 1))
  have key : paperError n m t -
      (exposureSecondMoment n m t - 2 * n / m * S2 n t + ((n : ℝ) / m) ^ 2 *
        (((m : ℝ) - 1) / ((n : ℝ) - 1) * S2 n t + ((n : ℝ) - m) / ((n : ℝ) - 1) * S3 n t)) =
      coincidenceProb n m t - exposureSecondMoment n m t := by
    rw [paperError]
    field_simp
    ring
  rw [predictionError_eq hn hm hmn ht]
  linarith [exposureSecondMoment_le_coincidenceProb (n := n) (m := m) ht]

end CycleCutoff
