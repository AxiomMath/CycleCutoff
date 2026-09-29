/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Cutoff.UpperBound
public import CycleCutoff.Cutoff.LowerBound

/-!
# Cutoff for the adjacent transposition shuffle on the cycle

There is an absolute constant `C > 0` such that for every `ε ∈ (0, 1)` there is a constant
`C_ε > 0` with
`t_n - C_ε n² ≤ t_mix^{(n)}(ε) ≤ t_n + C n² log log n + C_ε n²`
for all sufficiently large `n`.

## Main results

* `CycleCutoff.cutoff`: the two-sided mixing-time estimate.

## Implementation notes

"For all sufficiently large `n`" is rendered as `∀ n ≥ N₀`. The instance binder `[NeZero n]`
is only there so that `ZMod n` is a `Fintype`; being a `Prop`, it carries no information
beyond `n ≠ 0`. The mixing time `t_mix^{(n)}(ε)` is an infimum in `ℝ`, where `sInf ∅ = 0`.

## References

* C. Defant, *Cutoff for the Adjacent Transposition Shuffle on a Cycle*, Theorem A.
-/

public section

open Real

namespace CycleCutoff

/-- **Cutoff.** There is an absolute constant `C > 0` such that for every `ε ∈ (0, 1)` there
are `C_ε > 0` and `N₀` with `t_n - C_ε n² ≤ t_mix^{(n)}(ε) ≤ t_n + C n² log log n + C_ε n²` for
all `n ≥ N₀`. -/
@[cycle_cutoff "thm_main"]
theorem cutoff :
    ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ Cε > (0 : ℝ), ∃ N₀ : ℕ,
      ∀ (n : ℕ) [NeZero n], N₀ ≤ n →
        tn n - Cε * (n : ℝ) ^ 2 ≤ tmix n ε ∧
        tmix n ε ≤ tn n + C * (n : ℝ) ^ 2 * Real.log (Real.log n) + Cε * (n : ℝ) ^ 2 := by
  obtain ⟨C, hC, hup⟩ := exists_tmix_le
  refine ⟨C, hC, fun ε hε hε1 => ?_⟩
  obtain ⟨Cu, hCu, Nu, hNu⟩ := hup ε hε hε1
  obtain ⟨Cl, -, Nl, hNl⟩ := exists_tn_sub_le_tmix ε hε hε1
  refine ⟨max Cu Cl, lt_max_of_lt_left hCu, max Nu Nl, fun n _ hn => ⟨?_, ?_⟩⟩
  · have h := hNl n (le_of_max_le_right hn)
    have := mul_le_mul_of_nonneg_right (le_max_right Cu Cl) (sq_nonneg (n : ℝ))
    linarith
  · have h := hNu n (le_of_max_le_left hn)
    have := mul_le_mul_of_nonneg_right (le_max_left Cu Cl) (sq_nonneg (n : ℝ))
    linarith

end CycleCutoff
