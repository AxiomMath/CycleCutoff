/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.LocalGap.WithinSector
public import CycleCutoff.LocalGap.BetweenSector
public import CycleCutoff.FiniteProbability.VarDecomposition

/-!
# The uniform local Poincaré inequality

There is an absolute constant `K₁ > 0` such that for every `s`, `k` and every `f : Ω^p_{s,k} → ℝ`,
`Var_ν(f) ≤ K₁ s² 𝒟^p_{s,k}(f)`, where `ν` is the uniform measure on the two-copy states
`Ω^p_{s,k}` and `𝒟^p_{s,k}` is the Dirichlet form of the path two-copy chain.

## Main results

* `CycleCutoff.exists_variance_le_pathTwoCopy`: The uniform local Poincaré inequality.

## Implementation notes

No hypothesis on `s` or `k` is assumed: the inequality holds for all `s` and `k`.

## References

* C. Defant, *Cutoff for the Adjacent Transposition Shuffle on a Cycle*, Lemma 5.1.
-/

public section

open Finset

namespace CycleCutoff

/-- **Uniform local Poincaré inequality.** There is an absolute constant `K₁ > 0` with
`Var_ν(f) ≤ K₁ s² 𝒟^p_{s,k}(f)` for all `s`, `k` and `f : Ω^p_{s,k} → ℝ`. -/
@[cycle_cutoff "lem_local_gap"]
theorem exists_variance_le_pathTwoCopy :
    ∃ K₁ > 0, ∀ s k : ℕ, ∀ f : TwoCopyState (Fin s) k → ℝ,
      variance (unif (TwoCopyState (Fin s) k)) f ≤
        K₁ * (s : ℝ) ^ 2 * (pathTwoCopy s k).dirichletForm f := by
  obtain ⟨K₂, hK₂, hW⟩ := exists_expectation_condVar_diag_le
  refine ⟨K₂ + 8, by positivity, fun s k f => ?_⟩
  rw [variance_eq_expectation_condVar_add _ unif_pos (fun w => decide (w.x = w.y)) f]
  linarith [hW s k f, variance_condExp_diag_le s k f]

end CycleCutoff
