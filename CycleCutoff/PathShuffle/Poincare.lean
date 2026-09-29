/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.PathShuffle.Lsi
public import CycleCutoff.Generator.LsiImpliesPoincare

/-!
# The Poincaré inequality for the path shuffle

There is an absolute constant `c > 0` such that for every `N ≥ 1` and every `f : 𝔖_N → ℝ`,
`Var_u(f) ≤ c N² 𝒟_{𝒯^path_N}(f)`.

## Main results

* `CycleCutoff.exists_variance_le_pathShuffle`: the Poincaré inequality
  `Var_u(f) ≤ c N² 𝒟_{𝒯^path_N}(f)`.
-/

public section

namespace CycleCutoff

/-- **Poincaré inequality for the path shuffle.** There is an absolute constant `c > 0` such that
for every `N ≥ 1` and every `f : 𝔖_N → ℝ`, `Var_u(f) ≤ c N² 𝒟_{𝒯^path_N}(f)`. -/
@[cycle_cutoff "lem_path_poincare"]
theorem exists_variance_le_pathShuffle :
    ∃ c > 0, ∀ N : ℕ, 1 ≤ N → ∀ f : Equiv.Perm (Fin N) → ℝ,
      variance (unif (Equiv.Perm (Fin N))) f ≤
        c * (N : ℝ) ^ 2 * (pathShuffle N).dirichletForm f := by
  obtain ⟨c₁, hc₁, hLSI⟩ := exists_ent_sq_le_pathShuffle
  exact ⟨c₁ / 2, by positivity, fun N hN f =>
    ((pathShuffle N).variance_le_of_lsi (c₁ * (N : ℝ) ^ 2) (hLSI N hN) f).trans_eq (by ring)⟩

end CycleCutoff
