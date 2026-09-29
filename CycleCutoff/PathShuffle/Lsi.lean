/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.PathShuffle.BisectionBetween
public import CycleCutoff.PathShuffle.BisectionWithin
public import CycleCutoff.FiniteProbability.EntChainRule

/-!
# The log-Sobolev inequality for the path shuffle

There is an absolute constant `c₁ > 0` such that for every `N ≥ 1` and every
`f : 𝔖_N → ℝ`, `Ent_u(f²) ≤ c₁ N² 𝒟_{𝒯^path_N}(f)`.

## Main results

* `CycleCutoff.exists_ent_sq_le_pathShuffle`: the log-Sobolev inequality
  `Ent_u(f²) ≤ c₁ N² 𝒟_{𝒯^path_N}(f)`.
-/

public section

open Finset Equiv

namespace CycleCutoff

/-- **Log-Sobolev inequality for the path shuffle.** There is an absolute constant `c₁ > 0` such
that for every `N ≥ 1` and every `f : 𝔖_N → ℝ`, `Ent_u(f²) ≤ c₁ N² 𝒟_{𝒯^path_N}(f)`. -/
@[cycle_cutoff "lem_lsi"]
theorem exists_ent_sq_le_pathShuffle :
    ∃ c₁ > 0, ∀ N : ℕ, 1 ≤ N → ∀ f : Equiv.Perm (Fin N) → ℝ,
      ent (unif (Equiv.Perm (Fin N))) (fun σ => f σ ^ 2) ≤
        c₁ * (N : ℝ) ^ 2 * (pathShuffle N).dirichletForm f := by
  obtain ⟨c₄, hc₄, hB⟩ := exists_ent_condExp_bisectionSet_le
  refine ⟨3 * c₄, by positivity, fun N => ?_⟩
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro hN f
  have hD := (pathShuffle N).dirichletForm_nonneg f
  rcases (show N = 1 ∨ 2 ≤ N by omega) with rfl | hN2
  · have : ent (unif (Perm (Fin 1))) (fun σ => f σ ^ 2) = 0 := by
      simp [ent, expectation, unif]
    rw [this]
    positivity
  · have hu : ∀ σ, 0 < unif (Perm (Fin N)) σ := unif_pos
    have hW := expectation_condEnt_bisectionSet_le N hN2
      (3 * c₄ * ((N / 2 : ℕ) : ℝ) ^ 2) (3 * c₄ * ((N - N / 2 : ℕ) : ℝ) ^ 2)
      (by positivity) (by positivity) (ih (N / 2) (by omega) (by omega))
      (ih (N - N / 2) (by omega) (by omega)) f
    have hk₁ : ((N / 2 : ℕ) : ℝ) ≤ ((N : ℝ) + 1) / 2 := by
      rw [le_div_iff₀ (by norm_num)]
      exact_mod_cast (show N / 2 * 2 ≤ N + 1 by omega)
    have hk₂ : ((N - N / 2 : ℕ) : ℝ) ≤ ((N : ℝ) + 1) / 2 := by
      rw [le_div_iff₀ (by norm_num)]
      exact_mod_cast (show (N - N / 2) * 2 ≤ N + 1 by omega)
    have hmax : max (3 * c₄ * ((N / 2 : ℕ) : ℝ) ^ 2) (3 * c₄ * ((N - N / 2 : ℕ) : ℝ) ^ 2) ≤
        3 * c₄ * (((N : ℝ) + 1) / 2) ^ 2 :=
      max_le (by gcongr) (by gcongr)
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    rw [ent_eq_ent_condExp_add _ hu (bisectionSet N (N / 2))]
    calc _ ≤ c₄ * (N : ℝ) ^ 2 * (pathShuffle N).dirichletForm f +
          3 * c₄ * (((N : ℝ) + 1) / 2) ^ 2 * (pathShuffle N).dirichletForm f :=
        add_le_add (hB N hN2 f) (hW.trans (mul_le_mul_of_nonneg_right hmax hD))
      _ ≤ 3 * c₄ * (N : ℝ) ^ 2 * (pathShuffle N).dirichletForm f := by
        rw [← add_mul]
        refine mul_le_mul_of_nonneg_right ?_ hD
        have h : 3 * ((N : ℝ) + 1) ^ 2 ≤ 8 * (N : ℝ) ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h hc₄.le]

end CycleCutoff
