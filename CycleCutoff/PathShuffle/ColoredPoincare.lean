/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.PathShuffle.Poincare
public import CycleCutoff.FiniteProbability.PushforwardVariance
public import CycleCutoff.Generator.DirichletTransport

/-!
# The Poincaré inequality for the coloured path process

There is an absolute constant `c₇ > 0` such that for every `s`, every colour multiplicity
vector `k` and every `f : Ω_{s,k} → ℝ`, `Var_u(f) ≤ c₇ s² 𝒟_{𝒯^col_{s,k}}(f)`.

## Main results

* `CycleCutoff.exists_variance_le_coloredProcess`: the Poincaré inequality
  `Var_u(f) ≤ c₇ s² 𝒟_{𝒯^col_{s,k}}(f)`.
-/

public section

open Finset

namespace CycleCutoff

variable {𝒜 : Type*} [DecidableEq 𝒜] {s : ℕ} {k : 𝒜 → ℕ}

/-- Two colourings with the same colour counts differ by a permutation of the positions. -/
private theorem ColoredConfig.exists_perm_eq_comp (c c' : ColoredConfig s k) :
    ∃ π : Equiv.Perm (Fin s), c'.1 = c.1 ∘ π :=
  ⟨Equiv.ofFiberEquiv fun a => Fintype.equivOfCardEq
      (by rw [Fintype.card_subtype, Fintype.card_subtype, c.2, c'.2]),
    funext fun i => (Equiv.ofFiberEquiv_map _ i).symm⟩

/-- The colouring `col ∘ σ⁻¹` seen at the positions after permuting by `σ`. -/
private def colorOfPerm (col : ColoredConfig s k) (σ : Equiv.Perm (Fin s)) :
    ColoredConfig s k :=
  ⟨col.1 ∘ ⇑σ⁻¹, fun a => (card_filter_comp_equiv col.1 σ⁻¹ a).trans (col.2 a)⟩

private theorem colorOfPerm_mul (col : ColoredConfig s k) (τ σ : Equiv.Perm (Fin s)) :
    (colorOfPerm col (τ * σ)).1 = (colorOfPerm col σ).1 ∘ ⇑τ⁻¹ := by
  funext i
  simp [colorOfPerm, mul_inv_rev]

private theorem colorOfPerm_pathShuffle (col : ColoredConfig s k) (j : Fin (s - 1))
    (σ : Equiv.Perm (Fin s)) :
    colorOfPerm col ((pathShuffle s).T j σ) = (coloredProcess s k).T j (colorOfPerm col σ) := by
  apply Subtype.ext
  rw [pathShuffle_T, colorOfPerm_mul, coloredProcess_T_val]
  congr 1

private theorem pushforward_colorOfPerm [Fintype 𝒜] (col : ColoredConfig s k) :
    pushforward (colorOfPerm col) (unif (Equiv.Perm (Fin s))) = unif (ColoredConfig s k) := by
  classical
  set Ψ := colorOfPerm col
  have hle : ∀ c₁ c₂ : ColoredConfig s k,
      #{σ | Ψ σ = c₁} ≤ #{σ | Ψ σ = c₂} := by
    intro c₁ c₂
    obtain ⟨π, hπ⟩ := ColoredConfig.exists_perm_eq_comp c₁ c₂
    refine card_le_card_of_injOn (fun σ => π⁻¹ * σ) (fun σ hσ => ?_)
      (fun σ _ τ _ h => mul_left_cancel h)
    simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hσ ⊢
    apply Subtype.ext
    rw [colorOfPerm_mul, inv_inv, show colorOfPerm col σ = c₁ from hσ, hπ]
  have hfib : ∀ c, pushforward Ψ (unif (Equiv.Perm (Fin s))) c =
      pushforward Ψ (unif (Equiv.Perm (Fin s))) col := by
    intro c
    simp only [pushforward, unif_apply, sum_const, nsmul_eq_mul]
    convert congrArg (fun n : ℕ => (n : ℝ) * (Fintype.card (Equiv.Perm (Fin s)) : ℝ)⁻¹)
      (le_antisymm (hle c col) (hle col c)) using 3 <;>
      first | rfl | (congr 1; exact filter_congr_decidable _ _ _)
  have hsum := sum_pushforward Ψ (unif (Equiv.Perm (Fin s)))
  rw [isProbVec_unif.sum_eq_one, sum_congr rfl fun c _ => hfib c, sum_const, card_univ,
    nsmul_eq_mul] at hsum
  funext c
  rw [hfib, unif_apply]
  exact eq_inv_of_mul_eq_one_left (by rwa [mul_comm] at hsum)

/-- **Poincaré inequality for the coloured path process.** There is an absolute constant `c₇ > 0`
such that for all `s`, all colour multiplicities `k` and all `f : Ω_{s,k} → ℝ`,
`Var_u(f) ≤ c₇ s² 𝒟_{𝒯^col_{s,k}}(f)`. -/
@[cycle_cutoff "lem_colored_poincare"]
theorem exists_variance_le_coloredProcess :
    ∃ c₇ > 0, ∀ (s : ℕ) {𝒜 : Type*} [Fintype 𝒜] [DecidableEq 𝒜] (k : 𝒜 → ℕ)
      (f : ColoredConfig s k → ℝ),
        variance (unif (ColoredConfig s k)) f ≤
          c₇ * (s : ℝ) ^ 2 * (coloredProcess s k).dirichletForm f := by
  obtain ⟨c, hc, hP⟩ := exists_variance_le_pathShuffle
  refine ⟨c, hc, fun s 𝒜 _ _ k f => ?_⟩
  rcases isEmpty_or_nonempty (ColoredConfig s k) with hΩ | hΩ
  · simp [variance, expectation, InvFamily.dirichletForm, innerP]
  obtain ⟨col⟩ := hΩ
  have hΨ := pushforward_colorOfPerm col
  have hV : variance (unif (ColoredConfig s k)) f =
      variance (unif (Equiv.Perm (Fin s))) (f ∘ colorOfPerm col) := by
    rw [← hΨ, ← variance_comp]
    rfl
  have hD : (pathShuffle s).dirichletForm (f ∘ colorOfPerm col) =
      (coloredProcess s k).dirichletForm f :=
    InvFamily.dirichletForm_comp _ _ (Equiv.refl _) _ hΨ
      (fun j σ => colorOfPerm_pathShuffle col j σ) f
  rw [hV, ← hD]
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp [variance, expectation, unif]
  · exact hP s hs _

end CycleCutoff
