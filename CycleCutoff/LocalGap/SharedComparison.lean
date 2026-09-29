/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.LocalGap.Defs
public import CycleCutoff.Generator.DirichletFormula

/-!
# Shared-transposition comparison

The shared-transposition chain `𝒮_{s,k}`, which applies `τ_j` to all three coordinates of
`(R, x, y)`, has Dirichlet form at most twice that of the path two-copy process `𝒯^p_{s,k}`:
`𝒟_{𝒮_{s,k}}(f) ≤ 2 𝒟^p_{s,k}(f)` for every `f`.

## Main results

* `CycleCutoff.sq_sub_sharedFamily_le`: The pointwise comparison on one edge.
* `CycleCutoff.dirichletForm_sharedFamily_le`: `𝒟_{sharedFamily}(f) ≤ 2 𝒟_{twoCopyFamily}(f)` for
  an arbitrary finite graph.
* `CycleCutoff.dirichletForm_sharedChain_le`: `𝒟_{𝒮_{s,k}}(f) ≤ 2 𝒟^p_{s,k}(f)`.

## Implementation notes

The comparison holds for the families `sharedFamily edge m` and `twoCopyFamily edge m` of an
arbitrary edge map `edge : ι → V × V`; no hypothesis on the edges (such as distinct endpoints) is
needed, since a loop gives `τ_e = id`.
-/

public section

open Finset

namespace CycleCutoff

/-- A self-embedding that maps a finite set into itself fixes it setwise. -/
private theorem map_eq_self_of_mapsTo {V : Type*} {R : Finset V} {τ : V ↪ V}
    (h : ∀ v ∈ R, τ v ∈ R) : R.map τ = R :=
  map_eq_of_subset fun v hv => by obtain ⟨u, hu, rfl⟩ := mem_map.1 hv; exact h u hu

variable {V ι : Type*} [DecidableEq V] (edge : ι → V × V) (m : ℕ)

/-- On one edge `e`, the squared increment of `f` along the shared move `S_e` is at most
`2 (f(T^sh_e w) - f w)² + 2 (f(T^1_e w) - f w)² + 2 (f(T^2_e w') - f w')²`, `w' = T^1_e w`. -/
theorem sq_sub_sharedFamily_le (f : TwoCopyState V m → ℝ) (e : ι) (w : TwoCopyState V m) :
    (f ((sharedFamily edge m).T e w) - f w) ^ 2 ≤
      2 * (f (shMove edge m e w) - f w) ^ 2 + 2 * (f (oneMove edge m e w) - f w) ^ 2 +
        2 * (f (twoMove edge m e (oneMove edge m e w)) - f (oneMove edge m e w)) ^ 2 := by
  set a := (edge e).1
  set b := (edge e).2
  by_cases ha : a ∈ w.R <;> by_cases hb : b ∈ w.R
  · have hE : edgeSet edge e ⊆ w.R := insert_subset_iff.2 ⟨ha, singleton_subset_iff.2 hb⟩
    have hS : (sharedFamily edge m).T e w = twoMove edge m e (oneMove edge m e w) := by
      rw [sharedFamily_T, twoMove, dif_pos (by simp [oneMove, hE]), TwoCopyState.ext_iff']
      simp only [oneMove, dif_pos hE, TwoCopyState.R_permMap, TwoCopyState.x_permMap,
        TwoCopyState.y_permMap, TwoCopyState.R_mk, TwoCopyState.x_mk, TwoCopyState.y_mk, and_true]
      exact map_eq_self_of_mapsTo fun v hv => edgeSwap_mem_of_subset edge hE hv
    rw [hS]
    nlinarith [sq_nonneg (f (twoMove edge m e (oneMove edge m e w)) - 2 * f (oneMove edge m e w)
      + f w), sq_nonneg (f (shMove edge m e w) - f w)]
  rotate_left 2
  · have hfix : ∀ v ∈ w.R, edgeSwap edge e v = v := fun v hv =>
      Equiv.swap_apply_of_ne_of_ne (by rintro rfl; exact ha hv) (by rintro rfl; exact hb hv)
    have hS : (sharedFamily edge m).T e w = w := by
      rw [sharedFamily_T, TwoCopyState.ext_iff', TwoCopyState.R_permMap]
      exact ⟨map_eq_self_of_mapsTo fun v hv => (hfix v hv).symm ▸ hv, hfix _ w.x_mem,
        hfix _ w.y_mem⟩
    rw [hS, sub_self, zero_pow two_ne_zero]
    positivity
  all_goals
    have h₁ : (w.R ∩ edgeSet edge e).card = 1 := by
      rw [card_eq_one]
      first
        | exact ⟨a, by ext v; grind [mem_edgeSet]⟩
        | exact ⟨b, by ext v; grind [mem_edgeSet]⟩
    rw [show (sharedFamily edge m).T e w = shMove edge m e w by
      rw [sharedFamily_T, shMove, if_pos h₁]]
    nlinarith [sq_nonneg (f (oneMove edge m e w) - f w),
      sq_nonneg (f (twoMove edge m e (oneMove edge m e w)) - f (oneMove edge m e w))]

variable [Fintype V] [Fintype ι]

/-- The shared-transposition family has Dirichlet form at most twice that of the two-copy family of
the same graph. -/
theorem dirichletForm_sharedFamily_le (f : TwoCopyState V m → ℝ) :
    (sharedFamily edge m).dirichletForm f ≤ 2 * (twoCopyFamily edge m).dirichletForm f := by
  rw [InvFamily.dirichletForm_eq, InvFamily.dirichletForm_eq, TwoCopyMove.sum_eq]
  simp only [twoCopyFamily_T_sh, twoCopyFamily_T_one, twoCopyFamily_T_two, expectation_unif,
    ← mul_sum]
  have key (e : ι) : ∑ w, (f ((sharedFamily edge m).T e w) - f w) ^ 2 ≤
      2 * (∑ w, (f (shMove edge m e w) - f w) ^ 2 + ∑ w, (f (oneMove edge m e w) - f w) ^ 2 +
        ∑ w, (f (twoMove edge m e w) - f w) ^ 2) := by
    rw [← Equiv.sum_comp (oneMove_involutive edge m e).toPerm
      (fun w => (f (twoMove edge m e w) - f w) ^ 2), mul_add, mul_add, mul_sum, mul_sum, mul_sum,
      ← sum_add_distrib, ← sum_add_distrib]
    exact sum_le_sum fun w _ => sq_sub_sharedFamily_le edge m f e w
  have := sum_le_sum fun e (_ : e ∈ univ) => key e
  rw [← mul_sum, sum_add_distrib, sum_add_distrib] at this
  have hc : (0 : ℝ) ≤ (Fintype.card (TwoCopyState V m) : ℝ)⁻¹ := by positivity
  linarith [mul_le_mul_of_nonneg_left this hc]

/-- **Shared-transposition comparison.** `𝒟_{𝒮_{s,k}}(f) ≤ 2 𝒟^p_{s,k}(f)`. -/
@[cycle_cutoff "lem_shared_comparison"]
theorem dirichletForm_sharedChain_le (s k : ℕ) (f : TwoCopyState (Fin s) k → ℝ) :
    (sharedChain s k).dirichletForm f ≤ 2 * (pathTwoCopy s k).dirichletForm f :=
  dirichletForm_sharedFamily_le (pathEdge s) k f

end CycleCutoff
