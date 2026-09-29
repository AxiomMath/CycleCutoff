/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.LocalGap.LocalGap
public import CycleCutoff.Generator.DirichletTransport
public import CycleCutoff.Generator.DirichletFormula
public import CycleCutoff.FiniteProbability.PushforwardVariance

/-!
# Poincaré inequality for the cycle two-copy process

There is an absolute constant `K > 0` such that `Var_{ϖ_{n,m}}(f) ≤ K n² 𝒟_{n,m}(f)` for every
`f : Ω_{n,m} → ℝ`, where `ϖ_{n,m}` is the uniform measure on the two-copy states `Ω_{n,m}` and
`𝒟_{n,m}` is the Dirichlet form of the cycle two-copy process `𝒯_{n,m}`.

## Main results

* `CycleCutoff.TwoCopyState.congr_twoCopyFamily_T`: Transport of states along a bijection of
  vertices intertwines the two-copy families of corresponding edge maps.
* `CycleCutoff.InvFamily.dirichletForm_le_of_injective`: The Dirichlet form of a subfamily is at
  most that of the family.
* `CycleCutoff.exists_variance_le_twoCopy`: The Poincaré inequality for `𝒯_{n,m}`.

## Implementation notes

The statement carries no hypothesis on `n` or `m` beyond `n ≠ 0` (needed for `ℤ/nℤ` to be finite).
-/

public section

open Finset

namespace CycleCutoff

section Transport

variable {V V' ι : Type*} [DecidableEq V] [DecidableEq V'] (e : V ≃ V')

/-- Transport along `e : V ≃ V'` intertwines the two-copy family of `edge` with that of an edge map
`edge'` whose edges are the images of those of `edge`. -/
theorem TwoCopyState.congr_twoCopyFamily_T {m : ℕ} (edge : ι → V × V) (edge' : ι → V' × V')
    (h : ∀ i, edge' i = (e (edge i).1, e (edge i).2)) (θ : TwoCopyMove ι)
    (w : TwoCopyState V m) :
    TwoCopyState.congr e ((twoCopyFamily edge m).T θ w) =
      (twoCopyFamily edge' m).T θ (TwoCopyState.congr e w) := by
  have hswap : ∀ i v, e (edgeSwap edge i v) = edgeSwap edge' i (e v) := fun i v => by
    simp only [edgeSwap, h]
    exact e.injective.map_swap _ _ _
  have hset : ∀ i, edgeSet edge' i = (edgeSet edge i).map e.toEmbedding := fun i => by
    simp [edgeSet, h, map_insert]
  cases θ with
  | sh i =>
    simp only [twoCopyFamily_T_sh, shMove, TwoCopyState.R_congr, hset, ← map_inter, card_map]
    split_ifs
    · rw [TwoCopyState.ext_iff', TwoCopyState.R_congr, TwoCopyState.R_permMap,
        TwoCopyState.R_permMap, TwoCopyState.R_congr, map_map, map_map]
      exact ⟨congrArg w.R.map (Function.Embedding.ext (hswap i)), hswap i w.x, hswap i w.y⟩
    · rfl
  | one i | two i =>
    have hc : edgeSet edge' i ⊆ (TwoCopyState.congr e w).R ↔ edgeSet edge i ⊆ w.R := by
      rw [TwoCopyState.R_congr, hset, map_subset_map]
    simp only [twoCopyFamily_T_one, twoCopyFamily_T_two, oneMove, twoMove]
    by_cases hs : edgeSet edge i ⊆ w.R
    · rw [dif_pos hs, dif_pos (hc.2 hs)]
      simp [TwoCopyState.ext_iff', hswap]
    · rw [dif_neg hs, dif_neg (mt hc.1 hs)]

end Transport

/-- Dropping maps from an involution family can only decrease its Dirichlet form: if
`T'_i = T_{g i}` for an injection `g`, then `𝒟_{𝒯'}(f) ≤ 𝒟_𝒯(f)`. -/
theorem InvFamily.dirichletForm_le_of_injective {ι κ Ω : Type*} [Fintype ι] [Fintype κ]
    [Fintype Ω] (𝒯 : InvFamily κ Ω) (g : ι → κ) (hg : Function.Injective g)
    (𝒯' : InvFamily ι Ω) (h : ∀ i, 𝒯'.T i = 𝒯.T (g i)) (f : Ω → ℝ) :
    𝒯'.dirichletForm f ≤ 𝒯.dirichletForm f := by
  rw [InvFamily.dirichletForm_eq, InvFamily.dirichletForm_eq]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  simp only [h]
  exact (sum_map univ ⟨g, hg⟩ fun e => expectation (unif Ω) fun z => (f (𝒯.T e z) - f z) ^ 2
    ).symm.trans_le <| sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ =>
      expectation_nonneg (fun _ => inv_nonneg.2 (Nat.cast_nonneg _)) fun _ => sq_nonneg _

/-- The ring isomorphism `Fin n ≃+* ℤ/nℤ` sends `j + 1` to the image of `j` plus one, for
`j + 1 < n`. -/
private theorem finEquiv_succ' (n : ℕ) [NeZero n] (j : Fin (n - 1)) :
    ZMod.finEquiv n (⟨j + 1, by lia⟩ : Fin n) = ZMod.finEquiv n ⟨j, by lia⟩ + 1 := by
  rw [← map_one (ZMod.finEquiv n), ← map_add]
  congr 1
  ext
  rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  exact (Nat.mod_eq_of_lt (by lia)).symm

/-- Relabelling moves along an injection is injective. -/
private theorem TwoCopyMove.map_injective {ι κ : Type*} {g : ι → κ}
    (hg : Function.Injective g) : Function.Injective (TwoCopyMove.map g) := by
  rintro (a | a | a) (b | b | b) hab <;> simp_all [TwoCopyMove.map, hg.eq_iff]

/-- **Poincaré inequality for the cycle two-copy process.** There is an absolute constant `K > 0`
such that for all `n` and `m` and all `f : Ω_{n,m} → ℝ`, `Var_{ϖ_{n,m}}(f) ≤ K n² 𝒟_{n,m}(f)`. -/
@[cycle_cutoff "lem_cycle_two_copy_poincare"]
theorem exists_variance_le_twoCopy :
    ∃ K > 0, ∀ (n : ℕ) [NeZero n], ∀ m : ℕ, ∀ f : TwoCopyState (ZMod n) m → ℝ,
      variance (unif (TwoCopyState (ZMod n) m)) f ≤
        K * (n : ℝ) ^ 2 * (twoCopy n m).dirichletForm f := by
  obtain ⟨K₁, hK₁, hL⟩ := exists_variance_le_pathTwoCopy
  refine ⟨K₁, hK₁, fun n _ m f => ?_⟩
  let e : Fin n ≃ ZMod n := (ZMod.finEquiv n).toEquiv
  let Ψ : TwoCopyState (Fin n) m ≃ TwoCopyState (ZMod n) m := TwoCopyState.congr e
  let g : Fin (n - 1) → ZMod n := fun j => e ⟨j, by lia⟩
  let 𝒯m : InvFamily (TwoCopyMove (Fin (n - 1))) (TwoCopyState (ZMod n) m) :=
    { T := fun θ => (twoCopy n m).T (θ.map g)
      involutive := fun θ => (twoCopy n m).involutive (θ.map g) }
  have hT : ∀ θ, 𝒯m.T θ = (twoCopyFamily (fun j => cycleEdge n (g j)) m).T θ := by
    rintro (j | j | j) <;> rfl
  have hcomm : ∀ θ w, Ψ ((pathTwoCopy n m).T θ w) = 𝒯m.T (Equiv.refl _ θ) (Ψ w) := fun θ w => by
    rw [Equiv.refl_apply, hT]
    exact TwoCopyState.congr_twoCopyFamily_T e (pathEdge n) (fun j => cycleEdge n (g j))
      (fun j => Prod.ext rfl (finEquiv_succ' n j).symm) θ w
  have hΨ := pushforward_unif_equiv Ψ
  calc variance (unif (TwoCopyState (ZMod n) m)) f
      = variance (unif (TwoCopyState (Fin n) m)) (f ∘ Ψ) := by rw [← hΨ, ← variance_comp]; rfl
    _ ≤ K₁ * (n : ℝ) ^ 2 * (pathTwoCopy n m).dirichletForm (f ∘ Ψ) := hL n m (f ∘ Ψ)
    _ ≤ K₁ * (n : ℝ) ^ 2 * (twoCopy n m).dirichletForm f := by
      rw [InvFamily.dirichletForm_comp _ _ (Equiv.refl _) Ψ hΨ hcomm f]
      gcongr
      exact InvFamily.dirichletForm_le_of_injective _ _
        (TwoCopyMove.map_injective fun i j h => Fin.ext (Fin.mk.inj_iff.1 (e.injective h))) _
        (fun _ => rfl) f

end CycleCutoff
