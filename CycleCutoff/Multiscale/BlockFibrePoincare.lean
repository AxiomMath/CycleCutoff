/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Multiscale.Defs
public import CycleCutoff.Multiscale.BlockMeanCondExp
public import CycleCutoff.LocalGap.LocalGap

/-!
# Poincaré inequality on block fibres

There is an absolute constant `K > 0` such that for every block `B = I^z[a, b)` of the cycle `ℤ/nℤ`
(with `b ≤ n`) and every `f : Ω_{n,m} → ℝ`, `𝔼_ϖ[1[X ∈ B, Y ∈ B] Var_ϖ(f ∣ π_B)] ≤ K |B|² 𝒟_B(f)`.

## Main results

* `CycleCutoff.exists_expectation_indicator_condVar_le_blockDirichlet`: the Poincaré inequality on
  block fibres `𝔼_ϖ[1[X ∈ B, Y ∈ B] Var_ϖ(f ∣ π_B)] ≤ K |B|² 𝒟_B(f)`.
* `CycleCutoff.expectation_condVar_blockProj_le`: the fibre-by-fibre Poincaré inequality on a
  block, given a local Poincaré inequality for the path two-copy processes.
* `CycleCutoff.TwoCopyState.embed_twoCopyFamily_T`: the embedding
  `(S, x, y) ↦ (R₀ ∪ φ S, φ x, φ y)` intertwines two generic two-copy families whose edges
  correspond under `φ`.

## Implementation notes

The paper's standing hypotheses `n ≥ 3`, `1 ≤ m ≤ n` and `a < b` are not needed; only `b ≤ n` is
assumed, so that `p ↦ z + 1 + p` is injective on `[a, b)` and `|B| = b - a`.
-/

@[expose] public section

open Finset

namespace CycleCutoff

/-! ### Embedding a two-copy state space -/

namespace TwoCopyState

variable {V V' : Type*} [DecidableEq V] {k m : ℕ} (φ : V' ↪ V) (R₀ : Finset V)
  (hR₀ : ∀ v ∈ R₀, ∀ u, φ u ≠ v) (hkm : #R₀ + k = m)

omit [DecidableEq V] in
/-- A set avoiding the range of `φ` is disjoint from every image under `φ`. -/
theorem disjoint_map_of_forall_ne {φ : V' ↪ V} {R₀ : Finset V} (hR₀ : ∀ v ∈ R₀, ∀ u, φ u ≠ v)
    (S : Finset V') : Disjoint R₀ (S.map φ) :=
  disjoint_left.2 fun v hv hv' => by
    obtain ⟨u, -, rfl⟩ := mem_map.1 hv'
    exact hR₀ _ hv u rfl

/-- The embedding `(S, x, y) ↦ (R₀ ∪ φ S, φ x, φ y)` of `TwoCopyState V' k` into
`TwoCopyState V m`, for `R₀` disjoint from the range of `φ` with `|R₀| + k = m`. -/
def embed (w : TwoCopyState V' k) : TwoCopyState V m :=
  ⟨(R₀ ∪ w.R.map φ, φ w.x, φ w.y), by
    rw [card_union_of_disjoint (disjoint_map_of_forall_ne hR₀ _), card_map, w.card_R, hkm],
    mem_union_right _ (mem_map_of_mem _ w.x_mem), mem_union_right _ (mem_map_of_mem _ w.y_mem)⟩

variable {φ R₀ hR₀ hkm}

/-- The red set of the embedded state `(R₀ ∪ φ S, φ x, φ y)` is `R₀ ∪ φ S`. -/
@[simp] theorem R_embed (w : TwoCopyState V' k) :
    (embed φ R₀ hR₀ hkm w).R = R₀ ∪ w.R.map φ := rfl

/-- The first auxiliary coordinate of the embedded state `(R₀ ∪ φ S, φ x, φ y)` is `φ x`. -/
@[simp] theorem x_embed (w : TwoCopyState V' k) : (embed φ R₀ hR₀ hkm w).x = φ w.x := rfl

/-- The second auxiliary coordinate of the embedded state `(R₀ ∪ φ S, φ x, φ y)` is `φ y`. -/
@[simp] theorem y_embed (w : TwoCopyState V' k) : (embed φ R₀ hR₀ hkm w).y = φ w.y := rfl

/-- The embedding `(S, x, y) ↦ (R₀ ∪ φ S, φ x, φ y)` is injective. -/
theorem embed_injective : Function.Injective (embed (k := k) φ R₀ hR₀ hkm) := by
  intro w w' h
  rw [ext_iff'] at h ⊢
  obtain ⟨hR, hx, hy⟩ := h
  refine ⟨?_, φ.injective hx, φ.injective hy⟩
  have key : ∀ (S : Finset V') (u : V'), u ∈ S ↔ φ u ∈ R₀ ∪ S.map φ := fun S u => by
    simp only [mem_union, mem_map', or_iff_right (fun h => hR₀ _ h u rfl)]
  ext u
  have hR' : R₀ ∪ w.R.map φ = R₀ ∪ w'.R.map φ := hR
  rw [key, key w'.R, hR']

variable [DecidableEq V'] {ι : Type*} {edge' : ι → V' × V'} {edge : ι → V × V}

/-- If the edges correspond under `φ` (`edge e = φ × φ (edge' e)`), the transposition of an
edge commutes with `φ`. -/
theorem edgeSwap_map_apply (hedge : ∀ e, edge e = (φ (edge' e).1, φ (edge' e).2)) (e : ι)
    (u : V') : edgeSwap edge e (φ u) = φ (edgeSwap edge' e u) := by
  simp only [edgeSwap, hedge]
  exact φ.swap_apply _ _ _

/-- If the edges correspond under `φ`, the transposition of an edge acts on `R₀ ∪ φ S` through
`S` alone: it fixes `R₀` and matches the transposition of `edge'` on the image of `φ`. -/
theorem map_edgeSwap_union_map {R₀ : Finset V} (hR₀ : ∀ v ∈ R₀, ∀ u, φ u ≠ v)
    (hedge : ∀ e, edge e = (φ (edge' e).1, φ (edge' e).2)) (e : ι) (S : Finset V') :
    (R₀ ∪ S.map φ).map (edgeSwap edge e).toEmbedding =
      R₀ ∪ (S.map (edgeSwap edge' e).toEmbedding).map φ := by
  have hfix : ∀ v ∈ R₀, edgeSwap edge e v = v := fun v hv => by
    simp only [edgeSwap, hedge]
    exact Equiv.swap_apply_of_ne_of_ne (hR₀ v hv _).symm (hR₀ v hv _).symm
  rw [map_union, map_map, map_map]
  congr 1
  · ext v
    simp only [mem_map, Equiv.coe_toEmbedding]
    refine ⟨?_, fun hv => ⟨v, hv, hfix v hv⟩⟩
    rintro ⟨u, hu, rfl⟩
    rwa [hfix u hu]
  · congr 1
    ext u
    simp [edgeSwap_map_apply hedge]

/-- If the edges correspond under `φ` (`edge e = φ × φ (edge' e)`), the embedding
`(S, x, y) ↦ (R₀ ∪ φ S, φ x, φ y)` carries each move `T^sh_e, T^1_e, T^2_e` of the two-copy family
of `edge'` to the corresponding move of the two-copy family of `edge`. -/
theorem embed_twoCopyFamily_T (hedge : ∀ e, edge e = (φ (edge' e).1, φ (edge' e).2))
    (θ : TwoCopyMove ι) (w : TwoCopyState V' k) :
    embed φ R₀ hR₀ hkm ((twoCopyFamily edge' k).T θ w) =
      (twoCopyFamily edge m).T θ (embed φ R₀ hR₀ hkm w) := by
  have hset : ∀ e, edgeSet edge e = (edgeSet edge' e).map φ := fun e => by
    simp [edgeSet, hedge, map_insert]
  have hswap := edgeSwap_map_apply (φ := φ) hedge
  have hinter : ∀ e (S : Finset V'),
      (R₀ ∪ S.map φ) ∩ edgeSet edge e = (S ∩ edgeSet edge' e).map φ := fun e S => by
    rw [union_inter_distrib_right, hset, ← map_inter,
      disjoint_iff_inter_eq_empty.1 (disjoint_map_of_forall_ne hR₀ _), empty_union]
  have hsub : ∀ e (S : Finset V'),
      edgeSet edge e ⊆ R₀ ∪ S.map φ ↔ edgeSet edge' e ⊆ S := fun e S => by
    rw [← inter_eq_right, hinter, hset, map_inj, inter_eq_right]
  cases θ with
  | sh e =>
    simp only [twoCopyFamily_T_sh, shMove, R_embed, hinter, card_map]
    split_ifs
    · simp [ext_iff', map_edgeSwap_union_map hR₀ hedge, hswap]
    · rfl
  | one e | two e =>
    simp only [twoCopyFamily_T_one, oneMove, twoCopyFamily_T_two, twoMove]
    by_cases h : edgeSet edge' e ⊆ w.R
    · have h' : edgeSet edge e ⊆ (embed φ R₀ hR₀ hkm w).R := (hsub e w.R).2 h
      rw [dif_pos h, dif_pos h']
      simp [ext_iff', hswap]
    · have h' : ¬edgeSet edge e ⊆ (embed φ R₀ hR₀ hkm w).R := fun h' => h ((hsub e w.R).1 h')
      rw [dif_neg h, dif_neg h']

/-- The transposition of an edge inside `B` preserves membership in `B`. -/
theorem edgeSwap_mem_iff {ι : Type*} {edge : ι → V × V} {e : ι} {B : Finset V}
    (h : edgeSet edge e ⊆ B) {v : V} : edgeSwap edge e v ∈ B ↔ v ∈ B :=
  ⟨fun h' => by simpa [edgeSwap_edgeSwap] using edgeSwap_mem_of_subset edge h h',
    edgeSwap_mem_of_subset edge h⟩

/-- If every edge lies in `B`, the two-copy moves preserve whether each auxiliary coordinate
lies in `B`. -/
theorem twoCopyFamily_T_mem_iff {ι : Type*} {edge : ι → V × V} {B : Finset V}
    (hB : ∀ e, edgeSet edge e ⊆ B) (θ : TwoCopyMove ι) (w : TwoCopyState V m) :
    (((twoCopyFamily edge m).T θ w).x ∈ B ↔ w.x ∈ B) ∧
      (((twoCopyFamily edge m).T θ w).y ∈ B ↔ w.y ∈ B) := by
  cases θ with
  | sh e | one e | two e =>
    simp only [twoCopyFamily_T_sh, shMove, twoCopyFamily_T_one, oneMove,
      twoCopyFamily_T_two, twoMove]
    split_ifs <;> simp [edgeSwap_mem_iff (hB e)]

end TwoCopyState

/-! ### Conditional variance through the values on one fibre -/

section Fiberwise

variable {Ω Y : Type*} [Fintype Ω] (ν : Ω → ℝ) (Φ : Ω → Y) {f g : Ω → ℝ} {z : Ω}

/-- The conditional variance at `z` depends only on the values of `f` on the fibre of `z`. -/
theorem condVar_congr_fiber (h : ∀ v ∈ fiber Φ z, f v = g v) :
    condVar ν Φ f z = condVar ν Φ g z := by
  have hE : ∀ v ∈ fiber Φ z, condExp ν Φ f v = condExp ν Φ g v := fun v hv => by
    rw [condExp_apply, condExp_apply, fiber_eq_of_mem hv]
    congr 1
    exact sum_congr rfl fun u hu => by rw [h u hu]
  rw [condVar, condVar, condExp_apply, condExp_apply]
  congr 1
  exact sum_congr rfl fun v hv => by rw [h v hv, hE v hv]

/-- The conditional variance at `z` of a function vanishing on the fibre of `z` is zero. -/
theorem condVar_eq_zero_of_fiber (h : ∀ v ∈ fiber Φ z, f v = 0) : condVar ν Φ f z = 0 := by
  rw [condVar_congr_fiber ν Φ h]
  simp [condVar, condExp_apply]

end Fiberwise

/-- The indicator of the `π_B`-measurable event `{X, Y ∈ B}` can be absorbed into the function:
`1[X, Y ∈ B] Var(f ∣ π_B) = Var(1[X, Y ∈ B] f ∣ π_B)`. -/
theorem indicator_mul_condVar_blockProj {n : ℕ} [NeZero n] {m : ℕ} (B : Finset (ZMod n))
    (f : TwoCopyState (ZMod n) m → ℝ) (w : TwoCopyState (ZMod n) m) :
    (if w.x ∈ B ∧ w.y ∈ B then (1 : ℝ) else 0) *
        condVar (unif (TwoCopyState (ZMod n) m)) (blockProj B) f w =
      condVar (unif (TwoCopyState (ZMod n) m)) (blockProj B)
        (fun v => if v.x ∈ B ∧ v.y ∈ B then f v else 0) w := by
  by_cases hw : w.x ∈ B ∧ w.y ∈ B
  · rw [if_pos hw, one_mul]
    refine condVar_congr_fiber _ _ fun v hv => ?_
    have := (mem_fiber_blockProj hw.1 hw.2).1 hv
    simp only [if_pos (And.intro this.2.1 this.2.2)]
  · rw [if_neg hw, zero_mul, eq_comm]
    exact condVar_eq_zero_of_fiber _ _ fun v hv => if_neg (not_mem_of_mem_fiber_blockProj hw hv)

/-! ### The parametrisation of a cut interval -/

section CutInterval

variable (n : ℕ) (z : ZMod n) (a b : ℕ)

/-- The listing `j ↦ y_{a+j} = z + 1 + (a + j)` of `I^z[a, b)` by `Fin (b - a)`, injective for
`b ≤ n`. -/
def cutEmbedding (hb : b ≤ n) : Fin (b - a) ↪ ZMod n where
  toFun j := z + 1 + ((a + j : ℕ) : ZMod n)
  inj' i j h := Fin.ext (by have := eq_of_add_natCast_eq (by omega) (by omega) h; omega)

variable {n z a b}

/-- The listing of `I^z[a, b)` sends `j` to `y_{a+j} = z + 1 + (a + j)`. -/
@[simp] theorem cutEmbedding_apply (hb : b ≤ n) (j : Fin (b - a)) :
    cutEmbedding n z a b hb j = z + 1 + ((a + j : ℕ) : ZMod n) := rfl

/-- The listing `j ↦ y_{a+j}` enumerates `I^z[a, b)`. -/
theorem map_cutEmbedding (hb : b ≤ n) :
    univ.map (cutEmbedding n z a b hb) = cutInterval n z a b := by
  ext v
  simp only [mem_map, mem_univ, true_and, cutEmbedding_apply, mem_cutInterval]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨a + j, by omega, by omega, rfl⟩
  · rintro ⟨p, hap, hpb, rfl⟩
    exact ⟨⟨p - a, by omega⟩, by simp [Nat.add_sub_cancel' hap]⟩

/-- The listing `j ↦ y_{a+j}` takes its values in `I^z[a, b)`. -/
theorem cutEmbedding_mem_cutInterval (hb : b ≤ n) (j : Fin (b - a)) :
    cutEmbedding n z a b hb j ∈ cutInterval n z a b := by
  rw [← map_cutEmbedding hb]
  exact mem_map_of_mem _ (mem_univ j)

/-- The listing `j ↦ y_{a+j}` hits every element of `I^z[a, b)`. -/
theorem exists_cutEmbedding_eq (hb : b ≤ n) {v : ZMod n} (hv : v ∈ cutInterval n z a b) :
    ∃ j, cutEmbedding n z a b hb j = v := by
  rw [← map_cutEmbedding hb] at hv
  obtain ⟨j, -, hj⟩ := mem_map.1 hv
  exact ⟨j, hj⟩

/-- The block edge with index `j` is the image of the path edge `j` of `[b - a]` under the
listing of `I^z[a, b)`. -/
theorem blockEdge_eq_cutEmbedding (hb : b ≤ n) (j : Fin (b - a - 1)) :
    blockEdge n z a b j = (cutEmbedding n z a b hb (pathEdge (b - a) j).1,
      cutEmbedding n z a b hb (pathEdge (b - a) j).2) := by
  simp only [blockEdge, cycleEdge, pathEdge, cutEmbedding_apply, Prod.mk.injEq, true_and]
  push_cast
  ring

end CutInterval

/-! ### The fibres of the block projection -/

/-- If every block edge lies in `B`, truncating by the indicator of `{X, Y ∈ B}` does not increase
the block Dirichlet form of `I^z[a, b)`: `𝒟(1[X, Y ∈ B] f) ≤ 𝒟(f)`. -/
theorem dirichletForm_indicator_le {n : ℕ} [NeZero n] {m : ℕ} {z : ZMod n} {a b : ℕ}
    {B : Finset (ZMod n)} (hedgeB : ∀ j, edgeSet (blockEdge n z a b) j ⊆ B)
    (f : TwoCopyState (ZMod n) m → ℝ) :
    (blockFamily n m z a b).dirichletForm (fun w => if w.x ∈ B ∧ w.y ∈ B then f w else 0) ≤
      (blockFamily n m z a b).dirichletForm f := by
  rw [InvFamily.dirichletForm_eq, InvFamily.dirichletForm_eq]
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun θ _ => ?_) (by norm_num)
  refine expectation_mono (fun _ => by rw [unif_apply]; positivity) fun w => ?_
  have hT := TwoCopyState.twoCopyFamily_T_mem_iff hedgeB θ w
  by_cases hw : w.x ∈ B ∧ w.y ∈ B
  · have hw' : ((blockFamily n m z a b).T θ w).x ∈ B ∧ ((blockFamily n m z a b).T θ w).y ∈ B :=
      ⟨hT.1.2 hw.1, hT.2.2 hw.2⟩
    simp only [if_pos hw, if_pos hw', le_refl]
  · have hw' : ¬(((blockFamily n m z a b).T θ w).x ∈ B ∧
        ((blockFamily n m z a b).T θ w).y ∈ B) := fun h => hw ⟨hT.1.1 h.1, hT.2.1 h.2⟩
    simp only [if_neg hw, if_neg hw', sub_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    exact sq_nonneg _

/-- The embedding `(S, x, y) ↦ (R ∖ B ∪ φ S, φ x, φ y)` along an enumeration `φ` of a subset
of `B` lands in the fibre of `π_B` through `w₀`. -/
theorem embed_mem_fiber_blockProj {n m s : ℕ} [NeZero n] {B : Finset (ZMod n)}
    {φ : Fin s ↪ ZMod n} (hφB : ∀ j, φ j ∈ B) {w₀ : TwoCopyState (ZMod n) m}
    (hw₀x : w₀.x ∈ B) (hw₀y : w₀.y ∈ B) (hR₀ : ∀ u ∈ w₀.R \ B, ∀ j, φ j ≠ u)
    (hkm : #(w₀.R \ B) + #(w₀.R ∩ B) = m) (c : TwoCopyState (Fin s) #(w₀.R ∩ B)) :
    TwoCopyState.embed φ (w₀.R \ B) hR₀ hkm c ∈ fiber (blockProj B) w₀ := by
  refine (mem_fiber_blockProj hw₀x hw₀y).2 ⟨?_, hφB _, hφB _⟩
  have hc : c.R.map φ \ B = ∅ := sdiff_eq_empty_iff_subset.2 fun v hv => by
    obtain ⟨u, -, rfl⟩ := mem_map.1 hv
    exact hφB u
  rw [TwoCopyState.R_embed, union_sdiff_distrib, Finset.sdiff_idem, hc, union_empty]

/-- Every state on the fibre of `π_B` through `w₀` is an embedded internal state: if `φ`
enumerates `B`, then `v = (w₀.R ∖ B ∪ φ S, φ x, φ y)` for `S = φ⁻¹(v.R)`. -/
theorem exists_embed_eq_of_mem_fiber_blockProj {n m s : ℕ} [NeZero n] {B : Finset (ZMod n)}
    {φ : Fin s ↪ ZMod n} (hφB : ∀ j, φ j ∈ B) (hBφ : ∀ v ∈ B, ∃ j, φ j = v)
    {w₀ v : TwoCopyState (ZMod n) m} (hw₀x : w₀.x ∈ B) (hw₀y : w₀.y ∈ B)
    (hR₀ : ∀ u ∈ w₀.R \ B, ∀ j, φ j ≠ u) (hkm : #(w₀.R \ B) + #(w₀.R ∩ B) = m)
    (hv : v ∈ fiber (blockProj B) w₀) :
    ∃ c, TwoCopyState.embed φ (w₀.R \ B) hR₀ hkm c = v := by
  obtain ⟨hvR, hvx, hvy⟩ := (mem_fiber_blockProj hw₀x hw₀y).1 hv
  obtain ⟨i, hi⟩ := hBφ _ hvx
  obtain ⟨j, hj⟩ := hBφ _ hvy
  have hSmap : (univ.filter fun u => φ u ∈ v.R).map φ = v.R ∩ B := by
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, mem_inter]
    refine ⟨?_, fun hx => ?_⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨hu, hφB u⟩
    · obtain ⟨u, rfl⟩ := hBφ x hx.2
      exact ⟨u, hx.1, rfl⟩
  have hScard : #(univ.filter fun u => φ u ∈ v.R) = #(w₀.R ∩ B) := by
    rw [← card_map φ, hSmap]
    have h₁ := card_inter_add_card_sdiff v.R B
    have h₂ := card_inter_add_card_sdiff w₀.R B
    rw [v.card_R, hvR] at h₁
    rw [w₀.card_R] at h₂
    omega
  refine ⟨⟨(univ.filter fun u => φ u ∈ v.R, i, j), hScard,
    by simp [hi, v.x_mem], by simp [hj, v.y_mem]⟩, TwoCopyState.ext_iff'.2 ⟨?_, hi, hj⟩⟩
  change w₀.R \ B ∪ (univ.filter fun u => φ u ∈ v.R).map φ = v.R
  rw [hSmap, ← hvR, sdiff_union_inter]

/-- Fibre-by-fibre Poincaré inequality on a block: a local Poincaré inequality for the path
two-copy processes with constant `K` gives `𝔼_ϖ[Var_ϖ(g ∣ π_B)] ≤ K (b - a)² 𝒟_B(g)` for every `g`
vanishing off `{X, Y ∈ B}`. -/
theorem expectation_condVar_blockProj_le {n : ℕ} [NeZero n] {m : ℕ} {z : ZMod n} {a b : ℕ}
    (hb : b ≤ n) {K : ℝ} (hK : 0 ≤ K)
    (hP : ∀ s k : ℕ, ∀ F : TwoCopyState (Fin s) k → ℝ,
      variance (unif (TwoCopyState (Fin s) k)) F ≤
        K * (s : ℝ) ^ 2 * (pathTwoCopy s k).dirichletForm F)
    {g : TwoCopyState (ZMod n) m → ℝ} (hg : ∀ w : TwoCopyState (ZMod n) m,
      ¬(w.x ∈ cutInterval n z a b ∧ w.y ∈ cutInterval n z a b) → g w = 0) :
    expectation (unif (TwoCopyState (ZMod n) m))
        (condVar (unif (TwoCopyState (ZMod n) m)) (blockProj (cutInterval n z a b)) g) ≤
      K * ((b - a : ℕ) : ℝ) ^ 2 * (blockFamily n m z a b).dirichletForm g := by
  set B := cutInterval n z a b
  set φ := cutEmbedding n z a b hb
  have hφB : ∀ j, φ j ∈ B := cutEmbedding_mem_cutInterval hb
  have hBφ : ∀ v ∈ B, ∃ j, φ j = v := fun _ => exists_cutEmbedding_eq hb
  refine expectation_condVar_unif_le _ _ _ fun w₀ => ?_
  by_cases hw₀ : w₀.x ∈ B ∧ w₀.y ∈ B
  · have hR₀ : ∀ v ∈ w₀.R \ B, ∀ u, φ u ≠ v := fun v hv u h => (mem_sdiff.1 hv).2 (h ▸ hφB u)
    have hkm : #(w₀.R \ B) + #(w₀.R ∩ B) = m := by
      rw [add_comm, card_inter_add_card_sdiff, w₀.card_R]
    let F : TwoCopyState (Fin (b - a)) #(w₀.R ∩ B) → fiber (blockProj B) w₀ := fun c =>
      ⟨TwoCopyState.embed φ (w₀.R \ B) hR₀ hkm c,
        embed_mem_fiber_blockProj hφB hw₀.1 hw₀.2 hR₀ hkm c⟩
    have hF : Function.Bijective F := by
      refine ⟨fun c c' h =>
        TwoCopyState.embed_injective (hR₀ := hR₀) (hkm := hkm) (Subtype.ext_iff.1 h), ?_⟩
      rintro ⟨v, hv⟩
      obtain ⟨c, hc⟩ := exists_embed_eq_of_mem_fiber_blockProj hφB hBφ hw₀.1 hw₀.2 hR₀ hkm hv
      exact ⟨c, Subtype.ext hc⟩
    exact sum_sq_sub_avg_le_of_equiv (blockFamily n m z a b)
      (pathTwoCopy (b - a) #(w₀.R ∩ B)) (fiber (blockProj B) w₀) (Equiv.ofBijective F hF)
      (TwoCopyState.embed_twoCopyFamily_T (hR₀ := hR₀) (hkm := hkm)
        (blockEdge_eq_cutEmbedding (z := z) (a := a) hb)) (hP (b - a) _) g
  · have hg₀ : ∀ v ∈ fiber (blockProj B) w₀, g v = 0 := fun v hv =>
      hg v (not_mem_of_mem_fiber_blockProj hw₀ hv)
    rw [sum_congr rfl fun v hv => by rw [hg₀ v hv, sum_congr rfl hg₀]]
    simp only [sum_const_zero, zero_div, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    positivity

/-- **Poincaré inequality on block fibres.** There is an absolute constant `K > 0` such that for
every block `B = I^z[a, b)` with `b ≤ n` and every `f : Ω_{n,m} → ℝ`,
`𝔼_ϖ[1[X ∈ B, Y ∈ B] Var_ϖ(f ∣ π_B)] ≤ K |B|² 𝒟_B(f)`. -/
@[cycle_cutoff "lem_block_fibre_poincare"]
theorem exists_expectation_indicator_condVar_le_blockDirichlet :
    ∃ K > 0, ∀ (n : ℕ) [NeZero n] (m : ℕ) (z : ZMod n) (a b : ℕ), b ≤ n →
      ∀ f : TwoCopyState (ZMod n) m → ℝ,
        expectation (unif (TwoCopyState (ZMod n) m)) (fun w =>
            (if w.x ∈ cutInterval n z a b ∧ w.y ∈ cutInterval n z a b then 1 else 0) *
              condVar (unif (TwoCopyState (ZMod n) m)) (blockProj (cutInterval n z a b)) f w) ≤
          K * (#(cutInterval n z a b) : ℝ) ^ 2 * blockDirichlet n m z a b f := by
  obtain ⟨K₁, hK₁, hP⟩ := exists_variance_le_pathTwoCopy
  refine ⟨K₁, hK₁, fun n _ m z a b hb f => ?_⟩
  set B := cutInterval n z a b
  let g : TwoCopyState (ZMod n) m → ℝ := fun w => if w.x ∈ B ∧ w.y ∈ B then f w else 0
  have hedgeB : ∀ j, edgeSet (blockEdge n z a b) j ⊆ B := fun j => by
    rw [edgeSet, blockEdge_eq_cutEmbedding hb, insert_subset_iff, singleton_subset_iff]
    exact ⟨cutEmbedding_mem_cutInterval hb _, cutEmbedding_mem_cutInterval hb _⟩
  have h₁ : (blockFamily n m z a b).dirichletForm g ≤ (blockFamily n m z a b).dirichletForm f :=
    dirichletForm_indicator_le hedgeB f
  calc _ = expectation (unif _) (condVar (unif _) (blockProj B) g) :=
        congrArg _ (funext (indicator_mul_condVar_blockProj B f))
    _ ≤ K₁ * ((b - a : ℕ) : ℝ) ^ 2 * (blockFamily n m z a b).dirichletForm g :=
        expectation_condVar_blockProj_le hb hK₁.le hP fun w hw => if_neg hw
    _ ≤ K₁ * ((b - a : ℕ) : ℝ) ^ 2 * (blockFamily n m z a b).dirichletForm f := by gcongr
    _ = K₁ * (#B : ℝ) ^ 2 * blockDirichlet n m z a b f := by rw [card_cutInterval hb]; rfl

end CycleCutoff
