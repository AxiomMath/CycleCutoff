/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.TwoCopy.Defs
public import CycleCutoff.Generator.Lumping
public import CycleCutoff.Generator.SemigroupSymmetric
public import CycleCutoff.Generator.ConeInvariance
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real

/-!
# Positive semidefiniteness of the coincidence matrices

For `i ∈ A`, `t ≥ 0` and a black configuration `β ∈ 𝔅_A`, the `R(β) × R(β)` matrix
`(P^{𝒢_A}_t((ι_A, i, i), (β, y₁, y₂)))_{y₁, y₂}` is positive semidefinite.

## Main results

* `CycleCutoff.commute_of_mulVec_mulVec`: two square matrices commute if their actions on vectors
  do.
* `CycleCutoff.semigroup_smul_one`: `P^{c I}_t = e^{t c} I`.
* `CycleCutoff.InvFamily.rateMatrix_mulVec_comp`: a map intertwining two involution families
  intertwines their rate matrices.
* `CycleCutoff.InvFamily.commute_rateMatrix`: involution families with commuting maps have
  commuting rate matrices.
* `CycleCutoff.posSemidef_blackTwoCopy_semigroup`: the coincidence matrices are positive
  semidefinite.

## Implementation notes

The paper's hypothesis `|A| = m` only names `m` and is dropped.
-/

public section

open Finset Matrix

namespace CycleCutoff

section Generic

variable {Ω Ω' : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω']

omit [DecidableEq Ω] in
/-- Two square matrices commute if their actions on vectors do. -/
theorem commute_of_mulVec_mulVec {A B : Matrix Ω Ω ℝ}
    (h : ∀ f : Ω → ℝ, A *ᵥ (B *ᵥ f) = B *ᵥ (A *ᵥ f)) : Commute A B := by
  classical
  change A * B = B * A
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  rwa [mulVec_mulVec, mulVec_mulVec, mulVec_single_one, mulVec_single_one] at this

/-- `P^{c I}_t = e^{t c} I`: the semigroup of the scalar matrix `c • 1`. -/
theorem semigroup_smul_one (c t : ℝ) :
    semigroup (c • (1 : Matrix Ω Ω ℝ)) t = Real.exp (t * c) • 1 := by
  rw [semigroup, smul_smul, smul_one_eq_diagonal, exp_diagonal, Pi.exp_def,
    ← Real.exp_eq_exp_ℝ, smul_one_eq_diagonal]

namespace InvFamily

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A map `j` with `T_e ∘ j = j ∘ T'_e` intertwines the rate matrices under restriction. -/
theorem rateMatrix_mulVec_comp (𝒯 : InvFamily ι Ω) (𝒯' : InvFamily ι Ω') (j : Ω' → Ω)
    (hj : ∀ e y, 𝒯.T e (j y) = j (𝒯'.T e y)) (f : Ω → ℝ) :
    (𝒯.rateMatrix *ᵥ f) ∘ j = 𝒯'.rateMatrix *ᵥ (f ∘ j) := by
  rw [rateMatrix_mulVec, rateMatrix_mulVec]
  funext y
  simp [generator, hj]

/-- Rate matrices of two involution families whose maps commute do commute. -/
theorem commute_rateMatrix (𝒯 : InvFamily ι Ω) (𝒯' : InvFamily κ Ω)
    (h : ∀ e e' w, 𝒯.T e (𝒯'.T e' w) = 𝒯'.T e' (𝒯.T e w)) :
    Commute 𝒯.rateMatrix 𝒯'.rateMatrix := by
  refine commute_of_mulVec_mulVec fun f => ?_
  simp only [rateMatrix_mulVec]
  funext w
  simp only [generator, sum_sub_distrib, sum_const, card_univ, h]
  rw [sum_comm]
  simp only [nsmul_eq_mul, ← mul_sum]
  ring

end InvFamily

end Generic

section Black

variable {n : ℕ} [NeZero n] {A : Finset (ZMod n)}

/-- The block `Γ(β) = (Γ(β, y₁, y₂))_{y₁, y₂ ∈ R(β)}` of a function `Γ` on `Ξ_A`. -/
private def blackBlock (Γ : BlackTwoState n A → ℝ) (β : BlackConfig n A) :
    Matrix (blackRed β) (blackRed β) ℝ :=
  Matrix.of fun y₁ y₂ => Γ ⟨(β, y₁, y₂), y₁.2, y₂.2⟩

variable (n A) in
/-- The maps `S_z` alone, as an involution family. -/
private def blackSFamily : InvFamily (ZMod n) (BlackTwoState n A) := ⟨blackS, blackS_involutive⟩

variable (n A) in
/-- The maps `X_z` alone, as an involution family. -/
private def blackXFamily : InvFamily (ZMod n) (BlackTwoState n A) := ⟨blackX, blackX_involutive⟩

variable (n A) in
/-- The maps `Y_z` alone, as an involution family. -/
private def blackYFamily : InvFamily (ZMod n) (BlackTwoState n A) := ⟨blackY, blackY_involutive⟩

/-- The transpositions `τ_z` with `e_z ⊆ R(β)`, acting on `R(β)`. -/
private def redFamily (β : BlackConfig n A) : InvFamily (ZMod n) (blackRed β) where
  T z y := if h : ({z, z + 1} : Finset (ZMod n)) ⊆ blackRed β then
      ⟨Equiv.swap z (z + 1) y, edgeSwap_mem_of_subset (cycleEdge n) (e := z) h y.2⟩ else y
  involutive z y := by
    by_cases h : ({z, z + 1} : Finset (ZMod n)) ⊆ blackRed β <;> simp [h]

private theorem rateMatrix_blackTwoCopy :
    (blackTwoCopy n A).rateMatrix = (blackSFamily n A).rateMatrix +
      (blackXFamily n A).rateMatrix + (blackYFamily n A).rateMatrix := by
  ext w w'
  simp only [InvFamily.rateMatrix, Matrix.add_apply, TwoCopyMove.sum_eq]
  rfl

variable (n A) in
/-- The cone `K` of functions all of whose blocks are positive semidefinite. -/
private def psdCone : Set (BlackTwoState n A → ℝ) := {Γ | ∀ β, (blackBlock Γ β).PosSemidef}

private theorem isClosed_psdCone : IsClosed (psdCone n A) := by
  simp only [psdCone, Set.ofPred_forall]
  refine isClosed_iInter fun β => ?_
  have hc : Continuous fun Γ : BlackTwoState n A → ℝ => blackBlock Γ β := by
    unfold blackBlock; fun_prop
  simp only [posSemidef_iff_dotProduct_mulVec, Set.ofPred_and, Set.ofPred_forall, IsHermitian]
  exact (isClosed_eq hc.matrix_conjTranspose hc).inter (isClosed_iInter fun x =>
    isClosed_le continuous_const (continuous_const.dotProduct (hc.matrix_mulVec continuous_const)))

private theorem single_mem_psdCone {i : ZMod n} (hi : i ∈ A) :
    Pi.single (blackTwoInit hi) 1 ∈ psdCone n A := by
  intro β
  let v : blackRed β → ℝ := fun y => if β = blackIncl A ∧ (y : ZMod n) = i then 1 else 0
  have : blackBlock (Pi.single (blackTwoInit hi) 1) β = vecMulVec v (star v) := by
    ext y₁ y₂
    simp only [blackBlock, of_apply, vecMulVec_apply, v, star_trivial, Pi.single_apply,
      blackTwoInit, Subtype.ext_iff, Prod.ext_iff]
    by_cases hβ : β = blackIncl A <;> by_cases h₁ : (y₁ : ZMod n) = i <;>
      by_cases h₂ : (y₂ : ZMod n) = i <;> simp [hβ, h₁, h₂]
  exact this ▸ posSemidef_vecMulVec_self_star v

variable (n A) in
/-- The operator `𝒫 Γ = ∑_z Γ ∘ S_z`. -/
private noncomputable def shMatrix : Matrix (BlackTwoState n A) (BlackTwoState n A) ℝ :=
  (blackSFamily n A).rateMatrix + (n : ℝ) • 1

private theorem shMatrix_mulVec (Γ : BlackTwoState n A → ℝ) :
    shMatrix n A *ᵥ Γ = ∑ z : ZMod n, Γ ∘ blackS z := by
  rw [shMatrix, add_mulVec, InvFamily.rateMatrix_mulVec, smul_mulVec, one_mulVec]
  funext w
  simp [InvFamily.generator, blackSFamily, sum_sub_distrib, Finset.sum_apply, ZMod.card]

private theorem blackBlock_smul (c : ℝ) (Γ : BlackTwoState n A → ℝ) (β : BlackConfig n A) :
    blackBlock (c • Γ) β = c • blackBlock Γ β :=
  rfl

private theorem blackBlock_sum {ι : Type*} (s : Finset ι) (f : ι → BlackTwoState n A → ℝ)
    (β : BlackConfig n A) : blackBlock (∑ z ∈ s, f z) β = ∑ z ∈ s, blackBlock (f z) β := by
  ext y₁ y₂
  simp [blackBlock, Finset.sum_apply, Matrix.sum_apply]

private theorem posSemidef_blackBlock_comp_blackS {Γ : BlackTwoState n A → ℝ}
    (hΓ : Γ ∈ psdCone n A) (z : ZMod n) (β : BlackConfig n A) :
    (blackBlock (Γ ∘ blackS z) β).PosSemidef := by
  by_cases h : ({z, z + 1} : Finset (ZMod n)) ⊆ blackRed β
  · have : blackBlock (Γ ∘ blackS z) β = blackBlock Γ β := by
      ext y₁ y₂
      simp [blackBlock, blackS, h]
    exact this ▸ hΓ β
  · let g : blackRed β → blackRed (β.trans (Equiv.swap z (z + 1)).toEmbedding) := fun y =>
      ⟨Equiv.swap z (z + 1) y, by rw [blackRed_trans]; exact mem_map_of_mem _ y.2⟩
    have : blackBlock (Γ ∘ blackS z) β =
        (blackBlock Γ (β.trans (Equiv.swap z (z + 1)).toEmbedding)).submatrix g g := by
      ext y₁ y₂
      simp only [blackBlock, Function.comp_apply, of_apply, submatrix_apply, blackS, if_neg h]
      rfl
    exact this ▸ (hΓ _).submatrix g

private theorem shMatrix_mulVec_mem {Γ : BlackTwoState n A → ℝ} (hΓ : Γ ∈ psdCone n A) :
    shMatrix n A *ᵥ Γ ∈ psdCone n A := fun β => by
  rw [shMatrix_mulVec, blackBlock_sum]
  exact posSemidef_sum _ fun z _ => posSemidef_blackBlock_comp_blackS hΓ z β

private theorem blackX_mk (z : ZMod n) (β : BlackConfig n A) (y y₂ : blackRed β) :
    blackX z ⟨(β, y, y₂), y.2, y₂.2⟩ =
      ⟨(β, (redFamily β).T z y, y₂), ((redFamily β).T z y).2, y₂.2⟩ := by
  by_cases h : ({z, z + 1} : Finset (ZMod n)) ⊆ blackRed β <;> simp [blackX, redFamily, h]

private theorem blackY_mk (z : ZMod n) (β : BlackConfig n A) (y₁ y : blackRed β) :
    blackY z ⟨(β, y₁, y), y₁.2, y.2⟩ =
      ⟨(β, y₁, (redFamily β).T z y), y₁.2, ((redFamily β).T z y).2⟩ := by
  by_cases h : ({z, z + 1} : Finset (ZMod n)) ⊆ blackRed β <;> simp [blackY, redFamily, h]

private theorem blackBlock_semigroup_blackX (s : ℝ) (Γ : BlackTwoState n A → ℝ)
    (β : BlackConfig n A) :
    blackBlock (semigroup (blackXFamily n A).rateMatrix s *ᵥ Γ) β =
      (redFamily β).semigroup s * blackBlock Γ β := by
  ext y₁ y₂
  have := congrFun (semigroup_mulVec_comp _ _
    (fun y : blackRed β => (⟨(β, y, y₂), y.2, y₂.2⟩ : BlackTwoState n A))
    (fun g => (InvFamily.rateMatrix_mulVec_comp (blackXFamily n A) (redFamily β) _
      (fun z y => blackX_mk z β y y₂) g).symm) s Γ).symm y₁
  simp only [Function.comp_apply] at this
  rw [blackBlock, of_apply, this, mul_apply]
  rfl

private theorem blackBlock_semigroup_blackY (s : ℝ) (Γ : BlackTwoState n A → ℝ)
    (β : BlackConfig n A) :
    blackBlock (semigroup (blackYFamily n A).rateMatrix s *ᵥ Γ) β =
      blackBlock Γ β * ((redFamily β).semigroup s)ᵀ := by
  ext y₁ y₂
  have := congrFun (semigroup_mulVec_comp _ _
    (fun y : blackRed β => (⟨(β, y₁, y), y₁.2, y.2⟩ : BlackTwoState n A))
    (fun g => (InvFamily.rateMatrix_mulVec_comp (blackYFamily n A) (redFamily β) _
      (fun z y => blackY_mk z β y₁ y) g).symm) s Γ).symm y₂
  simp only [Function.comp_apply] at this
  rw [blackBlock, of_apply, this, mul_apply]
  simp only [mulVec, dotProduct, transpose_apply, blackBlock, of_apply, Function.comp_apply,
    mul_comm]
  rfl

private theorem blackX_blackY (z z' : ZMod n) (w : BlackTwoState n A) :
    blackX z (blackY z' w) = blackY z' (blackX z w) := by
  obtain ⟨⟨β, y₁, y₂⟩, hw⟩ := w
  by_cases h : ({z, z + 1} : Finset (ZMod n)) ⊆ blackRed β <;>
    by_cases h' : ({z', z' + 1} : Finset (ZMod n)) ⊆ blackRed β <;>
    simp [blackX, blackY, h, h']

variable (n A) in
/-- The operator `𝒞 = Q_{𝒢_A} - 𝒫`. -/
private noncomputable def localMatrix : Matrix (BlackTwoState n A) (BlackTwoState n A) ℝ :=
  (blackXFamily n A).rateMatrix + (blackYFamily n A).rateMatrix + (-(n : ℝ)) • 1

private theorem semigroup_localMatrix (s : ℝ) :
    semigroup (localMatrix n A) s = Real.exp (s * -(n : ℝ)) •
      (semigroup (blackXFamily n A).rateMatrix s * semigroup (blackYFamily n A).rateMatrix s) := by
  have hXY := InvFamily.commute_rateMatrix (blackXFamily n A) (blackYFamily n A) blackX_blackY
  rw [localMatrix, semigroup, smul_add, exp_add_of_commute _ _
    (((Commute.one_right _).smul_right _).smul_right _), smul_add,
    exp_add_of_commute _ _ ((hXY.smul_left s).smul_right s),
    show NormedSpace.exp (s • (-(n : ℝ)) • (1 : Matrix (BlackTwoState n A) _ ℝ)) =
      semigroup ((-(n : ℝ)) • 1) s from rfl, semigroup_smul_one, mul_smul_comm, mul_one]
  rfl

private theorem semigroup_localMatrix_mulVec_mem (s : ℝ) {Γ : BlackTwoState n A → ℝ}
    (hΓ : Γ ∈ psdCone n A) : semigroup (localMatrix n A) s *ᵥ Γ ∈ psdCone n A := by
  rw [semigroup_localMatrix, smul_mulVec, ← mulVec_mulVec]
  intro β
  rw [blackBlock_smul]
  refine PosSemidef.smul ?_ (Real.exp_pos _).le
  rw [blackBlock_semigroup_blackX, blackBlock_semigroup_blackY, ← Matrix.mul_assoc]
  simpa [conjTranspose_eq_transpose_of_trivial] using
    (hΓ β).mul_mul_conjTranspose_same ((redFamily β).semigroup s)

end Black

/-- **Positive semidefiniteness of the coincidence matrices.** For `i ∈ A`, `t ≥ 0` and a black
configuration `β ∈ 𝔅_A`, the `R(β) × R(β)` matrix with entries
`P^{𝒢_A}_t((ι_A, i, i), (β, y₁, y₂))` is positive semidefinite. -/
@[cycle_cutoff "lem_black_psd"]
theorem posSemidef_blackTwoCopy_semigroup (n : ℕ) [NeZero n] (A : Finset (ZMod n)) {i : ZMod n}
    (hi : i ∈ A) {t : ℝ} (ht : 0 ≤ t) (β : BlackConfig n A) :
    Matrix.PosSemidef (Matrix.of fun y₁ y₂ : ↥(blackRed β) =>
      (blackTwoCopy n A).semigroup t (blackTwoInit hi) ⟨(β, y₁, y₂), y₁.2, y₂.2⟩) := by
  have hQ : (blackTwoCopy n A).rateMatrix = shMatrix n A + localMatrix n A := by
    rw [rateMatrix_blackTwoCopy, shMatrix, localMatrix, neg_smul]
    abel
  have hmem := semigroup_mulVec_mem_of_cone (psdCone n A) isClosed_psdCone
    (fun _ h _ h' β => (h β).add (h' β)) (fun c hc _ h β => (h β).smul hc) _ _
    (fun _ => shMatrix_mulVec_mem) (fun s _ _ => semigroup_localMatrix_mulVec_mem s) ht _
    (single_mem_psdCone hi) β
  rw [← hQ] at hmem
  convert hmem using 1
  ext y₁ y₂
  simp only [of_apply, blackBlock, mulVec_single_one, col_apply]
  exact InvFamily.semigroup_apply_comm _ _ _ _

end CycleCutoff
