/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.TwoCopy.Defs
public import CycleCutoff.Generator.Lumping

/-!
# The first-copy marginal of the black two-copy chain

Forgetting the second auxiliary coordinate, `Ψ(β, y₁, y₂) = (β, y₁)`, lumps the black-labelled
two-copy chain `𝒢_A` onto the black-labelled one-copy chain `𝒰_A`. Consequently, for all `t`,
`(β₀, y⁰₁, y⁰₂) ∈ Ξ_A` and `(β, y₁) ∈ Ξ'_A`,
`∑_{y₂ ∈ R(β)} P^{𝒢_A}_t((β₀, y⁰₁, y⁰₂), (β, y₁, y₂)) = P^{𝒰_A}_t((β₀, y⁰₁), (β, y₁))`.

## Main definitions

* `CycleCutoff.BlackTwoState.fst`: the projection `Ψ : Ξ_A → Ξ'_A`, `(β, y₁, y₂) ↦ (β, y₁)`.

## Main results

* `CycleCutoff.blackTwoCopy_rateMatrix_mulVec_comp_fst`: `Q_{𝒢_A}(f ∘ Ψ) = (Q_{𝒰_A} f) ∘ Ψ`.
* `CycleCutoff.sum_blackTwoCopy_semigroup_eq_blackOneCopy`: the marginal identity above.
-/

@[expose] public section

open Finset Matrix

namespace CycleCutoff

variable {n : ℕ} [NeZero n] {A : Finset (ZMod n)}

/-- A transposition of two red positions fixes a black configuration. -/
theorem trans_swap_eq_self_of_mem_blackRed {β : BlackConfig n A} {a b : ZMod n}
    (ha : a ∈ blackRed β) (hb : b ∈ blackRed β) :
    β.trans (Equiv.swap a b).toEmbedding = β := by
  ext c
  simp [Equiv.swap_apply_of_ne_of_ne (mem_blackRed.1 ha c) (mem_blackRed.1 hb c)]

/-- The projection `Ψ : Ξ_A → Ξ'_A`, `(β, y₁, y₂) ↦ (β, y₁)`, forgetting the second auxiliary
coordinate. -/
def BlackTwoState.fst (w : BlackTwoState n A) : BlackOneState n A :=
  ⟨(w.1.1, w.1.2.1), w.2.1⟩

/-- The underlying pair of `Ψ(β, y₁, y₂)` is `(β, y₁)`. -/
@[simp] theorem BlackTwoState.fst_val (w : BlackTwoState n A) :
    w.fst.1 = (w.1.1, w.1.2.1) := rfl

/-- If `e_z ⊆ R(β)`, then `Ψ ∘ X_z = U_z ∘ Ψ`. -/
theorem BlackTwoState.fst_blackX_of_subset {z : ZMod n} {w : BlackTwoState n A}
    (h : ({z, z + 1} : Finset (ZMod n)) ⊆ blackRed w.1.1) :
    (blackX z w).fst = (blackOneCopy n A).T z w.fst :=
  Subtype.ext <| by
    simp [blackX, h, trans_swap_eq_self_of_mem_blackRed (h (mem_insert_self _ _))
      (h (mem_insert_of_mem (mem_singleton_self _)))]

/-- If `e_z ⊄ R(β)`, then `Ψ ∘ S_z = U_z ∘ Ψ`. -/
theorem BlackTwoState.fst_blackS_of_not_subset {z : ZMod n} {w : BlackTwoState n A}
    (h : ¬ ({z, z + 1} : Finset (ZMod n)) ⊆ blackRed w.1.1) :
    (blackS z w).fst = (blackOneCopy n A).T z w.fst :=
  Subtype.ext (by simp [blackS, h])

/-- `Ψ ∘ Y_z = Ψ`. -/
@[simp] theorem BlackTwoState.fst_blackY (z : ZMod n) (w : BlackTwoState n A) :
    (blackY z w).fst = w.fst := by
  rw [blackY]
  split_ifs <;> rfl

/-- `Q_{𝒢_A}(f ∘ Ψ) = (Q_{𝒰_A} f) ∘ Ψ`. -/
theorem blackTwoCopy_rateMatrix_mulVec_comp_fst (f : BlackOneState n A → ℝ) :
    (blackTwoCopy n A).rateMatrix *ᵥ (f ∘ BlackTwoState.fst) =
      ((blackOneCopy n A).rateMatrix *ᵥ f) ∘ BlackTwoState.fst := by
  rw [InvFamily.rateMatrix_mulVec, InvFamily.rateMatrix_mulVec]
  funext w
  simp only [InvFamily.generator, Function.comp_apply, TwoCopyMove.sum_eq, blackTwoCopy_T_sh,
    blackTwoCopy_T_one, blackTwoCopy_T_two, BlackTwoState.fst_blackY, sub_self, sum_const_zero,
    add_zero, ← sum_add_distrib]
  refine sum_congr rfl fun z _ => ?_
  by_cases h : ({z, z + 1} : Finset (ZMod n)) ⊆ blackRed w.1.1
  · simp [BlackTwoState.fst_blackX_of_subset h, blackS, h]
  · simp [BlackTwoState.fst_blackS_of_not_subset h, blackX, h]

/-- **First-copy marginal of the black two-copy chain.** Summing the black two-copy semigroup over
the second auxiliary coordinate `y₂ ∈ R(β)` gives the black one-copy semigroup:
`∑_{y₂ ∈ R(β)} P^{𝒢_A}_t((β₀, y⁰₁, y⁰₂), (β, y₁, y₂)) = P^{𝒰_A}_t((β₀, y⁰₁), (β, y₁))`. -/
@[cycle_cutoff "lem_black_marginal"]
theorem sum_blackTwoCopy_semigroup_eq_blackOneCopy (n : ℕ) [NeZero n] (A : Finset (ZMod n))
    (t : ℝ) (w₀ : BlackTwoState n A) (v : BlackOneState n A) :
    ∑ y₂ : ↥(blackRed v.1.1),
        (blackTwoCopy n A).semigroup t w₀ ⟨(v.1.1, v.1.2, y₂), v.2, y₂.2⟩ =
      (blackOneCopy n A).semigroup t ⟨(w₀.1.1, w₀.1.2.1), w₀.2.1⟩ v := by
  refine .trans ?_ (sum_semigroup_fiber _ _ BlackTwoState.fst
    blackTwoCopy_rateMatrix_mulVec_comp_fst t w₀ v)
  refine sum_bij (fun y₂ _ => ⟨(v.1.1, v.1.2, y₂), v.2, y₂.2⟩)
    (fun _ _ => mem_filter.2 ⟨mem_univ _, rfl⟩)
    (fun _ _ _ _ hy => Subtype.ext (congrArg (·.1.2.2) hy)) (fun w hw => ?_) fun _ _ => rfl
  obtain rfl := (mem_filter.1 hw).2
  exact ⟨⟨_, w.2.2⟩, mem_univ _, rfl⟩

end CycleCutoff
