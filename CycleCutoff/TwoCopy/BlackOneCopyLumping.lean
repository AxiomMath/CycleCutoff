/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.TwoCopy.Defs
public import CycleCutoff.Generator.Lumping

/-!
# Black one-copy lumping

For `A ⊆ ℤ/nℤ`, `i ∈ A`, a time `t` and a state `(β, y) ∈ Ξ'_A`, the law `μ_t` of the cycle
shuffle started from the identity, summed over the permutations `σ` with `σ|_{A^c} = β` and
`σ(i) = y`, is the transition probability `P^{𝒰_A}_t((ι_A, i), (β, y))` of the black-labelled
one-copy chain.

## Main results

* `CycleCutoff.sum_muT_permRestrict_eq`: `∑_{σ|_{A^c} = β, σ(i) = y} μ_t(σ) =
  P^{𝒰_A}_t((ι_A, i), (β, y))`.

## Implementation notes

The paper's hypothesis `|A| = m` only names the size of `A` and is dropped, and so is `t ≥ 0`:
the identity holds for every real `t`.
-/

public section

open Finset Matrix

namespace CycleCutoff

variable {n : ℕ} [NeZero n] {A : Finset (ZMod n)} {i : ZMod n}

/-- The lumping map `Ψ(σ) = (σ|_{A^c}, σ(i))` from permutations to `Ξ'_A`, for `i ∈ A`. -/
private def blackOneProj (hi : i ∈ A) (σ : Equiv.Perm (ZMod n)) : BlackOneState n A :=
  ⟨(permRestrict A σ, σ i), mem_blackRed.2 fun a h => by
    rw [permRestrict_apply] at h
    exact a.2 (σ.injective h ▸ hi)⟩

private theorem blackOneProj_swap_mul (hi : i ∈ A) (z : ZMod n) (σ : Equiv.Perm (ZMod n)) :
    blackOneProj hi (Equiv.swap z (z + 1) * σ) = (blackOneCopy n A).T z (blackOneProj hi σ) :=
  rfl

/-- **Black one-copy lumping.** For `i ∈ A` and every time `t`,
`∑_{σ|_{A^c} = β, σ(i) = y} μ_t(σ) = P^{𝒰_A}_t((ι_A, i), (β, y))`. -/
@[cycle_cutoff "lem_black_one_copy_lumping"]
theorem sum_muT_permRestrict_eq (n : ℕ) [NeZero n] (A : Finset (ZMod n)) {i : ZMod n}
    (hi : i ∈ A) (t : ℝ) (v : BlackOneState n A) :
    ∑ σ with permRestrict A σ = v.1.1 ∧ σ i = v.1.2, muT n t σ =
      (blackOneCopy n A).semigroup t (blackOneInit hi) v := by
  refine .trans (sum_congr ?_ fun _ _ => rfl)
    (sum_semigroup_fiber _ _ (blackOneProj hi) (fun f => ?_) t 1 v)
  · ext σ
    simp [blackOneProj, Subtype.ext_iff, Prod.ext_iff]
  · rw [InvFamily.rateMatrix_mulVec, InvFamily.rateMatrix_mulVec]
    ext σ
    simp only [InvFamily.generator, Function.comp_apply, cycleShuffle_T, blackOneProj_swap_mul]

end CycleCutoff
