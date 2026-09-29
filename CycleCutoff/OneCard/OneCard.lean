/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.OneCard.Defs
public import CycleCutoff.OneCard.DeltaInvolution
public import CycleCutoff.Generator.Lumping

/-!
# The motion of one card

Under the adjacent transposition shuffle on the cycle, the position of a single card performs
the one-card walk: for `σ ∈ 𝔖_n` and `i, x ∈ ℤ/nℤ`,
`∑_{σ' : σ'(i) = x} P_t(σ, σ') = p_t(σ(i), x)`.

## Main results

* `CycleCutoff.cycleShuffle_rateMatrix_mulVec_comp_apply`:
  `Q_{𝒯_n} (f ∘ Ψ_i) = (Δ f) ∘ Ψ_i` with `Ψ_i σ = σ i`.
* `CycleCutoff.sum_cycleShuffle_semigroup_apply_eq_heatKernel`:
  `∑_{σ' : σ'(i) = x} P_t(σ, σ') = p_t(σ(i), x)`.
* `CycleCutoff.sum_muT_mul_apply`: under `μ_t`, the position `σ(i)` has law `p_t(i, ·)`.
-/

public section

open Finset Matrix

namespace CycleCutoff

variable {n : ℕ} [NeZero n]

/-- The position of card `i` intertwines the shuffle generator with the one-card generator:
`Q_{𝒯_n} (f ∘ Ψ_i) = (Δ f) ∘ Ψ_i` with `Ψ_i σ = σ i`. -/
theorem cycleShuffle_rateMatrix_mulVec_comp_apply (i : ZMod n) (f : ZMod n → ℝ) :
    (cycleShuffle n).rateMatrix *ᵥ (f ∘ fun σ : Equiv.Perm (ZMod n) => σ i) =
      (Delta n *ᵥ f) ∘ fun σ : Equiv.Perm (ZMod n) => σ i := by
  rw [Delta_eq_rateMatrix, InvFamily.rateMatrix_mulVec, InvFamily.rateMatrix_mulVec]
  ext σ
  simp [InvFamily.generator, Equiv.Perm.mul_apply]

/-- **The motion of one card.** Under the adjacent transposition shuffle on the cycle, the
position of card `i` follows the one-card walk: `∑_{σ' : σ'(i) = x} P_t(σ, σ') = p_t(σ(i), x)`. -/
@[cycle_cutoff "lem_one_card"]
theorem sum_cycleShuffle_semigroup_apply_eq_heatKernel (t : ℝ) (σ : Equiv.Perm (ZMod n))
    (i x : ZMod n) :
    ∑ σ' with σ' i = x, (cycleShuffle n).semigroup t σ σ' = heatKernel n t (σ i) x :=
  sum_semigroup_fiber _ _ (fun σ : Equiv.Perm (ZMod n) => σ i)
    (cycleShuffle_rateMatrix_mulVec_comp_apply i) t σ x

/-- Under `μ_t`, the position `σ(i)` of card `i` has law `p_t(i, ·)`. -/
theorem sum_muT_mul_apply (t : ℝ) (i : ZMod n) (f : ZMod n → ℝ) :
    ∑ σ, muT n t σ * f (σ i) = ∑ x, heatKernel n t i x * f x := by
  rw [← sum_fiberwise univ (fun σ : Equiv.Perm (ZMod n) => σ i)]
  refine sum_congr rfl fun x _ => ?_
  have h := sum_cycleShuffle_semigroup_apply_eq_heatKernel (n := n) t 1 i x
  rw [Equiv.Perm.one_apply] at h
  rw [← h, sum_mul]
  refine sum_congr rfl fun σ hσ => ?_
  rw [(mem_filter.1 hσ).2, muT_def]

end CycleCutoff
