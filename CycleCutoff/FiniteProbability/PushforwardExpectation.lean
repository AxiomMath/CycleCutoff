/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.FiniteProbability.Defs

/-!
# Expectation against a push-forward

For a weight vector `ν` on a finite type `Ω` and a map `Φ : Ω → Y` to a finite type, the
push-forward `Φ_* ν` is a probability vector whenever `ν` is, and expectations of functions
factoring through `Φ` may be computed on `Y`: `𝔼_ν[h ∘ Φ] = 𝔼_{Φ_* ν}[h]`. Both facts come
from grouping a sum over `Ω` by the fibres of `Φ`, which partition `Ω`.

## Main results

* `CycleCutoff.sum_pushforward`: the total mass of `Φ_* ν` equals that of `ν`.
* `CycleCutoff.isProbVec_pushforward`: `Φ_* ν` is a probability vector when `ν` is.
* `CycleCutoff.expectation_comp`: `𝔼_ν[h ∘ Φ] = 𝔼_{Φ_* ν}[h]`.

## Implementation notes

The expectation identity holds for an arbitrary real weight vector `ν`; neither
non-negativity nor normalisation is used.
-/

public section

open Finset

namespace CycleCutoff

variable {Ω Y : Type*} [Fintype Ω] [Fintype Y]

/-- Push-forward preserves total mass: `∑_y (Φ_* ν)(y) = ∑_z ν(z)`. -/
theorem sum_pushforward (Φ : Ω → Y) (ν : Ω → ℝ) : ∑ y, pushforward Φ ν y = ∑ z, ν z := by
  classical
  simp only [pushforward]
  convert sum_fiberwise univ Φ ν

/-- The push-forward of a probability vector is a probability vector. -/
theorem isProbVec_pushforward {ν : Ω → ℝ} (hν : IsProbVec ν) (Φ : Ω → Y) :
    IsProbVec (pushforward Φ ν) where
  nonneg _ := sum_nonneg fun z _ => hν.nonneg z
  sum_eq_one := by rw [sum_pushforward, hν.sum_eq_one]

/-- **Expectation against a push-forward.** For a function `h ∘ Φ` factoring through `Φ`,
`𝔼_ν[h ∘ Φ] = 𝔼_{Φ_* ν}[h]`. -/
@[cycle_cutoff "lem_pushforward_expectation"]
theorem expectation_comp (ν : Ω → ℝ) (Φ : Ω → Y) (h : Y → ℝ) :
    expectation ν (fun z => h (Φ z)) = expectation (pushforward Φ ν) h := by
  classical
  simp only [expectation, pushforward, sum_mul]
  rw [← sum_fiberwise univ Φ (fun z => ν z * h (Φ z))]
  refine sum_congr rfl fun y _ => ?_
  convert sum_congr rfl fun z hz => ?_
  rw [(mem_filter.1 hz).2]

/-- The uniform measure on `α` pushed along an injection `Ψ : α → β` is the uniform measure on
`β` conditioned on the image of `Ψ`. -/
theorem pushforward_unif_of_injective {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    {Ψ : α → β} (hΨ : Function.Injective Ψ) :
    pushforward Ψ (unif α) = condMeasure (unif β) (univ.image Ψ) := by
  classical
  funext y
  simp only [pushforward, condMeasure, mass, unif_apply, sum_filter]
  by_cases hy : y ∈ univ.image Ψ
  · obtain ⟨p, -, rfl⟩ := mem_image.1 hy
    have : Nonempty β := ⟨Ψ p⟩
    have : Nonempty α := ⟨p⟩
    have hΩ : (Fintype.card β : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have hH : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    simp only [hΨ.eq_iff, sum_ite_eq', mem_univ, if_true, if_pos hy, sum_const,
      card_image_of_injective _ hΨ, card_univ, nsmul_eq_mul]
    field_simp
  · rw [if_neg hy, zero_div]
    exact sum_eq_zero fun q _ => if_neg fun h => hy (mem_image.2 ⟨q, mem_univ _, h⟩)

/-- The uniform measure pushed forward along a bijection is the uniform measure. -/
theorem pushforward_unif_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) :
    pushforward e (unif α) = unif β := by
  classical
  funext y
  have : (univ.filter fun z => e z = y) = {e.symm y} := by
    ext z
    simp [← Equiv.eq_symm_apply]
  simp only [pushforward, unif]
  rw [Finset.filter_congr_decidable, this, sum_singleton, Fintype.card_congr e]

end CycleCutoff
