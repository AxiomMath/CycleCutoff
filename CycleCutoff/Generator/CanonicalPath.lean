/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.Defs

/-!
# The canonical-path bound

Let `𝒯` be an involution family on a finite set `Ω` and `e₁, …, e_L` indices. For every
`f : Ω → ℝ`, moving along the path `T_{e_L} ∘ ⋯ ∘ T_{e₁}` changes `f`, in uniform mean square, by
at most `L` times the sum of the mean-square changes along the single steps:
`𝔼_u[(f ∘ T_{e_L} ∘ ⋯ ∘ T_{e₁} - f)²] ≤ L ∑_r 𝔼_u[(f ∘ T_{e_r} - f)²]`.

## Main results

* `CycleCutoff.expectation_unif_comp_of_bijective`: the uniform expectation is invariant under
  precomposition with a bijection of `Ω`.
* `CycleCutoff.InvFamily.bijective_foldl`: a composite of maps of an involution family is a
  bijection.
* `CycleCutoff.InvFamily.expectation_sq_foldl_sub_le`: the canonical-path bound.

## Implementation notes

The path `e₁, …, e_L` is a list `es`, and `T_{e_L} ∘ ⋯ ∘ T_{e₁}` is
`es.foldl (fun g e => 𝒯.T e ∘ g) id`. The empty path is allowed; both sides then vanish.
-/

public section

namespace CycleCutoff

/-- The uniform expectation is invariant under precomposition with a bijection. -/
theorem expectation_unif_comp_of_bijective {Ω : Type*} [Fintype Ω] {W : Ω → Ω}
    (hW : Function.Bijective W) (h : Ω → ℝ) :
    expectation (unif Ω) (fun z => h (W z)) = expectation (unif Ω) h := by
  rw [expectation_unif, expectation_unif]
  exact congrArg _ (Equiv.sum_comp (Equiv.ofBijective W hW) h)

/-- The composite `T_{e_L} ∘ ⋯ ∘ T_{e₁}` of maps of an involution family is a bijection. -/
theorem InvFamily.bijective_foldl {ι Ω : Type*} (𝒯 : InvFamily ι Ω) (es : List ι) :
    Function.Bijective (es.foldl (fun g e => 𝒯.T e ∘ g) id) := by
  induction es using List.reverseRecOn with
  | nil => exact Function.bijective_id
  | append_singleton l e ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact (𝒯.bijective e).comp ih

/-- **Canonical-path bound.** Along the path `T_{e_L} ∘ ⋯ ∘ T_{e₁}`,
`𝔼_u[(f ∘ T_{e_L} ∘ ⋯ ∘ T_{e₁} - f)²] ≤ L ∑_r 𝔼_u[(f ∘ T_{e_r} - f)²]`. -/
@[cycle_cutoff "lem_canonical_path"]
theorem InvFamily.expectation_sq_foldl_sub_le {ι Ω : Type*} [Fintype Ω] (𝒯 : InvFamily ι Ω)
    (es : List ι) (f : Ω → ℝ) :
    expectation (unif Ω) (fun z => (f (es.foldl (fun g e => 𝒯.T e ∘ g) id z) - f z) ^ 2) ≤
      es.length *
        (es.map fun e => expectation (unif Ω) (fun z => (f (𝒯.T e z) - f z) ^ 2)).sum := by
  have hu : ∀ z, 0 ≤ unif Ω z := fun z => by simp [unif_apply]
  induction es using List.reverseRecOn with
  | nil => simp
  | append_singleton l e ih =>
    set W := l.foldl (fun g e => 𝒯.T e ∘ g) id
    set c := expectation (unif Ω) (fun z => (f (𝒯.T e z) - f z) ^ 2)
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [List.length_append, List.length_singleton, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_singleton, Nat.cast_add, Nat.cast_one,
      Function.comp_apply]
    change expectation (unif Ω) (fun z => (f (𝒯.T e (W z)) - f z) ^ 2) ≤ _
    rcases Nat.eq_zero_or_pos l.length with hl | hl
    · rw [List.length_eq_zero_iff] at hl
      subst hl
      simp [W]
    have hc : expectation (unif Ω) (fun z => (f (𝒯.T e (W z)) - f (W z)) ^ 2) = c :=
      expectation_unif_comp_of_bijective (𝒯.bijective_foldl l) fun z => (f (𝒯.T e z) - f z) ^ 2
    set L : ℝ := (l.length : ℝ)
    have hL : 0 < L := by simp [L, hl]
    have key : expectation (unif Ω) (fun z => L * (f (𝒯.T e (W z)) - f z) ^ 2) ≤
        expectation (unif Ω) (fun z => L * (L + 1) * (f (𝒯.T e (W z)) - f (W z)) ^ 2 +
          (L + 1) * (f (W z) - f z) ^ 2) :=
      expectation_mono hu fun z => by
        nlinarith [sq_nonneg (L * (f (𝒯.T e (W z)) - f (W z)) - (f (W z) - f z))]
    rw [expectation_const_mul, expectation_add, expectation_const_mul, expectation_const_mul,
      hc] at key
    nlinarith

end CycleCutoff
