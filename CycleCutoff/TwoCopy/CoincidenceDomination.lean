/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.TwoCopy.BlackOneCopyLumping
public import CycleCutoff.TwoCopy.BlackMarginal
public import CycleCutoff.TwoCopy.BlackProjection
public import CycleCutoff.TwoCopy.BlackPsd
public import CycleCutoff.Generator.SemigroupLower

/-!
# Coincidence domination

For `t ≥ 0`, the second moment of the conditional law of the next exposed card is dominated by the
coincidence probability of the two-copy process: `𝔔_{n,m}(t) ≤ C_{n,m}(t)`.

## Main results

* `CycleCutoff.sq_sum_row_le_of_posSemidef`: For a real positive semidefinite matrix `G`,
  `(∑_j G y j)² ≤ G y y · ∑_{j,k} G j k`.
* `CycleCutoff.exposureSecondMoment_le_coincidenceProb`: `𝔔_{n,m}(t) ≤ C_{n,m}(t)` for `t ≥ 0`.

## Implementation notes

The hypotheses `n ≥ 3` and `1 ≤ m ≤ n` of the paper's statement are not needed.
-/

public section

open Finset Matrix

namespace CycleCutoff

/-- Cauchy–Schwarz for a positive semidefinite form, tested against a basis vector and the all-ones
vector: `(∑_j G y j)² ≤ G y y · ∑_{j,k} G j k`. -/
theorem sq_sum_row_le_of_posSemidef {ι : Type*} [Fintype ι] {G : Matrix ι ι ℝ}
    (hG : G.PosSemidef) (y : ι) :
    (∑ j, G y j) ^ 2 ≤ G y y * ∑ j, ∑ k, G j k := by
  classical
  have h := G.toBilin'.apply_sq_le_of_symm
    (fun x => by simpa [toBilin'_apply'] using hG.dotProduct_mulVec_nonneg x)
    (LinearMap.BilinForm.isSymm_iff.1 <| isSymm_toBilin'_iff_isSymm.2 <| by
      simpa [IsSymm, IsHermitian] using hG.1)
    (Pi.single y 1) fun _ => 1
  simpa [toBilin'_apply', dotProduct, mulVec, Pi.single_apply] using h

variable {n : ℕ} [NeZero n] {A : Finset (ZMod n)} {i : ZMod n}

/-- The fibre `agreeOff A σ` is the fibre of `σ' ↦ σ'|_{A^c}` through `σ`. -/
private theorem agreeOff_eq_filter_permRestrict (A : Finset (ZMod n)) (σ : Equiv.Perm (ZMod n)) :
    agreeOff A σ = univ.filter fun σ' => permRestrict A σ' = permRestrict A σ := by
  ext σ'
  simp only [mem_agreeOff, mem_filter, mem_univ, true_and]
  exact ⟨fun h => by ext a; exact h a a.2, fun h j hj => DFunLike.congr_fun h ⟨j, hj⟩⟩

/-- Summing over the fibres of `σ ↦ σ|_{A^c}`:
`∑_σ μ(σ) ∑_x 𝔲^μ_{A,i}(σ)(x)² = ∑_β ∑_x μ(σ|_{A^c} = β, σ(i) = x)² / μ(σ|_{A^c} = β)`. -/
private theorem sum_mul_sum_exposureLaw_sq (μ : Equiv.Perm (ZMod n) → ℝ) (A : Finset (ZMod n))
    (i : ZMod n) :
    ∑ σ, μ σ * ∑ x, exposureLaw μ A i σ x ^ 2 =
      ∑ β : BlackConfig n A, ∑ x, (∑ σ with permRestrict A σ = β ∧ σ i = x, μ σ) ^ 2 /
        ∑ σ with permRestrict A σ = β, μ σ := by
  rw [← sum_fiberwise univ (permRestrict A)]
  refine sum_congr rfl fun β _ => ?_
  have h : ∀ σ ∈ univ.filter (fun σ => permRestrict A σ = β), exposureLaw μ A i σ =
      fun x => (∑ σ with permRestrict A σ = β ∧ σ i = x, μ σ) /
        ∑ σ with permRestrict A σ = β, μ σ := fun σ hσ => funext fun x => by
    rw [exposureLaw_apply, mass, agreeOff_eq_filter_permRestrict, (mem_filter.1 hσ).2,
      filter_filter]
  rw [sum_congr rfl fun σ hσ => by rw [h σ hσ], ← sum_mul, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rcases eq_or_ne (∑ σ with permRestrict A σ = β, μ σ) 0 with h0 | h0
  · simp [h0]
  · field_simp

/-- The per-configuration Cauchy–Schwarz bound:
`∑_x M(β, x)² / m(β) ≤ ∑_{y ∈ R(β)} Γ(β, y, y)`. -/
private theorem sum_sq_div_le (hi : i ∈ A) {t : ℝ} (ht : 0 ≤ t) (β : BlackConfig n A) :
    ∑ x, (∑ σ with permRestrict A σ = β ∧ σ i = x, muT n t σ) ^ 2 /
        ∑ σ with permRestrict A σ = β, muT n t σ ≤
      ∑ y : ↥(blackRed β),
        (blackTwoCopy n A).semigroup t (blackTwoInit hi) ⟨(β, y, y), y.2, y.2⟩ := by
  set G : Matrix ↥(blackRed β) ↥(blackRed β) ℝ := Matrix.of fun y₁ y₂ =>
    (blackTwoCopy n A).semigroup t (blackTwoInit hi) ⟨(β, y₁, y₂), y₁.2, y₂.2⟩
  have hG : G.PosSemidef := posSemidef_blackTwoCopy_semigroup n A hi ht β
  have hM : ∀ y : ↥(blackRed β),
      ∑ σ with permRestrict A σ = β ∧ σ i = y, muT n t σ = ∑ j, G y j := fun y =>
    (sum_muT_permRestrict_eq n A hi t ⟨(β, y), y.2⟩).trans
      (sum_blackTwoCopy_semigroup_eq_blackOneCopy n A t (blackTwoInit hi) ⟨(β, y), y.2⟩).symm
  have hM0 : ∀ x ∉ blackRed β,
      ∑ σ with permRestrict A σ = β ∧ σ i = x, muT n t σ = 0 := by
    intro x hx
    refine sum_eq_zero fun σ hσ => absurd ?_ hx
    obtain ⟨rfl, rfl⟩ := (mem_filter.1 hσ).2
    refine mem_blackRed.2 fun a h => ?_
    rw [permRestrict_apply] at h
    exact a.2 (σ.injective h ▸ hi)
  have hsub : ∀ f : ZMod n → ℝ, (∀ x ∉ blackRed β, f x = 0) →
      ∑ x, f x = ∑ y : ↥(blackRed β), f y := fun f hf => by
    rw [sum_coe_sort]
    exact (sum_subset (subset_univ _) fun x _ hx => hf x hx).symm
  have hm : ∑ σ with permRestrict A σ = β, muT n t σ = ∑ y, ∑ j, G y j := by
    rw [← sum_fiberwise (univ.filter fun σ => permRestrict A σ = β) (fun σ => σ i)]
    simp only [filter_filter]
    rw [hsub _ hM0]
    exact sum_congr rfl fun y _ => hM y
  rw [hsub _ fun x hx => by rw [hM0 x hx, zero_pow two_ne_zero, zero_div], hm]
  simp only [hM]
  have hS : 0 ≤ ∑ y, ∑ j, G y j :=
    hm ▸ sum_nonneg fun σ _ => InvFamily.semigroup_apply_nonneg _ ht _ _
  exact sum_le_sum fun y _ =>
    div_le_of_le_mul₀ hS hG.diag_nonneg (sq_sum_row_le_of_posSemidef hG y)

/-- Projection of the diagonal of the black two-copy chain:
`∑_β ∑_{y ∈ R(β)} Γ(β, y, y) = ∑_{(R, x)} P^{𝒯_{n,m}}_t((A, i, i), (R, x, x))`. -/
private theorem sum_blackTwoCopy_diag_eq {m : ℕ} (hA : A.card = m) (hi : i ∈ A) (t : ℝ) :
    ∑ β : BlackConfig n A, ∑ y : ↥(blackRed β),
        (blackTwoCopy n A).semigroup t (blackTwoInit hi) ⟨(β, y, y), y.2, y.2⟩ =
      ∑ w' : TwoCopyState (ZMod n) m with w'.x = w'.y,
        (twoCopy n m).semigroup t ((blackTwoInit hi).proj hA) w' := by
  set Γ := (blackTwoCopy n A).semigroup t (blackTwoInit hi)
  simp only [← sum_blackTwoCopy_semigroup_eq_twoCopy n A m hA t (blackTwoInit hi)]
  trans ∑ w : BlackTwoState n A with w.1.2.1 = w.1.2.2, Γ w
  · rw [← sum_fiberwise (univ.filter fun w : BlackTwoState n A => w.1.2.1 = w.1.2.2)
      (fun w => w.1.1)]
    refine sum_congr rfl fun β _ => sum_bij (fun y _ => ⟨(β, y, y), y.2, y.2⟩) (fun y _ => by simp)
      (fun y _ y' _ h => Subtype.ext (congrArg (fun w : BlackTwoState n A => w.1.2.1) h)) ?_
      fun _ _ => rfl
    intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw
    obtain ⟨hd, rfl⟩ := hw
    exact ⟨⟨w.1.2.1, w.2.1⟩, mem_univ _, Subtype.ext (Prod.ext rfl (Prod.ext rfl hd))⟩
  · rw [sum_filter, sum_filter,
      ← sum_fiberwise univ (BlackTwoState.proj hA) (fun w => if w.1.2.1 = w.1.2.2 then Γ w else 0)]
    refine sum_congr rfl fun w' _ => ?_
    have hf : (univ.filter fun w : BlackTwoState n A =>
        blackRed w.1.1 = w'.R ∧ w.1.2.1 = w'.x ∧ w.1.2.2 = w'.y) =
        univ.filter fun w => w.proj hA = w' := by
      ext w
      simp [TwoCopyState.ext_iff']
    rw [hf]
    split_ifs with h
    · exact sum_congr rfl fun w hw => if_pos (by
        rw [← BlackTwoState.proj_x hA, ← BlackTwoState.proj_y hA, (mem_filter.1 hw).2, h])
    · exact sum_eq_zero fun w hw => if_neg fun hx => h (by
        rw [← (mem_filter.1 hw).2, BlackTwoState.proj_x, BlackTwoState.proj_y, hx])

/-- **Coincidence domination.** For `t ≥ 0`, `𝔔_{n,m}(t) ≤ C_{n,m}(t)`. -/
@[cycle_cutoff "lem_coincidence_domination"]
theorem exposureSecondMoment_le_coincidenceProb {n : ℕ} [NeZero n] {m : ℕ} {t : ℝ}
    (ht : 0 ≤ t) : exposureSecondMoment n m t ≤ coincidenceProb n m t := by
  set F : TwoCopyState (ZMod n) m → ℝ := fun w =>
    ∑ w' : TwoCopyState (ZMod n) m with w'.x = w'.y, (twoCopy n m).semigroup t w w'
  have hR : coincidenceProb n m t = ∑ A : Finset (ZMod n), ∑ i : ZMod n, exposureWeight n m A i *
      ∑ w ∈ ((univ.filter fun w : TwoCopyState (ZMod n) m => w.x = w.y).filter
        fun w => w.R = A).filter fun w => w.x = i, F w := by
    rw [coincidenceProb]
    symm
    calc _ = ∑ A : Finset (ZMod n), ∑ i : ZMod n,
          ∑ w ∈ ((univ.filter fun w : TwoCopyState (ZMod n) m => w.x = w.y).filter
            fun w => w.R = A).filter fun w => w.x = i, exposureWeight n m w.R w.x * F w := by
          refine sum_congr rfl fun A _ => sum_congr rfl fun i _ => ?_
          rw [mul_sum]
          exact sum_congr rfl fun w hw => by simp only [mem_filter] at hw; rw [hw.1.2, hw.2]
      _ = ∑ A : Finset (ZMod n), ∑ w ∈ (univ.filter fun w : TwoCopyState (ZMod n) m =>
            w.x = w.y).filter fun w => w.R = A, exposureWeight n m w.R w.x * F w :=
          sum_congr rfl fun A _ => sum_fiberwise _ _ _
      _ = _ := sum_fiberwise _ _ _
  rw [exposureSecondMoment, hR]
  refine sum_le_sum fun A _ => sum_le_sum fun i _ => ?_
  by_cases h : A.card = m ∧ i ∈ A
  · refine mul_le_mul_of_nonneg_left ?_ (exposureWeight_nonneg _ _ _)
    obtain ⟨hA, hi⟩ := h
    have hmem : (blackTwoInit hi).proj hA ∈ ((univ.filter fun w : TwoCopyState (ZMod n) m =>
        w.x = w.y).filter fun w => w.R = A).filter fun w => w.x = i := by
      simp [blackTwoInit]
    rw [sum_eq_single_of_mem _ hmem fun w hw hne => absurd ?_ hne,
      sum_mul_sum_exposureLaw_sq]
    · exact (sum_le_sum fun β _ => sum_sq_div_le hi ht β).trans_eq
        (sum_blackTwoCopy_diag_eq hA hi t)
    · simp only [mem_filter, mem_univ, true_and] at hw
      rw [TwoCopyState.ext_iff']
      simp [blackTwoInit, hw.1.2, hw.2, ← hw.1.1]
  · rw [exposureWeight_eq_zero h, zero_mul, zero_mul]

end CycleCutoff
