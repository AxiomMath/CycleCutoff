/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.OneCard.Defs
public import Mathlib.Data.Fintype.Powerset

/-!
# Random exposure and the prediction error

Card labels and positions are `ZMod n`. A uniformly random `m`-set `A` of labels, with a uniformly
random `i ∈ A`, is exposed; the conditional law of the position of card `i` given the positions of
the cards outside `A` is compared with a reference predictor.

## Main definitions

* `CycleCutoff.exposureWeight`: the weights `ζ_m(A, i) = 1[|A| = m, i ∈ A] / (binom(n, m) m)`.
* `CycleCutoff.agreeOff`: the permutations agreeing with `σ` off `A`, the fibre of `σ ↦ σ|_{A^c}`
  through `σ`.
* `CycleCutoff.exposureLaw`: the conditional law
  `𝔲^μ_{A,i}(σ)(x) = μ{σ' ∈ agreeOff A σ : σ'(i) = x} / μ(agreeOff A σ)`.
* `CycleCutoff.qHat`: the reference predictor `q̂^W_{i,R}(x) = W(i, x) / ∑_{y ∈ R} W(i, y)`.
* `CycleCutoff.predictionError`: the prediction error `𝔈_{n,m}(t)`.
* `CycleCutoff.exposureSecondMoment`: the second moment `𝔔_{n,m}(t)` of the conditional law.

## Main results

* `CycleCutoff.sum_exposureWeight`: the weights `ζ_m` sum to `1` for `1 ≤ m ≤ n`.
* `CycleCutoff.sum_exposureLaw`: for `i ∈ A`, `𝔲^μ_{A,i}(σ)` sums to `1` over `σ(A)`.
* `CycleCutoff.sum_mul_exposureLaw`: summing over the fibres of `σ ↦ σ|_{A^c}`,
  `∑_σ μ(σ) ∑_x 𝔲^μ_{A,i}(σ)(x) h(σ, x) = ∑_σ μ(σ) h(σ, σ(i))`.
-/

@[expose] public section

open Finset

namespace CycleCutoff

section Weights

variable (n : ℕ)

/-- The exposure weights `ζ_m(A, i) = 1[|A| = m, i ∈ A] / (binom(n, m) m)`: the law of a uniformly
random `m`-set `A` of labels together with a uniformly random `i ∈ A`. -/
@[cycle_cutoff "def_exposure_weights"]
noncomputable def exposureWeight (m : ℕ) (A : Finset (ZMod n)) (i : ZMod n) : ℝ :=
  if A.card = m ∧ i ∈ A then (((n.choose m : ℕ) : ℝ) * m)⁻¹ else 0

variable {n}

/-- The defining formula of the exposure weights. -/
theorem exposureWeight_apply (m : ℕ) (A : Finset (ZMod n)) (i : ZMod n) :
    exposureWeight n m A i =
      if A.card = m ∧ i ∈ A then (((n.choose m : ℕ) : ℝ) * m)⁻¹ else 0 := rfl

/-- For `|A| = m` and `i ∈ A`, `ζ_m(A, i) = (binom(n, m) m)⁻¹`. -/
theorem exposureWeight_of_mem {m : ℕ} {A : Finset (ZMod n)} {i : ZMod n} (hA : A.card = m)
    (hi : i ∈ A) : exposureWeight n m A i = (((n.choose m : ℕ) : ℝ) * m)⁻¹ := by
  simp [exposureWeight, hA, hi]

/-- `ζ_m(A, i) = 0` unless `|A| = m` and `i ∈ A`. -/
theorem exposureWeight_eq_zero {m : ℕ} {A : Finset (ZMod n)} {i : ZMod n}
    (h : ¬(A.card = m ∧ i ∈ A)) : exposureWeight n m A i = 0 := by
  simp only [exposureWeight, if_neg h]

/-- The exposure weights are nonnegative. -/
theorem exposureWeight_nonneg (m : ℕ) (A : Finset (ZMod n)) (i : ZMod n) :
    0 ≤ exposureWeight n m A i := by
  unfold exposureWeight
  split_ifs <;> positivity

variable [NeZero n]

/-- Sums against `ζ_m`:
`∑_{A,i} ζ_m(A,i) g(A,i) = (binom(n,m) m)⁻¹ ∑_{|A| = m} ∑_{i ∈ A} g(A,i)`. -/
theorem sum_exposureWeight_mul (m : ℕ) (g : Finset (ZMod n) → ZMod n → ℝ) :
    ∑ A : Finset (ZMod n), ∑ i : ZMod n, exposureWeight n m A i * g A i =
      (((n.choose m : ℕ) : ℝ) * m)⁻¹ * ∑ A : Finset (ZMod n) with A.card = m, ∑ i ∈ A, g A i := by
  rw [mul_sum, sum_filter]
  refine sum_congr rfl fun A _ => ?_
  split_ifs with hA
  · rw [mul_sum, ← sum_filter_add_sum_filter_not univ (· ∈ A)]
    rw [sum_eq_zero (s := filter (fun i => i ∉ A) univ) (fun i hi => by
      rw [exposureWeight_eq_zero (by simp_all)]; ring), add_zero, filter_mem_eq_inter,
      univ_inter]
    exact sum_congr rfl fun i hi => by rw [exposureWeight_of_mem hA hi]
  · exact sum_eq_zero fun i _ => by rw [exposureWeight_eq_zero (by tauto), zero_mul]

/-- The weights `ζ_m` sum to one for `1 ≤ m ≤ n`. -/
theorem sum_exposureWeight {m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∑ A : Finset (ZMod n), ∑ i : ZMod n, exposureWeight n m A i = 1 := by
  have h := sum_exposureWeight_mul (n := n) m (fun _ _ => 1)
  simp only [mul_one] at h
  rw [h]
  have hcard : ∀ A ∈ (univ.filter fun A : Finset (ZMod n) => A.card = m),
      ∑ i ∈ A, (1 : ℝ) = m := fun A hA => by simp [(mem_filter.1 hA).2]
  rw [sum_congr rfl hcard, sum_const, univ_filter_card_eq, card_powersetCard, Finset.card_univ,
    ZMod.card, nsmul_eq_mul]
  have h1 : (0 : ℝ) < n.choose m := by exact_mod_cast Nat.choose_pos hmn
  have h2 : (0 : ℝ) < m := by exact_mod_cast hm
  field_simp

end Weights

section Law

variable {n : ℕ} [NeZero n]

/-- The permutations agreeing with `σ` off `A`: `{σ' : σ'|_{A^c} = σ|_{A^c}}`, the fibre of
`σ ↦ σ|_{A^c}` through `σ`. -/
def agreeOff (A : Finset (ZMod n)) (σ : Equiv.Perm (ZMod n)) : Finset (Equiv.Perm (ZMod n)) :=
  {σ' | ∀ j ∉ A, σ' j = σ j}

/-- `σ' ∈ agreeOff A σ` if and only if `σ'` agrees with `σ` off `A`. -/
theorem mem_agreeOff {A : Finset (ZMod n)} {σ σ' : Equiv.Perm (ZMod n)} :
    σ' ∈ agreeOff A σ ↔ ∀ j ∉ A, σ' j = σ j := by
  simp [agreeOff]

/-- Every permutation lies in its own fibre. -/
theorem self_mem_agreeOff (A : Finset (ZMod n)) (σ : Equiv.Perm (ZMod n)) :
    σ ∈ agreeOff A σ :=
  mem_agreeOff.2 fun _ _ => rfl

/-- Agreeing off `A` is a symmetric relation. -/
theorem mem_agreeOff_comm {A : Finset (ZMod n)} {σ σ' : Equiv.Perm (ZMod n)} :
    σ' ∈ agreeOff A σ ↔ σ ∈ agreeOff A σ' := by
  simp only [mem_agreeOff]
  exact ⟨fun h j hj => (h j hj).symm, fun h j hj => (h j hj).symm⟩

/-- Two permutations agreeing off `A` have the same fibre. -/
theorem agreeOff_eq_of_mem {A : Finset (ZMod n)} {σ σ' : Equiv.Perm (ZMod n)}
    (h : σ' ∈ agreeOff A σ) : agreeOff A σ' = agreeOff A σ := by
  ext τ
  simp only [mem_agreeOff] at h ⊢
  exact ⟨fun hτ j hj => (hτ j hj).trans (h j hj), fun hτ j hj => (hτ j hj).trans (h j hj).symm⟩

/-- `agreeOff A σ` is the fibre through `σ` of the restriction `σ ↦ σ|_{A^c}`. -/
theorem agreeOff_eq_fiber (A : Finset (ZMod n)) (σ : Equiv.Perm (ZMod n)) :
    agreeOff A σ = fiber (fun (σ' : Equiv.Perm (ZMod n)) (j : {j // j ∉ A}) => σ' j) σ := by
  ext σ'
  rw [mem_agreeOff, mem_fiber]
  exact ⟨fun h => funext fun j => h j j.2, fun h j hj => congrFun h ⟨j, hj⟩⟩

/-- Agreeing off `univ` is no constraint: `agreeOff univ σ = univ`. -/
theorem agreeOff_univ (σ : Equiv.Perm (ZMod n)) : agreeOff univ σ = univ := by
  ext σ'
  simp [mem_agreeOff]

/-- Agreeing off `∅` means equality: `agreeOff ∅ σ = {σ}`. -/
theorem agreeOff_empty (σ : Equiv.Perm (ZMod n)) : agreeOff ∅ σ = {σ} := by
  ext σ'
  simp only [mem_agreeOff, notMem_empty, not_false_eq_true, forall_const, mem_singleton]
  exact ⟨Equiv.ext, fun h j => h ▸ rfl⟩

/-- Removing `i` from `A` refines the fibre by fixing the position of card `i`. -/
theorem agreeOff_erase {A : Finset (ZMod n)} {i : ZMod n} (hi : i ∈ A)
    (σ : Equiv.Perm (ZMod n)) :
    agreeOff (A.erase i) σ = (agreeOff A σ).filter (fun σ' => σ' i = σ i) := by
  ext σ'
  simp only [mem_filter, mem_agreeOff, mem_erase, not_and_or, ne_eq, not_not]
  constructor
  · intro h
    exact ⟨fun j hj => h j (Or.inr hj), h i (Or.inl rfl)⟩
  · rintro ⟨h, hi'⟩ j (rfl | hj)
    · exact hi'
    · exact h j hj

/-- A card of `A` sits, in any `σ'` agreeing with `σ` off `A`, at a position of `σ(A)`. -/
theorem apply_mem_image_of_mem_agreeOff {A : Finset (ZMod n)} {σ σ' : Equiv.Perm (ZMod n)}
    (h : σ' ∈ agreeOff A σ) {i : ZMod n} (hi : i ∈ A) : σ' i ∈ A.image σ := by
  rw [mem_agreeOff] at h
  rw [mem_image]
  by_contra hne
  push Not at hne
  have hA : σ.symm (σ' i) ∉ A := fun hA => hne _ hA (by simp)
  have := h _ hA
  rw [Equiv.apply_symm_apply] at this
  exact hA (by rw [σ'.injective this]; exact hi)

/-- Permutations agreeing off `A` send `A` to the same set of positions. -/
theorem image_eq_of_mem_agreeOff {A : Finset (ZMod n)} {σ σ' : Equiv.Perm (ZMod n)}
    (h : σ' ∈ agreeOff A σ) : A.image σ' = A.image σ := by
  have hsub : ∀ {τ τ' : Equiv.Perm (ZMod n)}, τ' ∈ agreeOff A τ → A.image τ' ⊆ A.image τ :=
    fun hτ x hx => by
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
      exact apply_mem_image_of_mem_agreeOff hτ ha
  exact Subset.antisymm (hsub h) (hsub (mem_agreeOff_comm.1 h))

omit [NeZero n] in
/-- A permutation preserves cardinalities: `|σ(A)| = |A|`. -/
theorem card_image_perm (A : Finset (ZMod n)) (σ : Equiv.Perm (ZMod n)) :
    (A.image σ).card = A.card :=
  card_image_of_injective A σ.injective

/-- The conditional law of the next exposed card:
`𝔲^μ_{A,i}(σ)(x) = μ{σ' : σ'(i) = x, σ'|_{A^c} = σ|_{A^c}} / μ{σ' : σ'|_{A^c} = σ|_{A^c}}`,
read as `0` when the denominator vanishes. -/
@[cycle_cutoff "def_exposure_law"]
noncomputable def exposureLaw (μ : Equiv.Perm (ZMod n) → ℝ) (A : Finset (ZMod n)) (i : ZMod n)
    (σ : Equiv.Perm (ZMod n)) (x : ZMod n) : ℝ :=
  (∑ σ' ∈ agreeOff A σ with σ' i = x, μ σ') / mass μ (agreeOff A σ)

/-- The defining formula of the conditional law. -/
theorem exposureLaw_apply (μ : Equiv.Perm (ZMod n) → ℝ) (A : Finset (ZMod n)) (i : ZMod n)
    (σ : Equiv.Perm (ZMod n)) (x : ZMod n) :
    exposureLaw μ A i σ x =
      (∑ σ' ∈ agreeOff A σ with σ' i = x, μ σ') / mass μ (agreeOff A σ) := rfl

/-- `𝔲^μ_{A,i}(σ)` depends on `σ` only through `σ|_{A^c}`. -/
theorem exposureLaw_eq_of_mem_agreeOff (μ : Equiv.Perm (ZMod n) → ℝ) {A : Finset (ZMod n)}
    (i : ZMod n) {σ σ' : Equiv.Perm (ZMod n)} (h : σ' ∈ agreeOff A σ) :
    exposureLaw μ A i σ' = exposureLaw μ A i σ := by
  funext x
  simp only [exposureLaw, agreeOff_eq_of_mem h]

/-- For `μ ≥ 0`, the conditional law is nonnegative. -/
theorem exposureLaw_nonneg {μ : Equiv.Perm (ZMod n) → ℝ} (hμ : ∀ σ, 0 ≤ μ σ)
    (A : Finset (ZMod n)) (i : ZMod n) (σ : Equiv.Perm (ZMod n)) (x : ZMod n) :
    0 ≤ exposureLaw μ A i σ x :=
  div_nonneg (sum_nonneg fun _ _ => hμ _) (sum_nonneg fun _ _ => hμ _)

/-- For `i ∈ A`, `𝔲^μ_{A,i}(σ)` vanishes off `σ(A)`. -/
theorem exposureLaw_eq_zero_of_notMem (μ : Equiv.Perm (ZMod n) → ℝ) {A : Finset (ZMod n)}
    {i : ZMod n} (hi : i ∈ A) (σ : Equiv.Perm (ZMod n)) {x : ZMod n} (hx : x ∉ A.image σ) :
    exposureLaw μ A i σ x = 0 := by
  rw [exposureLaw, sum_eq_zero, zero_div]
  intro σ' hσ'
  rw [mem_filter] at hσ'
  exact absurd (hσ'.2 ▸ apply_mem_image_of_mem_agreeOff hσ'.1 hi) hx

/-- For `i ∈ A` and a non-null fibre, `𝔲^μ_{A,i}(σ)` sums to one over `σ(A)`. -/
theorem sum_exposureLaw (μ : Equiv.Perm (ZMod n) → ℝ) {A : Finset (ZMod n)} {i : ZMod n}
    (hi : i ∈ A) (σ : Equiv.Perm (ZMod n)) (hσ : mass μ (agreeOff A σ) ≠ 0) :
    ∑ x ∈ A.image σ, exposureLaw μ A i σ x = 1 := by
  simp only [exposureLaw, ← sum_div]
  rw [sum_fiberwise_of_maps_to (fun σ' hσ' => apply_mem_image_of_mem_agreeOff hσ' hi)]
  exact div_self hσ

/-- For `i ∈ A`, `∑_x 𝔲^μ_{A,i}(σ)(x) f(x)` over all positions equals the sum over `σ(A)`. -/
theorem sum_univ_exposureLaw_mul (μ : Equiv.Perm (ZMod n) → ℝ) {A : Finset (ZMod n)}
    {i : ZMod n} (hi : i ∈ A) (σ : Equiv.Perm (ZMod n)) (f : ZMod n → ℝ) :
    ∑ x, exposureLaw μ A i σ x * f x = ∑ x ∈ A.image σ, exposureLaw μ A i σ x * f x := by
  refine (sum_subset (subset_univ _) fun x _ hx => ?_).symm
  rw [exposureLaw_eq_zero_of_notMem μ hi σ hx, zero_mul]

/-- **Summing over the fibres of `σ ↦ σ|_{A^c}`.** For `μ ≥ 0` and `h` constant on those fibres,
`∑_σ μ(σ) ∑_x 𝔲^μ_{A,i}(σ)(x) h(σ, x) = ∑_σ μ(σ) h(σ, σ(i))`. -/
theorem sum_mul_exposureLaw {μ : Equiv.Perm (ZMod n) → ℝ} (hμ : ∀ σ, 0 ≤ μ σ)
    (A : Finset (ZMod n)) (i : ZMod n) (h : Equiv.Perm (ZMod n) → ZMod n → ℝ)
    (hh : ∀ σ σ', σ' ∈ agreeOff A σ → h σ' = h σ) :
    ∑ σ, μ σ * ∑ x, exposureLaw μ A i σ x * h σ x = ∑ σ, μ σ * h σ (σ i) := by
  have h1 : ∀ σ, μ σ * ∑ x, exposureLaw μ A i σ x * h σ x =
      ∑ σ' ∈ agreeOff A σ, μ σ * μ σ' * h σ' (σ' i) / mass μ (agreeOff A σ) := by
    intro σ
    simp only [exposureLaw, div_mul_eq_mul_div, sum_mul, ← sum_div]
    have hsw : ∑ x, ∑ σ' ∈ agreeOff A σ with σ' i = x, μ σ' * h σ x =
        ∑ σ' ∈ agreeOff A σ, μ σ' * h σ' (σ' i) := by
      rw [← sum_fiberwise (agreeOff A σ) (fun σ' => σ' i) (fun σ' => μ σ' * h σ' (σ' i))]
      refine sum_congr rfl fun x _ => sum_congr rfl fun σ' hσ' => ?_
      rw [mem_filter] at hσ'
      rw [hh σ σ' hσ'.1, hσ'.2]
    rw [hsw, ← mul_div_assoc, mul_sum]
    congr 1
    exact sum_congr rfl fun _ _ => by ring
  simp only [h1]
  rw [sum_comm' (t' := univ) (s' := fun σ' => agreeOff A σ')
    (h := fun σ σ' => by simp [mem_agreeOff_comm])]
  refine sum_congr rfl fun σ' _ => ?_
  have h2 : ∀ σ ∈ agreeOff A σ',
      μ σ * μ σ' * h σ' (σ' i) / mass μ (agreeOff A σ) =
        μ σ * (μ σ' * h σ' (σ' i) / mass μ (agreeOff A σ')) := fun σ hσ => by
    rw [agreeOff_eq_of_mem (mem_agreeOff_comm.1 hσ)]
    ring
  rw [sum_congr rfl h2, ← sum_mul]
  change mass μ (agreeOff A σ') * _ = _
  by_cases hm : mass μ (agreeOff A σ') = 0
  · have hμ0 : μ σ' = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun τ _ => hμ τ)).1 hm σ' (self_mem_agreeOff A σ')
    simp [hμ0, hm]
  · field_simp

end Law

section Predictor

variable {n : ℕ}

/-- The reference predictor `q̂^W_{i,R}(x) = W(i, x) / ∑_{y ∈ R} W(i, y)`. -/
@[cycle_cutoff "def_q_hat"]
noncomputable def qHat (W : ZMod n → ZMod n → ℝ) (i : ZMod n) (R : Finset (ZMod n))
    (x : ZMod n) : ℝ :=
  W i x / ∑ y ∈ R, W i y

/-- The defining formula of the reference predictor. -/
theorem qHat_apply (W : ZMod n → ZMod n → ℝ) (i : ZMod n) (R : Finset (ZMod n)) (x : ZMod n) :
    qHat W i R x = W i x / ∑ y ∈ R, W i y := rfl

end Predictor

section Error

variable (n : ℕ) [NeZero n]

/-- The prediction error
`𝔈_{n,m}(t) = ∑_{A,i} ζ_m(A,i) ∑_σ μ_t(σ) ∑_{x ∈ σ(A)} (𝔲^{μ_t}_{A,i}(σ)(x) - (n/m) p_t(i,x))²`. -/
@[cycle_cutoff "def_pred_error"]
noncomputable def predictionError (m : ℕ) (t : ℝ) : ℝ :=
  ∑ A : Finset (ZMod n), ∑ i : ZMod n, exposureWeight n m A i *
    ∑ σ : Equiv.Perm (ZMod n), muT n t σ *
      ∑ x ∈ A.image σ, (exposureLaw (muT n t) A i σ x - n / m * heatKernel n t i x) ^ 2

/-- The second moment of the conditional law
`𝔔_{n,m}(t) = ∑_{A,i} ζ_m(A,i) ∑_σ μ_t(σ) ∑_x 𝔲^{μ_t}_{A,i}(σ)(x)²`. -/
@[cycle_cutoff "def_Qnm"]
noncomputable def exposureSecondMoment (m : ℕ) (t : ℝ) : ℝ :=
  ∑ A : Finset (ZMod n), ∑ i : ZMod n, exposureWeight n m A i *
    ∑ σ : Equiv.Perm (ZMod n), muT n t σ * ∑ x : ZMod n, exposureLaw (muT n t) A i σ x ^ 2

end Error

end CycleCutoff
