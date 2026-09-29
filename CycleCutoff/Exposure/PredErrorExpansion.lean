/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Exposure.Defs
public import CycleCutoff.Cycle.MuPositive
public import CycleCutoff.FiniteProbability.SampleSumVariance
public import CycleCutoff.OneCard.OneCard
public import CycleCutoff.OneCard.HeatTranslation
public import CycleCutoff.Generator.SemigroupLower
public import CycleCutoff.Generator.SemigroupRowsum

/-!
# Expansion of the prediction error

For `2 ≤ n`, `1 ≤ m ≤ n` and `t ≥ 0`, expanding the square in the prediction error gives
`𝔈_{n,m}(t) = 𝔔_{n,m}(t) - (2n/m) S₂(t)
  + (n/m)² ((m-1)/(n-1) S₂(t) + (n-m)/(n-1) S₃(t))`.

## Main results

* `CycleCutoff.predictionError_eq`: the expansion of `𝔈_{n,m}(t)`.
-/

public section

open Finset

namespace CycleCutoff

variable {n : ℕ} [NeZero n]

private lemma sum_heatKernel_sq (t : ℝ) (i : ZMod n) :
    ∑ x, heatKernel n t i x ^ 2 = S2 n t :=
  sum_comp_heatKernel n t i (· ^ 2)

private lemma sum_heatKernel_cube (t : ℝ) (i : ZMod n) :
    ∑ x, heatKernel n t i x ^ 3 = S3 n t :=
  sum_comp_heatKernel n t i (· ^ 3)

/-- Counting the `m`-sets of labels containing `i` and `a`, normalised by `n (n - 1)`. -/
private lemma card_filter_mem_mem {m : ℕ} (hmn : m ≤ n) (i a : ZMod n) :
    (#{A : Finset (ZMod n) | A.card = m ∧ i ∈ A ∧ a ∈ A} : ℝ) * (n * (n - 1)) =
      (n.choose m : ℕ) * m * (if a = i then (n : ℝ) - 1 else (m : ℝ) - 1) := by
  have hm : m ≤ Fintype.card (ZMod n) := by rwa [ZMod.card]
  have hfilt : ({A : Finset (ZMod n) | A.card = m ∧ i ∈ A ∧ a ∈ A} : Finset _) =
      (univ.powersetCard m).filter (fun A => i ∈ A ∧ a ∈ A) := by
    ext A; simp [mem_powersetCard]
  rw [hfilt]
  split_ifs with hai
  · subst hai
    have h := card_filter_mem_mul m hm a
    simp only [and_self]
    rw [ZMod.card] at h
    linear_combination ((n : ℝ) - 1) * h
  · have h := card_filter_mem_mem_mul m hm (Ne.symm hai)
    rw [ZMod.card] at h
    linear_combination h

/-- Double sums over a uniform `m`-set: diagonal and off-diagonal pairs are counted separately. -/
private lemma sum_card_eq_sum_mem_sum_mem {m : ℕ} (hmn : m ≤ n)
    (G : ZMod n → ZMod n → ℝ) :
    (n : ℝ) * (n - 1) * ∑ A : Finset (ZMod n) with A.card = m, ∑ i ∈ A, ∑ a ∈ A, G i a =
      (n.choose m : ℕ) * m * ((n - m) * ∑ i, G i i + (m - 1) * ∑ i, ∑ a, G i a) := by
  have h1 : ∑ A : Finset (ZMod n) with A.card = m, ∑ i ∈ A, ∑ a ∈ A, G i a =
      ∑ i, ∑ a, (#{A : Finset (ZMod n) | A.card = m ∧ i ∈ A ∧ a ∈ A} : ℝ) * G i a := by
    calc ∑ A : Finset (ZMod n) with A.card = m, ∑ i ∈ A, ∑ a ∈ A, G i a
        = ∑ A : Finset (ZMod n) with A.card = m, ∑ i, ∑ a,
            if i ∈ A ∧ a ∈ A then G i a else 0 := by
          refine sum_congr rfl fun A _ => ?_
          simp only [ite_and, sum_ite_irrel, sum_const_zero, sum_ite_mem, univ_inter]
      _ = ∑ i, ∑ a, ∑ A : Finset (ZMod n) with A.card = m,
            if i ∈ A ∧ a ∈ A then G i a else 0 := by
          rw [sum_comm]
          refine sum_congr rfl fun i _ => ?_
          rw [sum_comm]
      _ = _ := by
          refine sum_congr rfl fun i _ => sum_congr rfl fun a _ => ?_
          rw [← sum_filter, filter_filter, sum_const, nsmul_eq_mul]
  rw [h1, mul_sum]
  trans ∑ i, ((n.choose m : ℕ) : ℝ) * m *
    (((n : ℝ) - m) * G i i + ((m : ℝ) - 1) * ∑ a, G i a)
  swap
  · rw [← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  have h2 : ∀ a, (n : ℝ) * (n - 1) *
      ((#{A : Finset (ZMod n) | A.card = m ∧ i ∈ A ∧ a ∈ A} : ℝ) * G i a) =
      (n.choose m : ℕ) * m *
        (((m : ℝ) - 1) * G i a + ((n : ℝ) - m) * if a = i then G i a else 0) := by
    intro a
    rw [← mul_assoc, mul_comm _ (#_ : ℝ), card_filter_mem_mem hmn i a]
    split_ifs <;> ring
  rw [sum_congr rfl fun a _ => h2 a, ← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum,
    sum_ite_eq' univ i]
  simp only [mem_univ, if_true]
  ring

/-- The square term: `∑_{A,i} ζ_m ∑_σ μ_t(σ) ∑_{x ∈ σ(A)} p_t(i, x)²
= (m-1)/(n-1) S₂ + (n-m)/(n-1) S₃`. -/
private lemma sum_exposureWeight_mul_sum_image_heatKernel_sq (hn : 2 ≤ n) {m : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) (t : ℝ) :
    ∑ A : Finset (ZMod n), ∑ i, exposureWeight n m A i *
        ∑ σ, muT n t σ * ∑ x ∈ A.image σ, heatKernel n t i x ^ 2 =
      ((m : ℝ) - 1) / ((n : ℝ) - 1) * S2 n t + ((n : ℝ) - m) / ((n : ℝ) - 1) * S3 n t := by
  rw [sum_exposureWeight_mul]
  have h1 : ∑ A : Finset (ZMod n) with A.card = m, ∑ i ∈ A,
        ∑ σ, muT n t σ * ∑ x ∈ A.image σ, heatKernel n t i x ^ 2 =
      ∑ σ, muT n t σ * ∑ A : Finset (ZMod n) with A.card = m, ∑ i ∈ A, ∑ a ∈ A,
        heatKernel n t i (σ a) ^ 2 := by
    have himg : ∀ (σ : Equiv.Perm (ZMod n)) (A : Finset (ZMod n)) (f : ZMod n → ℝ),
        ∑ x ∈ A.image σ, f x = ∑ a ∈ A, f (σ a) := fun σ A f =>
      sum_image fun x _ y _ h => σ.injective h
    simp only [himg, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun A _ => ?_
    rw [sum_comm]
  rw [h1]
  have h2 : ∀ σ : Equiv.Perm (ZMod n), (n : ℝ) * (n - 1) *
      ∑ A : Finset (ZMod n) with A.card = m, ∑ i ∈ A, ∑ a ∈ A, heatKernel n t i (σ a) ^ 2 =
      (n.choose m : ℕ) * m * ((n - m) * ∑ i, heatKernel n t i (σ i) ^ 2 +
        (m - 1) * (n * S2 n t)) := by
    intro σ
    rw [sum_card_eq_sum_mem_sum_mem hmn]
    congr 3
    have : ∀ i, ∑ a, heatKernel n t i (σ a) ^ 2 = S2 n t := fun i => by
      rw [Equiv.sum_comp σ (fun x => heatKernel n t i x ^ 2), sum_heatKernel_sq]
    rw [sum_congr rfl fun i _ => this i, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  have h3 : ∑ σ : Equiv.Perm (ZMod n), muT n t σ * ∑ i, heatKernel n t i (σ i) ^ 2 =
      n * S3 n t := by
    simp only [mul_sum]
    rw [sum_comm]
    have : ∀ i : ZMod n, ∑ σ : Equiv.Perm (ZMod n), muT n t σ * heatKernel n t i (σ i) ^ 2 =
        S3 n t := fun i => by
      rw [sum_muT_mul_apply t i (fun x => heatKernel n t i x ^ 2), ← sum_heatKernel_cube t i]
      exact sum_congr rfl fun x _ => by ring
    rw [sum_congr rfl fun i _ => this i, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  have hY : (n : ℝ) * (n - 1) * ∑ σ, muT n t σ *
      ∑ A : Finset (ZMod n) with A.card = m, ∑ i ∈ A, ∑ a ∈ A, heatKernel n t i (σ a) ^ 2 =
      (n.choose m : ℕ) * m * ((n - m) * (n * S3 n t) + (m - 1) * (n * S2 n t)) := by
    rw [mul_sum]
    simp only [mul_left_comm ((n : ℝ) * (n - 1)), h2]
    have e : ∀ σ : Equiv.Perm (ZMod n), muT n t σ * ((n.choose m : ℕ) * m *
        ((n - m) * ∑ i, heatKernel n t i (σ i) ^ 2 + (m - 1) * (n * S2 n t))) =
        (n.choose m : ℕ) * m * (n - m) * (muT n t σ * ∑ i, heatKernel n t i (σ i) ^ 2) +
          (n.choose m : ℕ) * m * ((m - 1) * (n * S2 n t)) * muT n t σ := fun σ => by ring
    rw [sum_congr rfl fun σ _ => e σ, sum_add_distrib, ← mul_sum, ← mul_sum, h3, sum_muT]
    ring
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hC : ((n.choose m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmn).ne'
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  rw [eq_div_of_mul_eq (mul_ne_zero hn0 hn1) ((mul_comm _ _).trans hY)]
  field_simp
  ring

/-- The cross term: `∑_σ μ_t(σ) ∑_x 𝔲(σ)(x) p_t(i, x) = S₂(t)`, by summing over the fibres of
`σ ↦ σ|_{A^c}`. -/
private lemma sum_muT_mul_sum_exposureLaw_mul_heatKernel {t : ℝ} (ht : 0 ≤ t)
    (A : Finset (ZMod n)) (i : ZMod n) :
    ∑ σ, muT n t σ * ∑ x, exposureLaw (muT n t) A i σ x * heatKernel n t i x = S2 n t := by
  rw [sum_mul_exposureLaw (muT_nonneg ht) A i (fun _ x => heatKernel n t i x)
    (fun _ _ _ => rfl), sum_muT_mul_apply t i (heatKernel n t i), ← sum_heatKernel_sq t i]
  exact sum_congr rfl fun _ _ => (pow_two _).symm

/-- Expanding the square inside the prediction error, for `i ∈ A`. -/
private lemma sum_image_sub_sq {μ : Equiv.Perm (ZMod n) → ℝ} {A : Finset (ZMod n)}
    {i : ZMod n} (hi : i ∈ A) (σ : Equiv.Perm (ZMod n)) (c : ℝ) (q : ZMod n → ℝ) :
    ∑ x ∈ A.image σ, (exposureLaw μ A i σ x - c * q x) ^ 2 =
      ∑ x, exposureLaw μ A i σ x ^ 2 - 2 * c * ∑ x, exposureLaw μ A i σ x * q x +
        c ^ 2 * ∑ x ∈ A.image σ, q x ^ 2 := by
  have hu := sum_univ_exposureLaw_mul μ hi σ (exposureLaw μ A i σ)
  simp only [← pow_two] at hu
  rw [hu, sum_univ_exposureLaw_mul μ hi σ q, mul_sum, mul_sum, ← sum_sub_distrib,
    ← sum_add_distrib]
  exact sum_congr rfl fun _ _ => by ring

/-- **Expansion of the prediction error.** For `2 ≤ n`, `1 ≤ m ≤ n` and `t ≥ 0`,
`𝔈_{n,m}(t) = 𝔔_{n,m}(t) - (2n/m) S₂(t)
  + (n/m)² ((m-1)/(n-1) S₂(t) + (n-m)/(n-1) S₃(t))`. -/
@[cycle_cutoff "lem_pred_error_expansion"]
theorem predictionError_eq (hn : 2 ≤ n) {m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) {t : ℝ}
    (ht : 0 ≤ t) :
    predictionError n m t =
      exposureSecondMoment n m t - 2 * n / m * S2 n t +
        ((n : ℝ) / m) ^ 2 *
          (((m : ℝ) - 1) / ((n : ℝ) - 1) * S2 n t + ((n : ℝ) - m) / ((n : ℝ) - 1) * S3 n t) := by
  set c : ℝ := n / m
  have key : ∀ (A : Finset (ZMod n)) (i : ZMod n), exposureWeight n m A i *
      ∑ σ, muT n t σ * ∑ x ∈ A.image σ, (exposureLaw (muT n t) A i σ x -
        c * heatKernel n t i x) ^ 2 =
      exposureWeight n m A i *
          ∑ σ, muT n t σ * ∑ x, exposureLaw (muT n t) A i σ x ^ 2 -
        2 * c * (exposureWeight n m A i * S2 n t) +
        c ^ 2 * (exposureWeight n m A i *
          ∑ σ, muT n t σ * ∑ x ∈ A.image σ, heatKernel n t i x ^ 2) := by
    intro A i
    by_cases h : A.card = m ∧ i ∈ A
    · rw [← sum_muT_mul_sum_exposureLaw_mul_heatKernel ht A i]
      have e : ∀ σ : Equiv.Perm (ZMod n), muT n t σ * ∑ x ∈ A.image σ,
          (exposureLaw (muT n t) A i σ x - c * heatKernel n t i x) ^ 2 =
          muT n t σ * ∑ x, exposureLaw (muT n t) A i σ x ^ 2 -
            2 * c * (muT n t σ * ∑ x, exposureLaw (muT n t) A i σ x * heatKernel n t i x) +
            c ^ 2 * (muT n t σ * ∑ x ∈ A.image σ, heatKernel n t i x ^ 2) := fun σ => by
        rw [sum_image_sub_sq h.2]
        ring
      rw [sum_congr rfl fun σ _ => e σ, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
      ring
    · simp [exposureWeight_eq_zero h]
  rw [predictionError, sum_congr rfl fun A _ => sum_congr rfl fun i _ => key A i]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul]
  rw [sum_exposureWeight hm hmn, sum_exposureWeight_mul_sum_image_heatKernel_sq hn hm hmn t,
    exposureSecondMoment]
  ring

end CycleCutoff
