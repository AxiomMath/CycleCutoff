/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Exposure.ExposureBound
public import CycleCutoff.OneCard.OneCard
public import CycleCutoff.OneCard.HeatTranslation
public import CycleCutoff.OneCard.HeatUniform
public import CycleCutoff.OneCard.DeltaInvolution
public import CycleCutoff.OneCard.BIntegrandNonneg
public import CycleCutoff.Cycle.MuPositive
public import CycleCutoff.Cycle.LambdaLower
public import CycleCutoff.Generator.SemigroupRowsum
public import CycleCutoff.FiniteProbability.UnnormalizedKL

/-!
# The entropy of the shuffle is controlled by the prediction errors

For `n ≥ 3` and `t ≥ a₀ / λ_n`,
`H(μ_t | π_n) ≤ n h(t) + 3 (1 + log n) + 2 ∑_{m=1}^n m 𝔈_{n,m}(t)`.

## Main results

* `CycleCutoff.relEnt_muT_le`: the entropy–prediction error bound.
-/

public section

open Finset Real

namespace CycleCutoff

variable {n : ℕ} [NeZero n]

/-- The one-card term: `𝔼_{μ_t}[log(n p_t(i, σ(i)))] = h(t)`. -/
private lemma expectation_log_heatKernel (t : ℝ) (i : ZMod n) :
    expectation (muT n t) (fun σ => Real.log ((n : ℝ) * heatKernel n t i (σ i))) =
      oneCardEntropy n t := by
  rw [expectation, sum_muT_mul_apply t i (fun x => Real.log ((n : ℝ) * heatKernel n t i x)),
    oneCardEntropy]
  exact sum_comp_heatKernel n t i fun p => p * Real.log ((n : ℝ) * p)

/-- The relative entropy term on `R = σ(A)`, for `|A| = m`, `i ∈ A` and `n p_t ≥ 1/2`:
`H(𝔲 | q̂^W_{i,R}) ≤ 2m ∑_{x ∈ R} (𝔲(x) - (n/m) p_t(i, x))²`. -/
private lemma relEnt_exposureLaw_le {t : ℝ} (ht : a0 / lambdaN n ≤ t) (ht0 : 0 < t)
    {A : Finset (ZMod n)} {i : ZMod n} (hi : i ∈ A) (σ : Equiv.Perm (ZMod n)) :
    relEnt (fun x : A.image σ => exposureLaw (muT n t) A i σ x)
        (fun x : A.image σ =>
          qHat (fun i x => (n : ℝ) * heatKernel n t i x) i (A.image σ) x) ≤
      2 * A.card * ∑ x ∈ A.image σ,
        (exposureLaw (muT n t) A i σ x - n / A.card * heatKernel n t i x) ^ 2 := by
  set R := A.image σ
  set m : ℝ := (A.card : ℝ) with hm
  set u := exposureLaw (muT n t) A i σ
  have hm0 : 0 < m := by rw [hm]; exact_mod_cast card_pos.2 ⟨i, hi⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hpos := muT_pos (n := n) ht0
  have hmass : mass (muT n t) (agreeOff A σ) ≠ 0 :=
    (mass_pos_of_pos hpos ⟨σ, self_mem_agreeOff A σ⟩).ne'
  have hU : IsProbVec (fun x : R => u x) :=
    ⟨fun x => exposureLaw_nonneg (fun σ => (hpos σ).le) _ _ _ _,
      by rw [sum_coe_sort R u]; exact sum_exposureLaw _ hi σ hmass⟩
  set v : R → ℝ := fun x => n / m * heatKernel n t i x with hv
  have hW := one_half_le_mul_heatKernel_and_le ht i
  have hv2 : ∀ x, 1 ≤ 2 * m * v x := fun x => by
    have : 2 * m * v x = 2 * ((n : ℝ) * heatKernel n t i x) := by
      rw [hv]; field_simp
    rw [this]; linarith [(hW x).1]
  have hvpos : ∀ x, 0 < v x := fun x => by
    have := hv2 x
    by_contra h
    push Not at h
    nlinarith
  have hq : (fun x : R => qHat (fun i x => (n : ℝ) * heatKernel n t i x) i R x) =
      fun x => v x / ∑ y, v y := by
    funext x
    rw [qHat_apply, hv]
    simp only
    rw [← mul_sum, ← mul_sum, sum_coe_sort R (fun y => heatKernel n t i y),
      mul_div_mul_left _ _ hn0.ne', mul_div_mul_left _ _ (div_pos hn0 hm0).ne']
  rw [hq]
  refine (relEnt_div_sum_le _ hU v hvpos).trans ?_
  rw [← sum_coe_sort R (fun x => (u x - n / m * heatKernel n t i x) ^ 2), mul_sum]
  refine sum_le_sum fun x _ => ?_
  rw [div_le_iff₀ (hvpos x)]
  have h0 : 0 ≤ (u x - v x) ^ 2 := sq_nonneg _
  change (u x - v x) ^ 2 ≤ 2 * m * (u x - v x) ^ 2 * v x
  nlinarith [hv2 x]

/-- **The entropy–prediction error bound**: for `n ≥ 3` and `t ≥ a₀ / λ_n`,
`H(μ_t | π_n) ≤ n h(t) + 3 (1 + log n) + 2 ∑_{m=1}^n m 𝔈_{n,m}(t)`. -/
@[cycle_cutoff "prop_entropy_error"]
theorem relEnt_muT_le (hn : 3 ≤ n) {t : ℝ} (ht : a0 / lambdaN n ≤ t) :
    relEnt (muT n t) (unif (Equiv.Perm (ZMod n))) ≤
      n * oneCardEntropy n t + 3 * (1 + Real.log n) +
        2 * ∑ m ∈ Icc 1 n, (m : ℝ) * predictionError n m t := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlam : 0 < lambdaN n :=
    lt_of_lt_of_le (by positivity) (sixteen_div_sq_le_lambdaN (by omega))
  have ht0 : 0 < t := lt_of_lt_of_le (div_pos (by norm_num [a0]) hlam) ht
  set W : ZMod n → ZMod n → ℝ := fun i x => (n : ℝ) * heatKernel n t i x with hWdef
  have hrow : ∀ i, ∑ x, W i x = n := fun i => by
    rw [hWdef]; simp only; rw [← mul_sum, sum_heatKernel, mul_one]
  have key := relEnt_unif_le_exposure hn W (one_half_le_mul_heatKernel_and_le ht) hrow
    (muT n t) (isProbVec_muT ht0.le) (muT_pos ht0)
  refine key.trans ?_
  have hone : ∑ i : ZMod n, expectation (muT n t) (fun σ => Real.log (W i (σ i))) =
      n * oneCardEntropy n t := by
    simp only [hWdef, expectation_log_heatKernel, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  rw [hone]
  have hKL : ∑ m ∈ Icc 1 n, ∑ A : Finset (ZMod n), ∑ i : ZMod n, exposureWeight n m A i *
        ∑ σ : Equiv.Perm (ZMod n), muT n t σ *
          relEnt (fun x : A.image σ => exposureLaw (muT n t) A i σ x)
            (fun x : A.image σ => qHat W i (A.image σ) x) ≤
      2 * ∑ m ∈ Icc 1 n, (m : ℝ) * predictionError n m t := by
    rw [mul_sum]
    refine sum_le_sum fun m _ => ?_
    rw [predictionError, mul_sum, mul_sum]
    refine sum_le_sum fun A _ => ?_
    rw [mul_sum, mul_sum]
    refine sum_le_sum fun i _ => ?_
    by_cases h : A.card = m ∧ i ∈ A
    · obtain ⟨rfl, hi⟩ := h
      have hw := exposureWeight_nonneg (n := n) A.card A i
      set F : Equiv.Perm (ZMod n) → ℝ := fun σ => ∑ x ∈ A.image σ,
        (exposureLaw (muT n t) A i σ x - n / A.card * heatKernel n t i x) ^ 2
      have hσ : ∑ σ, muT n t σ * relEnt (fun x : A.image σ => exposureLaw (muT n t) A i σ x)
            (fun x : A.image σ => qHat W i (A.image σ) x) ≤
          ∑ σ, muT n t σ * (2 * A.card * F σ) :=
        sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_left (relEnt_exposureLaw_le ht ht0 hi σ) (muT_pos ht0 σ).le
      have hsum : ∑ σ, muT n t σ * (2 * A.card * F σ) = 2 * A.card * ∑ σ, muT n t σ * F σ := by
        rw [mul_sum]
        exact sum_congr rfl fun _ _ => by ring
      calc _ ≤ exposureWeight n A.card A i * ∑ σ, muT n t σ * (2 * A.card * F σ) :=
            mul_le_mul_of_nonneg_left hσ hw
        _ = _ := by rw [hsum]; ring
    · simp [exposureWeight_eq_zero h]
  linarith

end CycleCutoff
