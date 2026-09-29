/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Exposure.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Fintype.Perm

/-!
# The chain rule for random exposure

For a positive probability vector `μ` on `S_n`, the relative entropy of `μ` with respect to the
uniform law is the `ζ_m`-average, summed over `1 ≤ m ≤ n`, of the `μ`-averaged relative entropies
of the conditional laws `𝔲^μ_{A,i}(σ)` with respect to the uniform law on `σ(A)`:
`H(μ | π_n) = ∑_{m=1}^n ∑_{A,i} ζ_m(A,i) ∑_σ μ(σ) H(𝔲^μ_{A,i}(σ) | unif_{σ(A)})`.

## Main results

* `CycleCutoff.relEnt_unif_eq_sum_exposure`: the chain rule.
-/

public section

open Finset Real

namespace CycleCutoff

variable {n : ℕ} [NeZero n]

/-- The telescoping potential `G(A) = ∑_σ μ(σ) log (μ(σ) |A|! / μ(agreeOff A σ))`. -/
private noncomputable def chainPotential (μ : Equiv.Perm (ZMod n) → ℝ) (A : Finset (ZMod n)) :
    ℝ :=
  ∑ σ, μ σ * Real.log (μ σ * (A.card.factorial : ℝ) / mass μ (agreeOff A σ))

private lemma chainPotential_univ {μ : Equiv.Perm (ZMod n) → ℝ} (hμ : IsProbVec μ) :
    chainPotential μ univ = relEnt μ (unif (Equiv.Perm (ZMod n))) := by
  unfold chainPotential relEnt
  refine sum_congr rfl fun σ _ => ?_
  rw [agreeOff_univ, show mass μ univ = 1 from hμ.sum_eq_one, unif_apply, Fintype.card_perm,
    Finset.card_univ, div_one, div_inv_eq_mul]

private lemma chainPotential_empty {μ : Equiv.Perm (ZMod n) → ℝ} (hpos : ∀ σ, 0 < μ σ) :
    chainPotential μ ∅ = 0 := by
  unfold chainPotential
  refine sum_eq_zero fun σ _ => ?_
  rw [agreeOff_empty, mass, sum_singleton, card_empty, Nat.factorial_zero, Nat.cast_one, mul_one,
    div_self (hpos σ).ne', log_one, mul_zero]

private lemma exposureLaw_apply_self (μ : Equiv.Perm (ZMod n) → ℝ) {A : Finset (ZMod n)}
    {i : ZMod n} (hi : i ∈ A) (σ : Equiv.Perm (ZMod n)) :
    exposureLaw μ A i σ (σ i) = mass μ (agreeOff (A.erase i) σ) / mass μ (agreeOff A σ) := by
  rw [exposureLaw_apply, agreeOff_erase hi]
  rfl

private lemma relEnt_exposureLaw_unif (μ : Equiv.Perm (ZMod n) → ℝ) {A : Finset (ZMod n)}
    {i : ZMod n} (hi : i ∈ A) (σ : Equiv.Perm (ZMod n)) :
    relEnt (fun x : A.image σ => exposureLaw μ A i σ x) (unif (A.image σ)) =
      ∑ x, exposureLaw μ A i σ x * Real.log (exposureLaw μ A i σ x * A.card) := by
  rw [sum_univ_exposureLaw_mul μ hi, relEnt, ← Finset.sum_coe_sort (A.image σ)]
  simp only [unif_apply, Fintype.card_coe, card_image_perm, div_inv_eq_mul]

/-- The one-step identity: for `i ∈ A`,
`G(A) = G(A \ {i}) + ∑_σ μ(σ) H(𝔲^μ_{A,i}(σ) | unif_{σ(A)})`. -/
private lemma chainPotential_eq_erase_add {μ : Equiv.Perm (ZMod n) → ℝ} (hpos : ∀ σ, 0 < μ σ)
    {A : Finset (ZMod n)} {i : ZMod n} (hi : i ∈ A) :
    chainPotential μ A = chainPotential μ (A.erase i) + ∑ σ, μ σ *
      relEnt (fun x : A.image σ => exposureLaw μ A i σ x) (unif (A.image σ)) := by
  have hμ0 : ∀ σ, 0 ≤ μ σ := fun σ => (hpos σ).le
  have key : ∑ σ, μ σ * relEnt (fun x : A.image σ => exposureLaw μ A i σ x) (unif (A.image σ)) =
      ∑ σ, μ σ * Real.log (exposureLaw μ A i σ (σ i) * A.card) := by
    simp_rw [relEnt_exposureLaw_unif μ hi]
    exact sum_mul_exposureLaw hμ0 A i (fun σ x => Real.log (exposureLaw μ A i σ x * A.card))
      fun σ σ' h => by simp only [exposureLaw_eq_of_mem_agreeOff μ i h]
  rw [key, chainPotential, chainPotential, ← sum_add_distrib]
  refine sum_congr rfl fun σ _ => ?_
  rw [← mul_add, exposureLaw_apply_self μ hi]
  have hM : 0 < mass μ (agreeOff A σ) := mass_pos_of_pos hpos ⟨σ, self_mem_agreeOff A σ⟩
  have hM' : 0 < mass μ (agreeOff (A.erase i) σ) :=
    mass_pos_of_pos hpos ⟨σ, self_mem_agreeOff _ σ⟩
  have hσ := hpos σ
  have hcard : A.card = (A.erase i).card + 1 := (card_erase_add_one hi).symm
  have hf : (0 : ℝ) < ((A.erase i).card.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [← log_mul (by positivity) (by rw [hcard]; positivity)]
  congr 2
  rw [hcard, Nat.factorial_succ]
  push_cast
  field_simp

/-- Averaging a function of `A` against `ζ_m`. -/
private lemma sum_exposureWeight_mul_left {m : ℕ} (hm : m ≠ 0) (G : Finset (ZMod n) → ℝ) :
    ∑ A : Finset (ZMod n), ∑ i : ZMod n, exposureWeight n m A i * G A =
      ((n.choose m : ℕ) : ℝ)⁻¹ * ∑ A : Finset (ZMod n) with A.card = m, G A := by
  rw [sum_exposureWeight_mul]
  have h : ∀ A ∈ (univ.filter fun A : Finset (ZMod n) => A.card = m),
      ∑ _i ∈ A, G A = m * G A := fun A hA => by
    rw [sum_const, (mem_filter.1 hA).2, nsmul_eq_mul]
  rw [sum_congr rfl h, ← mul_sum, mul_inv, mul_assoc, ← mul_assoc (m : ℝ)⁻¹,
    inv_mul_cancel₀ (by exact_mod_cast hm), one_mul]

/-- Averaging a function of `A \ {i}` against `ζ_{k+1}` gives the average over `k`-sets. -/
private lemma sum_exposureWeight_mul_erase {k : ℕ} (hk : k < n) (G : Finset (ZMod n) → ℝ) :
    ∑ A : Finset (ZMod n), ∑ i : ZMod n, exposureWeight n (k + 1) A i * G (A.erase i) =
      ((n.choose k : ℕ) : ℝ)⁻¹ * ∑ B : Finset (ZMod n) with B.card = k, G B := by
  rw [sum_exposureWeight_mul]
  have hswap : ∑ A : Finset (ZMod n) with A.card = k + 1, ∑ i ∈ A, G (A.erase i) =
      ∑ B : Finset (ZMod n) with B.card = k, ∑ _i ∈ Bᶜ, G B := by
    rw [sum_sigma', sum_sigma']
    refine sum_nbij' (fun p => ⟨p.1.erase p.2, p.2⟩) (fun p => ⟨insert p.2 p.1, p.2⟩)
      ?_ ?_ ?_ ?_ ?_
    · rintro ⟨A, i⟩ h
      simp only [mem_sigma, mem_filter, mem_univ, true_and] at h ⊢
      exact ⟨by rw [card_erase_of_mem h.2, h.1]; rfl, by simp⟩
    · rintro ⟨B, i⟩ h
      simp only [mem_sigma, mem_filter, mem_univ, true_and, mem_compl] at h ⊢
      exact ⟨by rw [card_insert_of_notMem h.2, h.1], mem_insert_self _ _⟩
    · rintro ⟨A, i⟩ h
      simp only [mem_sigma, mem_filter, mem_univ, true_and] at h
      simp [insert_erase h.2]
    · rintro ⟨B, i⟩ h
      simp only [mem_sigma, mem_filter, mem_univ, true_and, mem_compl] at h
      simp [erase_insert h.2]
    · rintro ⟨A, i⟩ _
      rfl
  rw [hswap]
  have h : ∀ B ∈ (univ.filter fun B : Finset (ZMod n) => B.card = k),
      ∑ _i ∈ Bᶜ, G B = ((n - k : ℕ) : ℝ) * G B := fun B hB => by
    rw [sum_const, card_compl, ZMod.card, (mem_filter.1 hB).2, nsmul_eq_mul]
  rw [sum_congr rfl h, ← mul_sum, ← mul_assoc]
  congr 1
  have hc : ((n.choose (k + 1) : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) =
      ((n.choose k : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n k
  have h1 : ((n.choose k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk.le).ne'
  have h2 : ((n - k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.sub_pos_of_lt hk).ne'
  rw [hc, mul_inv, mul_assoc, inv_mul_cancel₀ h2, mul_one]

/-- A telescoping sum over `Icc 1 N`. -/
private lemma sum_Icc_sub_pred (f : ℕ → ℝ) (N : ℕ) :
    ∑ m ∈ Icc 1 N, (f m - f (m - 1)) = f N - f 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih, Nat.add_sub_cancel]
    ring

/-- The average of `G` over the `k`-subsets of labels. -/
private noncomputable def chainAverage (μ : Equiv.Perm (ZMod n) → ℝ) (k : ℕ) : ℝ :=
  ((n.choose k : ℕ) : ℝ)⁻¹ * ∑ A : Finset (ZMod n) with A.card = k, chainPotential μ A

private lemma chainAverage_self (μ : Equiv.Perm (ZMod n) → ℝ) :
    chainAverage μ n = chainPotential μ univ := by
  have h : (univ.filter fun A : Finset (ZMod n) => A.card = n) = {univ} := by
    ext A
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    rw [← card_eq_iff_eq_univ, ZMod.card]
  rw [chainAverage, h, sum_singleton, Nat.choose_self, Nat.cast_one, inv_one, one_mul]

private lemma chainAverage_zero (μ : Equiv.Perm (ZMod n) → ℝ) :
    chainAverage μ 0 = chainPotential μ ∅ := by
  have h : (univ.filter fun A : Finset (ZMod n) => A.card = 0) = {∅} := by
    ext A
    simp
  rw [chainAverage, h, sum_singleton, Nat.choose_zero_right, Nat.cast_one, inv_one, one_mul]

/-- **The chain rule for random exposure.** For a probability vector `μ` on `S_n` with `μ(σ) > 0`
for all `σ`,
`H(μ | π_n) = ∑_{m=1}^n ∑_{A,i} ζ_m(A,i) ∑_σ μ(σ) H(𝔲^μ_{A,i}(σ) | unif_{σ(A)})`,
each relative entropy taken on the finite set `σ(A)`. -/
@[cycle_cutoff "lem_exposure_chain_rule"]
theorem relEnt_unif_eq_sum_exposure (μ : Equiv.Perm (ZMod n) → ℝ) (hμ : IsProbVec μ)
    (hpos : ∀ σ, 0 < μ σ) :
    relEnt μ (unif (Equiv.Perm (ZMod n))) =
      ∑ m ∈ Icc 1 n, ∑ A : Finset (ZMod n), ∑ i : ZMod n, exposureWeight n m A i *
        ∑ σ : Equiv.Perm (ZMod n), μ σ *
          relEnt (fun x : A.image σ => exposureLaw μ A i σ x) (unif (A.image σ)) := by
  have hstep : ∀ m ∈ Icc 1 n,
      ∑ A : Finset (ZMod n), ∑ i : ZMod n, exposureWeight n m A i *
        ∑ σ : Equiv.Perm (ZMod n), μ σ *
          relEnt (fun x : A.image σ => exposureLaw μ A i σ x) (unif (A.image σ)) =
        chainAverage μ m - chainAverage μ (m - 1) := by
    intro m hm
    obtain ⟨hm1, hmn⟩ := mem_Icc.1 hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    calc _ = ∑ A : Finset (ZMod n), ∑ i : ZMod n, (exposureWeight n (k + 1) A i *
            chainPotential μ A - exposureWeight n (k + 1) A i * chainPotential μ (A.erase i)) :=
          sum_congr rfl fun A _ => sum_congr rfl fun i _ => by
            by_cases hi : i ∈ A
            · rw [chainPotential_eq_erase_add hpos hi]
              ring
            · rw [exposureWeight_eq_zero (by tauto)]
              ring
      _ = _ := by
        simp only [sum_sub_distrib]
        rw [sum_exposureWeight_mul_left (Nat.succ_ne_zero k),
          sum_exposureWeight_mul_erase (by omega), Nat.add_sub_cancel]
        rfl
  rw [sum_congr rfl hstep, sum_Icc_sub_pred, chainAverage_self, chainAverage_zero,
    chainPotential_univ hμ, chainPotential_empty hpos, sub_zero]

end CycleCutoff
