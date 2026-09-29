/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Exposure.ChainRule
public import CycleCutoff.Exposure.LogZBound
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The exposure bound on the relative entropy

Let `n ≥ 3`, let `W : ℤ/n × ℤ/n → [1/2, 3/2]` have all row sums equal to `n`, and let `μ` be a
positive probability vector on `S_n`. Then
`H(μ | π_n) ≤ ∑_{m=1}^n ∑_{A,i} ζ_m(A,i) ∑_σ μ(σ) H(𝔲^μ_{A,i}(σ) | q̂^W_{i,σ(A)})
  + ∑_i 𝔼_μ[log W(i, σ(i))] + 3 (1 + log n)`.

## Main results

* `CycleCutoff.relEnt_unif_le_exposure`: the exposure bound.
-/

public section

open Finset Real

namespace CycleCutoff

variable {n : ℕ} [NeZero n]

/-- `(binom(n, m) m)⁻¹ binom(n - 1, m - 1) = 1 / n` for `1 ≤ m ≤ n`. -/
private lemma choose_mul_inv_mul_choose {m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    (((n.choose m : ℕ) : ℝ) * m)⁻¹ * (((n - 1).choose (m - 1) : ℕ) : ℝ) = (n : ℝ)⁻¹ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h := Nat.add_one_mul_choose_eq k j
  have h1 : (0 : ℝ) < ((k + 1).choose (j + 1) : ℕ) := by exact_mod_cast Nat.choose_pos hmn
  have hr : ((k + 1 : ℕ) : ℝ) * ((k.choose j : ℕ) : ℝ) =
      (((k + 1).choose (j + 1) : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) := by exact_mod_cast h
  have h2 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have h3 : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  field_simp
  linarith

/-- Each label carries total `ζ_m`-weight `1 / n`. -/
private lemma sum_exposureWeight_left {m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (i : ZMod n) :
    ∑ A : Finset (ZMod n), exposureWeight n m A i = (n : ℝ)⁻¹ := by
  classical
  simp only [exposureWeight_apply]
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  have hfilt : (univ.filter fun A : Finset (ZMod n) => A.card = m ∧ i ∈ A) =
      (univ.powersetCard m).filter ({i} ⊆ ·) := by
    ext A
    simp [mem_powersetCard]
  have hcount := card_filter_powersetCard_subset {i} (univ : Finset (ZMod n)) m (subset_univ _)
    (by rw [card_singleton]; exact hm)
  rw [hfilt, hcount, card_singleton, card_univ, ZMod.card, mul_comm]
  exact choose_mul_inv_mul_choose hm hmn

/-- The splitting `H(u | unif_R) = H(u | q̂^W_{i,R}) + ∑_x u(x) log W(i, x) - log Z` on `R = σ(A)`,
with `u = 𝔲^μ_{A,i}(σ)` and `Z = |A|⁻¹ ∑_{y ∈ R} W(i, y)`. -/
private lemma relEnt_unif_eq_relEnt_qHat {μ : Equiv.Perm (ZMod n) → ℝ} (hpos : ∀ σ, 0 < μ σ)
    {W : ZMod n → ZMod n → ℝ} {i : ZMod n} (hW : ∀ x, 0 < W i x) {A : Finset (ZMod n)}
    (hi : i ∈ A) (σ : Equiv.Perm (ZMod n)) :
    relEnt (fun x : A.image σ => exposureLaw μ A i σ x) (unif (A.image σ)) =
      relEnt (fun x : A.image σ => exposureLaw μ A i σ x)
          (fun x : A.image σ => qHat W i (A.image σ) x) +
        ∑ x, exposureLaw μ A i σ x * Real.log (W i x) -
        Real.log ((A.card : ℝ)⁻¹ * ∑ x ∈ A.image σ, W i x) := by
  set R := A.image σ with hR
  set u := exposureLaw μ A i σ with hu
  set S := ∑ x ∈ R, W i x with hS
  have hmass : mass μ (agreeOff A σ) ≠ 0 :=
    (mass_pos_of_pos hpos ⟨σ, self_mem_agreeOff A σ⟩).ne'
  have hsum : ∑ x ∈ R, u x = 1 := sum_exposureLaw μ hi σ hmass
  have hRne : R.Nonempty := ⟨σ i, mem_image_of_mem σ hi⟩
  have hS0 : 0 < S := sum_pos (fun x _ => hW x) hRne
  have hc : (0 : ℝ) < A.card := by exact_mod_cast card_pos.2 ⟨i, hi⟩
  have hlogZ : Real.log ((A.card : ℝ)⁻¹ * S) =
      ∑ x : R, u x * Real.log ((A.card : ℝ)⁻¹ * S) := by
    rw [← sum_mul, sum_coe_sort R u, hsum, one_mul]
  rw [sum_univ_exposureLaw_mul μ hi, ← sum_coe_sort R (fun x => u x * Real.log (W i x)), hlogZ,
    relEnt, relEnt, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [unif_apply, Fintype.card_coe, show R.card = A.card from card_image_perm A σ, qHat_apply,
    ← hS]
  by_cases hux : u x = 0
  · simp [hux]
  have hu0 : 0 < u x := lt_of_le_of_ne (exposureLaw_nonneg (fun σ => (hpos σ).le) _ _ _ _)
    (Ne.symm hux)
  have hWx := hW x
  rw [← mul_add, ← mul_sub]
  congr 1
  rw [log_div hux (by positivity), log_div hux (by positivity), log_div hWx.ne' hS0.ne',
    log_mul (by positivity) hS0.ne', log_inv]
  ring

/-- **The exposure bound**: for `W` with entries in `[1/2, 3/2]` and row sums `n`, and a positive
probability vector `μ` on `S_n`,
`H(μ | π_n) ≤ ∑_{m=1}^n ∑_{A,i} ζ_m(A,i) ∑_σ μ(σ) H(𝔲^μ_{A,i}(σ) | q̂^W_{i,σ(A)})
  + ∑_i 𝔼_μ[log W(i, σ(i))] + 3 (1 + log n)`. -/
@[cycle_cutoff "lem_exposure"]
theorem relEnt_unif_le_exposure (hn : 3 ≤ n) (W : ZMod n → ZMod n → ℝ)
    (hW : ∀ i x, 1 / 2 ≤ W i x ∧ W i x ≤ 3 / 2) (hrow : ∀ i, ∑ x, W i x = n)
    (μ : Equiv.Perm (ZMod n) → ℝ) (hμ : IsProbVec μ) (hpos : ∀ σ, 0 < μ σ) :
    relEnt μ (unif (Equiv.Perm (ZMod n))) ≤
      ∑ m ∈ Icc 1 n, ∑ A : Finset (ZMod n), ∑ i : ZMod n, exposureWeight n m A i *
          ∑ σ : Equiv.Perm (ZMod n), μ σ *
            relEnt (fun x : A.image σ => exposureLaw μ A i σ x)
              (fun x : A.image σ => qHat W i (A.image σ) x) +
        ∑ i : ZMod n, expectation μ (fun σ => Real.log (W i (σ i))) + 3 * (1 + Real.log n) := by
  classical
  have hWpos : ∀ i x, 0 < W i x := fun i x => by linarith [(hW i x).1]
  set L : Finset (ZMod n) → ZMod n → Equiv.Perm (ZMod n) → ℝ :=
    fun A i σ => ∑ x, exposureLaw μ A i σ x * Real.log (W i x)
  set Z : ℕ → Finset (ZMod n) → ZMod n → Equiv.Perm (ZMod n) → ℝ :=
    fun m A i σ => Real.log ((m : ℝ)⁻¹ * ∑ x ∈ A.image σ, W i x)
  have hterm : ∀ m A i, exposureWeight n m A i * ∑ σ, μ σ *
        relEnt (fun x : A.image σ => exposureLaw μ A i σ x) (unif (A.image σ)) =
      exposureWeight n m A i * ∑ σ, μ σ * relEnt (fun x : A.image σ => exposureLaw μ A i σ x)
          (fun x : A.image σ => qHat W i (A.image σ) x) +
        exposureWeight n m A i * ∑ σ, μ σ * L A i σ +
        exposureWeight n m A i * ∑ σ, μ σ * (-Z m A i σ) := by
    intro m A i
    by_cases h : A.card = m ∧ i ∈ A
    · obtain ⟨rfl, hi⟩ := h
      rw [← mul_add, ← mul_add, ← sum_add_distrib, ← sum_add_distrib]
      congr 1
      refine sum_congr rfl fun σ _ => ?_
      rw [relEnt_unif_eq_relEnt_qHat hpos (hWpos i) hi σ]
      ring
    · simp [exposureWeight_eq_zero h]
  have hLsum : ∑ m ∈ Icc 1 n, ∑ A : Finset (ZMod n), ∑ i : ZMod n,
      exposureWeight n m A i * ∑ σ, μ σ * L A i σ =
      ∑ i : ZMod n, expectation μ (fun σ => Real.log (W i (σ i))) := by
    have h1 : ∀ A i, ∑ σ, μ σ * L A i σ = expectation μ (fun σ => Real.log (W i (σ i))) :=
      fun A i => sum_mul_exposureLaw hμ.nonneg A i (fun _ x => Real.log (W i x))
        (fun _ _ _ => rfl)
    simp only [h1]
    have h2 : ∀ m ∈ Icc 1 n, ∑ A : Finset (ZMod n), ∑ i : ZMod n,
        exposureWeight n m A i * expectation μ (fun σ => Real.log (W i (σ i))) =
        (n : ℝ)⁻¹ * ∑ i : ZMod n, expectation μ (fun σ => Real.log (W i (σ i))) := by
      intro m hm
      rw [mem_Icc] at hm
      rw [sum_comm, mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [← sum_mul, sum_exposureWeight_left hm.1 hm.2]
    rw [sum_congr rfl h2, sum_const, Nat.card_Icc, nsmul_eq_mul, ← mul_assoc, Nat.add_sub_cancel,
      mul_inv_cancel₀ (by exact_mod_cast NeZero.ne n), one_mul]
  have hZsum : ∑ m ∈ Icc 1 n, ∑ A : Finset (ZMod n), ∑ i : ZMod n,
      exposureWeight n m A i * ∑ σ, μ σ * (-Z m A i σ) ≤ 3 * (1 + Real.log n) := by
    have h1 : ∀ m ∈ Icc 1 n, ∑ A : Finset (ZMod n), ∑ i : ZMod n,
        exposureWeight n m A i * ∑ σ, μ σ * (-Z m A i σ) ≤ 3 / m := by
      intro m hm
      rw [mem_Icc] at hm
      have hswap : ∑ A : Finset (ZMod n), ∑ i : ZMod n,
          exposureWeight n m A i * ∑ σ, μ σ * (-Z m A i σ) =
          ∑ σ, μ σ * ∑ i : ZMod n, ∑ A : Finset (ZMod n),
            exposureWeight n m A i * (-Z m A i σ) := by
        calc _ = ∑ i : ZMod n, ∑ A : Finset (ZMod n), ∑ σ,
                μ σ * (exposureWeight n m A i * (-Z m A i σ)) := by
              rw [sum_comm]
              refine sum_congr rfl fun i _ => sum_congr rfl fun A _ => ?_
              rw [mul_sum]
              exact sum_congr rfl fun σ _ => by ring
          _ = ∑ i : ZMod n, ∑ σ, ∑ A : Finset (ZMod n),
                μ σ * (exposureWeight n m A i * (-Z m A i σ)) :=
              sum_congr rfl fun i _ => sum_comm
          _ = _ := by
              rw [sum_comm]
              refine sum_congr rfl fun σ _ => ?_
              rw [mul_sum]
              exact sum_congr rfl fun i _ => by rw [mul_sum]
      have hinner : ∀ σ i, ∑ A : Finset (ZMod n), exposureWeight n m A i * (-Z m A i σ) ≤
          (n : ℝ)⁻¹ * (3 / m) := by
        intro σ i
        set b : ℝ := (((n - 1).choose (m - 1) : ℕ) : ℝ) with hb
        have hb0 : 0 < b := by
          rw [hb]; exact_mod_cast Nat.choose_pos (by omega)
        have hT := neg_three_div_le_sum_log_exposure hn hm.1 hm.2 W hW hrow i σ
        rw [← hb] at hT
        have hfilt : ∑ A : Finset (ZMod n), exposureWeight n m A i * (-Z m A i σ) =
            (((n.choose m : ℕ) : ℝ) * m)⁻¹ *
              -∑ A : Finset (ZMod n) with i ∈ A ∧ A.card = m,
                Real.log ((m : ℝ)⁻¹ * ∑ x ∈ A.image σ, W i x) := by
          rw [← sum_neg_distrib, mul_sum, sum_filter]
          refine sum_congr rfl fun A _ => ?_
          by_cases h : i ∈ A ∧ A.card = m
          · rw [if_pos h, exposureWeight_of_mem h.2 h.1]
          · rw [if_neg h, exposureWeight_eq_zero (by tauto), zero_mul]
        have hcb := choose_mul_inv_mul_choose hm.1 hm.2
        rw [← hb] at hcb
        rw [hfilt]
        set c : ℝ := (((n.choose m : ℕ) : ℝ) * m)⁻¹
        set T := ∑ A : Finset (ZMod n) with i ∈ A ∧ A.card = m,
                Real.log ((m : ℝ)⁻¹ * ∑ x ∈ A.image σ, W i x)
        have hc : c = (n : ℝ)⁻¹ * b⁻¹ := by
          rw [← hcb]; field_simp
        rw [hc]
        have : -(b⁻¹ * T) ≤ 3 / m := by rw [neg_div] at hT; linarith
        calc (n : ℝ)⁻¹ * b⁻¹ * -T = (n : ℝ)⁻¹ * -(b⁻¹ * T) := by ring
          _ ≤ (n : ℝ)⁻¹ * (3 / m) := mul_le_mul_of_nonneg_left this (by positivity)
      rw [hswap]
      calc ∑ σ, μ σ * ∑ i : ZMod n, ∑ A : Finset (ZMod n),
            exposureWeight n m A i * (-Z m A i σ)
          ≤ ∑ σ, μ σ * ∑ i : ZMod n, (n : ℝ)⁻¹ * (3 / m) :=
            sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left
              (sum_le_sum fun i _ => hinner σ i) (hpos σ).le
        _ = 3 / m := by
            rw [← sum_mul, hμ.sum_eq_one, one_mul, sum_const, card_univ, ZMod.card,
              nsmul_eq_mul, ← mul_assoc,
              mul_inv_cancel₀ (by exact_mod_cast NeZero.ne n), one_mul]
    calc _ ≤ ∑ m ∈ Icc 1 n, (3 : ℝ) / m := sum_le_sum h1
      _ = 3 * (harmonic n : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        rw [mul_sum]
        exact sum_congr rfl fun m _ => by ring
      _ ≤ 3 * (1 + Real.log n) := by linarith [harmonic_le_one_add_log n]
  rw [relEnt_unif_eq_sum_exposure μ hμ hpos]
  simp only [hterm, sum_add_distrib]
  linarith

end CycleCutoff
