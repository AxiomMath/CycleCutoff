/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.FiniteProbability.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset

/-!
# The Bernoulli--Laplace slice, its energy and the Lee--Yau constant

For a ground set `U : Finset α`, the slice `Ω_{U,k} = {S ⊆ U : |S| = k}` is the finite subtype
`↥(U.powersetCard k)` of `Finset α`, so that `U \ {j}` is `U.erase j` and the maps
`S₀ ↦ S₀ ∪ {j}` and `S₀ ↦ S₀` from slices of `U.erase j` land in slices of `U`. The swap
`S ↦ S \ {a} ∪ {b}` is defined for `a ∈ S` and `b ∈ U \ S`, and is the identity on every
other pair.

## Main definitions

* `CycleCutoff.blSlice`: the slice `Ω_{U,k}`.
* `CycleCutoff.blSwap`: the swap `S ↦ S \ {a} ∪ {b}`.
* `CycleCutoff.blEnergy`: the energy
  `𝒟^BL_{U,k}(g) = 𝔼_u[∑_{a ∈ S} ∑_{b ∈ U \ S} (g(S \ {a} ∪ {b}) - g(S))²]`, `u` uniform.
* `CycleCutoff.blPhi`: the Lee--Yau constant `Φ_BL(k₁, k₂) = 3n(5 + log(n/k₁) + log(n/k₂))`,
  `n = k₁ + k₂`.
* `CycleCutoff.blInsert`, `CycleCutoff.blIncl`: the maps `Ω_{U \ {j}, k} → Ω_{U, k+1}`,
  `S₀ ↦ S₀ ∪ {j}`, and `Ω_{U \ {j}, k} → Ω_{U, k}`, `S₀ ↦ S₀`.
-/

@[expose] public section

open Finset

namespace CycleCutoff

variable {α : Type*}

/-- The slice `Ω_{U,k} = {S ⊆ U : |S| = k}`, as a finite type. -/
@[cycle_cutoff "def_bl_slice"]
abbrev blSlice (U : Finset α) (k : ℕ) : Type _ :=
  ↥(U.powersetCard k)

namespace blSlice

variable {U : Finset α} {k : ℕ}

/-- A point of the slice `Ω_{U,k}` is a subset of `U`. -/
theorem subset (S : blSlice U k) : (S : Finset α) ⊆ U :=
  (mem_powersetCard.1 S.2).1

/-- A point of the slice `Ω_{U,k}` has `k` elements. -/
theorem card_eq (S : blSlice U k) : (S : Finset α).card = k :=
  (mem_powersetCard.1 S.2).2

/-- An element of a point of the slice `Ω_{U,k}` lies in `U`. -/
theorem mem_of_mem (S : blSlice U k) {a : α} (ha : a ∈ (S : Finset α)) : a ∈ U :=
  S.subset ha

/-- Two points of the slice are equal when their underlying sets are. -/
@[ext] theorem ext {S T : blSlice U k} (h : (S : Finset α) = T) : S = T :=
  Subtype.ext h

end blSlice

/-- `|Ω_{U,k}| = binom(|U|, k)`. -/
theorem card_blSlice (U : Finset α) (k : ℕ) :
    Fintype.card (blSlice U k) = U.card.choose k := by
  simp [blSlice, Fintype.card_coe, card_powersetCard]

/-- The slice `Ω_{U,k}` is nonempty for `k ≤ |U|`. -/
theorem blSlice_nonempty {U : Finset α} {k : ℕ} (hk : k ≤ U.card) :
    Nonempty (blSlice U k) :=
  (powersetCard_nonempty.2 hk).to_subtype

variable [DecidableEq α]

/-- The swap `S ↦ S \ {a} ∪ {b}` on the slice, for `a ∈ S` and `b ∈ U \ S`; it returns `S`
itself for any other pair. -/
def blSwap {U : Finset α} {k : ℕ} (S : blSlice U k) (a b : α) : blSlice U k :=
  if h : a ∈ (S : Finset α) ∧ b ∈ U \ (S : Finset α) then
    ⟨insert b ((S : Finset α).erase a), by
      obtain ⟨ha, hb⟩ := h
      rw [mem_sdiff] at hb
      refine mem_powersetCard.2 ⟨?_, ?_⟩
      · exact insert_subset hb.1 ((erase_subset _ _).trans S.subset)
      · rw [card_insert_of_notMem (fun hb' => hb.2 (mem_of_mem_erase hb')),
          card_erase_of_mem ha, S.card_eq]
        have : 0 < k := S.card_eq ▸ card_pos.2 ⟨a, ha⟩
        omega⟩
  else S

/-- For `a ∈ S` and `b ∈ U \ S`, the swap is `S \ {a} ∪ {b}`. -/
theorem blSwap_of_mem {U : Finset α} {k : ℕ} (S : blSlice U k) {a b : α}
    (ha : a ∈ (S : Finset α)) (hb : b ∈ U \ (S : Finset α)) :
    ((blSwap S a b : blSlice U k) : Finset α) = insert b ((S : Finset α).erase a) := by
  simp [blSwap, ha, hb]

/-- Unless `a ∈ S` and `b ∈ U \ S`, the swap leaves `S` unchanged. -/
theorem blSwap_of_not {U : Finset α} {k : ℕ} (S : blSlice U k) {a b : α}
    (h : ¬(a ∈ (S : Finset α) ∧ b ∈ U \ (S : Finset α))) : blSwap S a b = S := by
  simp only [blSwap, dif_neg h]

/-- The Bernoulli--Laplace energy
`𝒟^BL_{U,k}(g) = 𝔼_u[∑_{a ∈ S} ∑_{b ∈ U \ S} (g(S \ {a} ∪ {b}) - g(S))²]`. -/
@[cycle_cutoff "def_bl_energy"]
noncomputable def blEnergy (U : Finset α) (k : ℕ) (g : blSlice U k → ℝ) : ℝ :=
  expectation (unif (blSlice U k)) (fun S =>
    ∑ a ∈ (S : Finset α), ∑ b ∈ U \ (S : Finset α), (g (blSwap S a b) - g S) ^ 2)

/-- The explicit Lee--Yau constant `Φ_BL(k₁, k₂) = 3n(5 + log(n/k₁) + log(n/k₂))`,
`n = k₁ + k₂` (meaningful for `k₁, k₂ ≥ 1`). -/
@[cycle_cutoff "def_bl_phi"]
noncomputable def blPhi (k₁ k₂ : ℕ) : ℝ :=
  3 * ((k₁ + k₂ : ℕ) : ℝ) *
    (5 + Real.log (((k₁ + k₂ : ℕ) : ℝ) / k₁) + Real.log (((k₁ + k₂ : ℕ) : ℝ) / k₂))

/-- The energy is non-negative. -/
theorem blEnergy_nonneg (U : Finset α) (k : ℕ) (g : blSlice U k → ℝ) : 0 ≤ blEnergy U k g :=
  expectation_nonneg (fun _ => inv_nonneg.2 (Nat.cast_nonneg _))
    fun _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _

/-- For natural numbers `a ≤ n`, `log(n / a) ≥ 0` (also when `a = 0`, where `n / 0 = 0`). -/
theorem log_natCast_div_nonneg {a n : ℕ} (h : a ≤ n) : 0 ≤ Real.log ((n : ℝ) / a) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · exact Real.log_nonneg ((one_le_div (by exact_mod_cast ha)).2 (by exact_mod_cast h))

/-- The Lee--Yau constant is non-negative. -/
theorem blPhi_nonneg (a b : ℕ) : 0 ≤ blPhi a b := by
  have h₁ := log_natCast_div_nonneg (a := a) (n := a + b) (by omega)
  have h₂ := log_natCast_div_nonneg (a := b) (n := a + b) (by omega)
  exact mul_nonneg (by positivity) (by linarith)

/-! ### The maps from slices of `U.erase j` -/

/-- `S₀ ↦ S₀ ∪ {j}`, from `Ω_{U \ {j}, k}` to `Ω_{U, k+1}` (for `j ∈ U`). -/
def blInsert {U : Finset α} {j : α} (hj : j ∈ U) {k : ℕ} (S : blSlice (U.erase j) k) :
    blSlice U (k + 1) :=
  ⟨insert j (S : Finset α), by
    refine mem_powersetCard.2 ⟨insert_subset hj (S.subset.trans (erase_subset _ _)), ?_⟩
    rw [card_insert_of_notMem (fun h => by simpa using S.subset h), S.card_eq]⟩

/-- The underlying set of `blInsert hj S` is `S ∪ {j}`. -/
@[simp] theorem coe_blInsert {U : Finset α} {j : α} (hj : j ∈ U) {k : ℕ}
    (S : blSlice (U.erase j) k) :
    ((blInsert hj S : blSlice U (k + 1)) : Finset α) = insert j (S : Finset α) := rfl

/-- A point of a slice of `U.erase j` does not contain `j`. -/
theorem not_mem_of_blSlice_erase {U : Finset α} {j : α} {k : ℕ} (S : blSlice (U.erase j) k) :
    j ∉ (S : Finset α) := fun h => by simpa using S.subset h

/-- The inclusion `Ω_{U \ {j}, k} → Ω_{U, k}`. -/
def blIncl {U : Finset α} (j : α) {k : ℕ} (S : blSlice (U.erase j) k) : blSlice U k :=
  ⟨(S : Finset α), mem_powersetCard.2 ⟨S.subset.trans (erase_subset _ _), S.card_eq⟩⟩

/-- The underlying set of `blIncl j S` is `S`. -/
@[simp] theorem coe_blIncl {U : Finset α} (j : α) {k : ℕ} (S : blSlice (U.erase j) k) :
    ((blIncl j S : blSlice U k) : Finset α) = (S : Finset α) := rfl

end CycleCutoff
