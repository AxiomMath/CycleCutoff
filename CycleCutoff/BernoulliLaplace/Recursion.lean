/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.BernoulliLaplace.Marginal
public import CycleCutoff.FiniteProbability.EntChainRule
public import CycleCutoff.FiniteProbability.PushforwardEntropy
public import CycleCutoff.FiniteProbability.CondExpPullOut
public import CycleCutoff.Generator.LsiTensorization

/-!
# The Lee--Yau recursion for the Bernoulli--Laplace slice

Let `U` be a finite set with `|U| = N`, let `1 ≤ k ≤ N - 1`, and let `ν` be the uniform
measure on the slice `Ω_{U,k}`. Suppose that for every `j ∈ U` the slices `Ω_{U \ {j}, k-1}`
(when `k ≥ 2`) and `Ω_{U \ {j}, k}` (when `k ≤ N - 2`) satisfy log-Sobolev inequalities with
constants `c'` and `c''` for the Bernoulli--Laplace energy. Then for every `g : Ω_{U,k} → ℝ`,
`Ent_ν(g²) ≤ [6/N² (1 + log(N/k) + log(N/(N-k))) + ((k-1)c' + (N-k-1)c'')/N] 𝒟^BL_{U,k}(g)`.

## Main results

* `CycleCutoff.ent_sq_le_blEnergy_of_erase`: the recursion above.
-/

public section

open Finset

namespace CycleCutoff

/-- On a type with at most one point, the uniform entropy of any function vanishes. -/
private lemma ent_unif_of_subsingleton {Ω : Type*} [Fintype Ω] [Subsingleton Ω] (f : Ω → ℝ) :
    ent (unif Ω) f = 0 := by
  cases isEmpty_or_nonempty Ω with
  | inl h => simp [ent, expectation]
  | inr h =>
    obtain ⟨z₀⟩ := h
    have hf : f = fun _ => f z₀ := funext fun z => by rw [Subsingleton.elim z z₀]
    have : Nonempty Ω := ⟨z₀⟩
    rw [hf, ent, isProbVec_unif.expectation_const, isProbVec_unif.expectation_const, sub_self]

variable {α : Type*} [DecidableEq α]

private lemma blInsert_injective {U : Finset α} {j : α} (hj : j ∈ U) {k : ℕ} :
    Function.Injective (blInsert hj : blSlice (U.erase j) k → blSlice U (k + 1)) := by
  intro S T h
  have h' : insert j (S : Finset α) = insert j (T : Finset α) := congrArg Subtype.val h
  ext1
  rw [← erase_insert (not_mem_of_blSlice_erase S), h', erase_insert (not_mem_of_blSlice_erase T)]

private lemma blIncl_injective {U : Finset α} (j : α) {k : ℕ} :
    Function.Injective (blIncl j : blSlice (U.erase j) k → blSlice U k) :=
  fun S T h => Subtype.ext (by simpa using congrArg Subtype.val h)

private lemma blInsert_blSwap {U : Finset α} {j : α} (hj : j ∈ U) {k : ℕ}
    (S : blSlice (U.erase j) k) {a b : α} (ha : a ∈ (S : Finset α))
    (hb : b ∈ U.erase j \ (S : Finset α)) :
    blInsert hj (blSwap S a b) = blSwap (blInsert hj S) a b := by
  have hjS := not_mem_of_blSlice_erase S
  have haj : a ≠ j := fun h => hjS (h ▸ ha)
  obtain ⟨hb₁, hb₂⟩ := mem_sdiff.1 hb
  have hbj : b ≠ j := ne_of_mem_erase hb₁
  have ha' : a ∈ ((blInsert hj S : blSlice U (k + 1)) : Finset α) := by
    simp [ha]
  have hb' : b ∈ U \ ((blInsert hj S : blSlice U (k + 1)) : Finset α) := by
    simp [hbj, hb₂, mem_of_mem_erase hb₁]
  ext1
  rw [blSwap_of_mem _ ha' hb', coe_blInsert, coe_blInsert, blSwap_of_mem S ha hb,
    erase_insert_of_ne (Ne.symm haj), insert_comm]

private lemma blIncl_blSwap {U : Finset α} (j : α) {k : ℕ}
    (S : blSlice (U.erase j) k) {a b : α} (ha : a ∈ (S : Finset α))
    (hb : b ∈ U.erase j \ (S : Finset α)) :
    blIncl j (blSwap S a b) = blSwap (blIncl j S) a b := by
  obtain ⟨hb₁, hb₂⟩ := mem_sdiff.1 hb
  have hb' : b ∈ U \ ((blIncl j S : blSlice U k) : Finset α) := by
    simp [hb₂, mem_of_mem_erase hb₁]
  ext1
  rw [blSwap_of_mem _ (by simpa using ha) hb', coe_blIncl, coe_blIncl, blSwap_of_mem S ha hb]

/-- The fibre `{S ∋ j}` is the image of `S₀ ↦ S₀ ∪ {j}`. -/
private lemma fiber_mem_eq_image_blInsert {U : Finset α} {j : α} (hj : j ∈ U) {k : ℕ}
    {S : blSlice U (k + 1)} (hjS : j ∈ (S : Finset α)) :
    fiber (fun T : blSlice U (k + 1) => decide (j ∈ (T : Finset α))) S =
      univ.image (blInsert hj : blSlice (U.erase j) k → blSlice U (k + 1)) := by
  ext T
  rw [mem_fiber, mem_image]
  simp only [hjS, decide_true, decide_eq_true_eq, mem_univ, true_and]
  constructor
  · intro hjT
    refine ⟨⟨(T : Finset α).erase j, mem_powersetCard.2 ⟨erase_subset_erase _ T.subset, ?_⟩⟩, ?_⟩
    · rw [card_erase_of_mem hjT, T.card_eq, Nat.add_sub_cancel]
    · ext1
      simp [insert_erase hjT]
  · rintro ⟨S₀, rfl⟩
    simp

/-- The fibre `{S ∌ j}` is the image of the inclusion. -/
private lemma fiber_not_mem_eq_image_blIncl {U : Finset α} (j : α) {k : ℕ}
    {S : blSlice U k} (hjS : j ∉ (S : Finset α)) :
    fiber (fun T : blSlice U k => decide (j ∈ (T : Finset α))) S =
      univ.image (blIncl j : blSlice (U.erase j) k → blSlice U k) := by
  ext T
  rw [mem_fiber, mem_image]
  simp only [hjS, decide_false, decide_eq_false_iff_not, mem_univ, true_and]
  constructor
  · intro hjT
    refine ⟨⟨(T : Finset α), mem_powersetCard.2 ⟨fun x hx => mem_erase.2
      ⟨fun h => hjT (h ▸ hx), T.subset hx⟩, T.card_eq⟩⟩, ?_⟩
    ext1
    simp
  · rintro ⟨S₀, rfl⟩
    exact not_mem_of_blSlice_erase S₀

/-- **Lee--Yau recursion.** If every slice `Ω_{U \ {j}, k-1}` (for `k ≥ 2`) and
`Ω_{U \ {j}, k}` (for `k ≤ N - 2`) satisfies the log-Sobolev inequality for the
Bernoulli--Laplace energy with constant `c'`, resp. `c''`, then
`Ent_u(g²) ≤ [6/N² (1 + log(N/k) + log(N/(N-k))) + ((k-1)c' + (N-k-1)c'')/N] 𝒟^BL_{U,k}(g)`
on `Ω_{U,k}`, `N = |U|`. -/
@[cycle_cutoff "lem_bl_recursion"]
theorem ent_sq_le_blEnergy_of_erase (U : Finset α) (k : ℕ) (hk : 1 ≤ k) (hkU : k < U.card)
    (c' c'' : ℝ) (hc' : 0 ≤ c') (hc'' : 0 ≤ c'')
    (h' : ∀ j ∈ U, 2 ≤ k → ∀ g' : blSlice (U.erase j) (k - 1) → ℝ,
      ent (unif (blSlice (U.erase j) (k - 1))) (fun S => g' S ^ 2) ≤
        c' * blEnergy (U.erase j) (k - 1) g')
    (h'' : ∀ j ∈ U, k + 2 ≤ U.card → ∀ g'' : blSlice (U.erase j) k → ℝ,
      ent (unif (blSlice (U.erase j) k)) (fun S => g'' S ^ 2) ≤
        c'' * blEnergy (U.erase j) k g'')
    (g : blSlice U k → ℝ) :
    ent (unif (blSlice U k)) (fun S => g S ^ 2) ≤
      (6 / (U.card : ℝ) ^ 2 * (1 + Real.log (U.card / k) + Real.log (U.card / (U.card - k))) +
          (((k : ℝ) - 1) * c' + ((U.card : ℝ) - k - 1) * c'') / U.card) *
        blEnergy U k g := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have H₁ : ∀ j ∈ U, ∀ g' : blSlice (U.erase j) k → ℝ,
      ent (unif (blSlice (U.erase j) k)) (fun S => g' S ^ 2) ≤ c' * blEnergy (U.erase j) k g' := by
    intro j hj g'
    by_cases hk2 : 2 ≤ k + 1
    · exact h' j hj hk2 g'
    · have : Subsingleton (blSlice (U.erase j) k) := ⟨fun S T => by
        ext1
        rw [card_eq_zero.1 (S.card_eq.trans (by omega)),
          card_eq_zero.1 (T.card_eq.trans (by omega))]⟩
      rw [ent_unif_of_subsingleton]
      exact mul_nonneg hc' (blEnergy_nonneg _ _ _)
  have H₀ : ∀ j ∈ U, ∀ g'' : blSlice (U.erase j) (k + 1) → ℝ,
      ent (unif (blSlice (U.erase j) (k + 1))) (fun S => g'' S ^ 2) ≤
        c'' * blEnergy (U.erase j) (k + 1) g'' := by
    intro j hj g''
    by_cases hk2 : k + 1 + 2 ≤ U.card
    · exact h'' j hj hk2 g''
    · have hcard : (U.erase j).card = k + 1 := by rw [card_erase_of_mem hj]; omega
      have hS : ∀ S : blSlice (U.erase j) (k + 1), (S : Finset α) = U.erase j := fun S =>
        eq_of_subset_of_card_le S.subset (by rw [hcard, S.card_eq])
      have : Subsingleton (blSlice (U.erase j) (k + 1)) := ⟨fun S T => by
        ext1; rw [hS, hS]⟩
      rw [ent_unif_of_subsingleton]
      exact mul_nonneg hc'' (blEnergy_nonneg _ _ _)
  have : Nonempty (blSlice U (k + 1)) := blSlice_nonempty hkU.le
  have hν : ∀ S, 0 < unif (blSlice U (k + 1)) S := unif_pos
  let q : blSlice U (k + 1) → α → α → ℝ := fun S a b => (g (blSwap S a b) - g S) ^ 2
  let H : α → blSlice U (k + 1) → ℝ := fun j S =>
    if j ∈ (S : Finset α) then
      c' * ∑ a ∈ (S : Finset α).erase j, ∑ b ∈ U \ (S : Finset α), q S a b
    else c'' * ∑ a ∈ (S : Finset α), ∑ b ∈ U.erase j \ (S : Finset α), q S a b
  have hcond : ∀ j ∈ U, ∀ S, condEnt (unif (blSlice U (k + 1)))
      (fun T : blSlice U (k + 1) => decide (j ∈ (T : Finset α))) (fun T => g T ^ 2) S ≤
        condExp (unif (blSlice U (k + 1)))
          (fun T : blSlice U (k + 1) => decide (j ∈ (T : Finset α))) (H j) S := by
    intro j hj S
    simp only [condEnt, condExp]
    by_cases hjS : j ∈ (S : Finset α)
    · rw [fiber_mem_eq_image_blInsert hj hjS,
        ← pushforward_unif_of_injective (blInsert_injective hj), ← ent_comp,
        ← expectation_comp]
      refine (H₁ j hj (fun S₀ => g (blInsert hj S₀))).trans (le_of_eq ?_)
      rw [blEnergy, ← expectation_const_mul]
      congr 1
      funext S₀
      simp only [H, q, coe_blInsert, mem_insert_self, if_true,
        erase_insert (not_mem_of_blSlice_erase S₀), sdiff_insert, ← erase_sdiff_comm]
      congr 1
      refine sum_congr rfl fun a ha => sum_congr rfl fun b hb => ?_
      rw [blInsert_blSwap hj S₀ ha hb]
    · rw [fiber_not_mem_eq_image_blIncl j hjS,
        ← pushforward_unif_of_injective (blIncl_injective j), ← ent_comp,
        ← expectation_comp]
      refine (H₀ j hj (fun S₀ => g (blIncl j S₀))).trans (le_of_eq ?_)
      rw [blEnergy, ← expectation_const_mul]
      congr 1
      funext S₀
      simp only [H, q]
      rw [if_neg (show j ∉ ((blIncl j S₀ : blSlice U (k + 1)) : Finset α) from
        not_mem_of_blSlice_erase S₀), coe_blIncl]
      congr 1
      refine sum_congr rfl fun a ha => sum_congr rfl fun b hb => ?_
      rw [blIncl_blSwap j S₀ ha hb]
  have hstep : ∀ j ∈ U, ent (unif (blSlice U (k + 1))) (fun S => g S ^ 2) ≤
      6 / U.card * (1 + Real.log (U.card / (k + 1 : ℕ)) +
          Real.log (U.card / (U.card - (k + 1 : ℕ)))) *
        expectation (unif (blSlice U (k + 1))) (fun S =>
          if j ∈ (S : Finset α) then
            ∑ b ∈ U \ (S : Finset α), (g (blSwap S j b) - g S) ^ 2
          else 0) +
        expectation (unif (blSlice U (k + 1))) (H j) := by
    intro j hj
    have hc := ent_eq_ent_condExp_add (unif (blSlice U (k + 1))) hν
      (fun T : blSlice U (k + 1) => decide (j ∈ (T : Finset α))) (fun S => g S ^ 2)
    have hm := ent_condExp_mem_le_blSwap U (k + 1) hk hkU j g
    have hC := expectation_mono (fun S => (hν S).le) (hcond j hj)
    have ht := expectation_mul_condExp (unif (blSlice U (k + 1))) hν
      (fun T : blSlice U (k + 1) => decide (j ∈ (T : Finset α))) (fun _ => (1 : ℝ)) (H j)
    simp only [one_mul] at ht
    linarith
  have hsum := sum_le_sum hstep
  rw [sum_const, nsmul_eq_mul, sum_add_distrib, ← mul_sum, ← expectation_sum,
    ← expectation_sum] at hsum
  have hE : expectation (unif (blSlice U (k + 1))) (fun S => ∑ j ∈ U,
      if j ∈ (S : Finset α) then ∑ b ∈ U \ (S : Finset α), (g (blSwap S j b) - g S) ^ 2
      else 0) = blEnergy U (k + 1) g := by
    rw [blEnergy]
    congr 1
    funext S
    rw [sum_ite_mem, inter_eq_right.2 S.subset]
  have hH : expectation (unif (blSlice U (k + 1))) (fun S => ∑ j ∈ U, H j S) =
      ((((k + 1 : ℕ) : ℝ) - 1) * c' + ((U.card : ℝ) - (k + 1 : ℕ) - 1) * c'') *
        blEnergy U (k + 1) g := by
    rw [blEnergy, ← expectation_const_mul]
    congr 1
    funext S
    have hcard : (((U \ (S : Finset α)).card : ℕ) : ℝ) = U.card - (k + 1 : ℕ) := by
      have h := card_sdiff_add_card_eq_card S.subset
      rw [S.card_eq] at h
      rw [eq_sub_iff_add_eq]
      exact_mod_cast h
    have h₁ : ∑ j ∈ (S : Finset α), H j S =
        c' * (((S : Finset α).card : ℝ) * ∑ a ∈ (S : Finset α), ∑ b ∈ U \ (S : Finset α),
          q S a b - ∑ a ∈ (S : Finset α), ∑ b ∈ U \ (S : Finset α), q S a b) := by
      rw [← nsmul_eq_mul, ← sum_const, ← sum_sub_distrib, mul_sum]
      refine sum_congr rfl fun j hj => ?_
      simp only [H, if_pos hj, sum_erase_eq_sub hj]
    have h₂ : ∑ j ∈ U \ (S : Finset α), H j S =
        c'' * (((U \ (S : Finset α)).card : ℝ) * ∑ a ∈ (S : Finset α),
          ∑ b ∈ U \ (S : Finset α), q S a b -
            ∑ a ∈ (S : Finset α), ∑ b ∈ U \ (S : Finset α), q S a b) := by
      have hj' : ∀ j ∈ U \ (S : Finset α), H j S = c'' * (∑ a ∈ (S : Finset α),
          ∑ b ∈ U \ (S : Finset α), q S a b - ∑ a ∈ (S : Finset α), q S a j) := fun j hj => by
        simp only [H, if_neg (mem_sdiff.1 hj).2, erase_sdiff_comm]
        congr 1
        rw [← sum_sub_distrib]
        exact sum_congr rfl fun a _ => sum_erase_eq_sub hj
      rw [sum_congr rfl hj', ← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul,
        sum_comm (s := U \ (S : Finset α)) (t := (S : Finset α))]
    rw [← sum_sdiff S.subset, h₁, h₂, hcard, S.card_eq]
    ring
  rw [hE, hH] at hsum
  have hN : (0 : ℝ) < U.card := by exact_mod_cast (by omega : 0 < U.card)
  have hD := blEnergy_nonneg U (k + 1) g
  rw [show ∀ L C : ℝ, (6 / (U.card : ℝ) ^ 2 * L + C / U.card) * blEnergy U (k + 1) g =
      (6 / U.card * L * blEnergy U (k + 1) g + C * blEnergy U (k + 1) g) / U.card by
    intro L C; field_simp, le_div_iff₀ hN]
  linarith

end CycleCutoff
