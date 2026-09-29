/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.BernoulliLaplace.Recursion
public import CycleCutoff.BernoulliLaplace.PhiSupersolution

/-!
# The log-Sobolev inequality for the Bernoulli--Laplace slice

Let `U` be a finite set with `|U| = N`, let `1 ≤ k ≤ N - 1`, and let `u` be the uniform
measure on the slice `Ω_{U,k}`. For every `g : Ω_{U,k} → ℝ`,
`Ent_u(g²) ≤ 2 Φ_BL(k, N - k) / (N (N - 1)) · 𝒟^BL_{U,k}(g)`.

## Main results

* `CycleCutoff.ent_sq_le_blEnergy`: the log-Sobolev inequality above.
-/

public section

open Finset

namespace CycleCutoff

variable {α : Type*} [DecidableEq α]

/-- For real `n ≥ 3` and `A ≥ 0`, the inequality `hS` bounds the coefficient of the Lee--Yau
recursion with constants `2P'/((n-1)(n-2))` and `2P''/((n-1)(n-2))` by `2P/(n(n-1))`. -/
private lemma coeff_le_of_supersolution {n k A P' P'' P : ℝ} (hn : 3 ≤ n) (hA : 0 ≤ A)
    (hS : 3 * A + ((k - 1) * P' + (n - k - 1) * P'') / (n - 2) ≤ P) :
    6 / n ^ 2 * A + ((k - 1) * (2 * P' / ((n - 1) * (n - 2))) +
        (n - k - 1) * (2 * P'' / ((n - 1) * (n - 2)))) / n ≤
      2 * P / (n * (n - 1)) := by
  have h1 : n - 1 ≠ 0 := by linarith
  have h2 : n - 2 ≠ 0 := by linarith
  have h0 : n ≠ 0 := by linarith
  have key : 6 / n ^ 2 * A + ((k - 1) * (2 * P' / ((n - 1) * (n - 2))) +
        (n - k - 1) * (2 * P'' / ((n - 1) * (n - 2)))) / n =
      2 / (n * (n - 1)) * ((n - 1) / n * (3 * A) +
        ((k - 1) * P' + (n - k - 1) * P'') / (n - 2)) := by
    field_simp
    ring
  have hfrac : (n - 1) / n * (3 * A) ≤ 3 * A :=
    mul_le_of_le_one_left (by linarith) ((div_le_one (by linarith)).2 (by linarith))
  rw [key, show 2 * P / (n * (n - 1)) = 2 / (n * (n - 1)) * P by ring]
  exact mul_le_mul_of_nonneg_left (by linarith)
    (div_nonneg zero_le_two (mul_nonneg (by linarith) (by linarith)))

/-- **Bernoulli--Laplace log-Sobolev inequality.** For a finite set `U` with `|U| = N` and
`1 ≤ k ≤ N - 1`, every `g : Ω_{U,k} → ℝ` satisfies
`Ent_u(g²) ≤ 2 Φ_BL(k, N - k) / (N (N - 1)) · 𝒟^BL_{U,k}(g)`. -/
@[cycle_cutoff "lem_bl_lsi"]
theorem ent_sq_le_blEnergy (U : Finset α) (k : ℕ) (hk : 1 ≤ k) (hkU : k < U.card)
    (g : blSlice U k → ℝ) :
    ent (unif (blSlice U k)) (fun S => g S ^ 2) ≤
      2 * blPhi k (U.card - k) / ((U.card : ℝ) * ((U.card : ℝ) - 1)) * blEnergy U k g := by
  obtain ⟨N, hN⟩ : ∃ N, U.card = N := ⟨_, rfl⟩
  induction N using Nat.strong_induction_on generalizing U k with
  | _ N ih =>
  subst hN
  have hn2 : (2 : ℝ) ≤ U.card := by exact_mod_cast (show 2 ≤ U.card by omega)
  have hden : 0 ≤ ((U.card : ℝ) - 1) * ((U.card : ℝ) - 2) :=
    mul_nonneg (by linarith) (by linarith)
  have e₂ : ((U.card - 1 : ℕ) : ℝ) = (U.card : ℝ) - 1 := Nat.cast_pred (by omega)
  refine (ent_sq_le_blEnergy_of_erase U k hk hkU
    (2 * blPhi (k - 1) (U.card - k) / (((U.card : ℝ) - 1) * ((U.card : ℝ) - 2)))
    (2 * blPhi k (U.card - k - 1) / (((U.card : ℝ) - 1) * ((U.card : ℝ) - 2)))
    (div_nonneg (mul_nonneg zero_le_two (blPhi_nonneg _ _)) hden)
    (div_nonneg (mul_nonneg zero_le_two (blPhi_nonneg _ _)) hden) ?_ ?_ g).trans ?_
  · intro j hj hk2 g'
    have hcard : (U.erase j).card = U.card - 1 := card_erase_of_mem hj
    have h := ih (U.card - 1) (by omega) (U.erase j) (k - 1) (by omega) (by omega) g' hcard
    rw [hcard, show U.card - 1 - (k - 1) = U.card - k by omega, e₂] at h
    exact h.trans_eq (by ring_nf)
  · intro j hj hk2 g''
    have hcard : (U.erase j).card = U.card - 1 := card_erase_of_mem hj
    have h := ih (U.card - 1) (by omega) (U.erase j) k hk (by omega) g'' hcard
    rw [hcard, show U.card - 1 - k = U.card - k - 1 by omega, e₂] at h
    exact h.trans_eq (by ring_nf)
  · refine mul_le_mul_of_nonneg_right ?_ (blEnergy_nonneg U k g)
    have ecast : ((U.card - k : ℕ) : ℝ) = (U.card : ℝ) - k := Nat.cast_sub hkU.le
    have hL₁ : 0 ≤ Real.log ((U.card : ℝ) / k) := log_natCast_div_nonneg hkU.le
    have hL₂ : 0 ≤ Real.log ((U.card : ℝ) / ((U.card : ℝ) - k)) := by
      rw [← ecast]; exact log_natCast_div_nonneg (by omega)
    rcases (show U.card = 2 ∨ 3 ≤ U.card by omega) with h2 | h3
    · obtain rfl : k = 1 := by omega
      rw [h2] at hL₁ hL₂ ⊢
      simp only [blPhi] at hL₁ hL₂ ⊢
      norm_num at hL₁ hL₂ ⊢
      nlinarith
    · have hS := blPhi_supersolution k (U.card - k) hk (by omega) (by omega)
      rw [Nat.add_sub_cancel' hkU.le, ecast] at hS
      exact coeff_le_of_supersolution (by exact_mod_cast h3) (by linarith) hS

end CycleCutoff
