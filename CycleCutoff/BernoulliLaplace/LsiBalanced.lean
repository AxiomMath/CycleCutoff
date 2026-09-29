/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.BernoulliLaplace.Lsi

/-!
# The balanced Bernoulli--Laplace log-Sobolev inequality

Let `U` be a finite set with `|U| = N ≥ 2` and let `k = ⌊N/2⌋`. There is an absolute constant
`c₂ > 0` such that for every `g : Ω_{U,k} → ℝ`, `Ent_u(g²) ≤ c₂ / N · 𝒟^BL_{U,k}(g)`, where `u`
is the uniform measure on the slice; one may take `c₂ = 12 (5 + log 6)`.

## Main results

* `CycleCutoff.exists_ent_sq_le_blEnergy_half`: the balanced inequality (Lee--Yau, Theorem 5).

## References

* [T.-Y. Lee and H.-T. Yau, *Logarithmic Sobolev inequality for some models of random walks*]
-/

public section

open Finset

namespace CycleCutoff

/-- For `N ≥ 2` and `k = ⌊N/2⌋`, the Lee--Yau coefficient is at most `12 (5 + log 6) / N`. -/
private lemma two_mul_blPhi_div_le {N k : ℕ} (hN : 2 ≤ N) (hk : k = N / 2) :
    2 * blPhi k (N - k) / ((N : ℝ) * ((N : ℝ) - 1)) ≤ 12 * (5 + Real.log 6) / N := by
  have hk1 : 1 ≤ k := by omega
  have hkN : k < N := by omega
  have e : k + (N - k) = N := by omega
  have ecast : ((N - k : ℕ) : ℝ) = (N : ℝ) - k := Nat.cast_sub hkN.le
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have h3 : (N : ℝ) ≤ 3 * k := by exact_mod_cast (show N ≤ 3 * k by omega)
  have h2 : (N : ℝ) ≤ 2 * ((N : ℝ) - k) := by
    rw [← ecast]; exact_mod_cast (show N ≤ 2 * (N - k) by omega)
  have hNk : (0 : ℝ) < (N : ℝ) - k := by linarith
  have hpos₁ : (0 : ℝ) < N / k := by positivity
  have hpos₂ : (0 : ℝ) < N / ((N : ℝ) - k) := by positivity
  have hlog : Real.log ((N : ℝ) / k) + Real.log ((N : ℝ) / ((N : ℝ) - k)) ≤ Real.log 6 := by
    rw [← Real.log_mul hpos₁.ne' hpos₂.ne']
    exact Real.log_le_log (mul_pos hpos₁ hpos₂) <|
      (mul_le_mul ((div_le_iff₀ (by linarith)).2 h3) ((div_le_iff₀ hNk).2 h2) hpos₂.le
        (by norm_num)).trans_eq (by norm_num)
  have hL : 0 < 5 + Real.log 6 := by positivity
  have hΦ : blPhi k (N - k) ≤ 3 * N * (5 + Real.log 6) := by
    simp only [blPhi, e, ecast]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [div_le_div_iff₀ (mul_pos (by linarith) (by linarith)) (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_right hΦ (show (0 : ℝ) ≤ 2 * N by linarith),
    mul_pos hL (show (0 : ℝ) < N by linarith)]

/-- **Balanced Bernoulli--Laplace log-Sobolev inequality** (Lee--Yau, Theorem 5). There is an
absolute constant `c₂ > 0` such that for every finite set `U` with `|U| = N ≥ 2`, `k = ⌊N/2⌋`
and every `g : Ω_{U,k} → ℝ`, `Ent_u(g²) ≤ c₂ / N · 𝒟^BL_{U,k}(g)`. -/
@[cycle_cutoff "lem_bl_lsi_balanced"]
theorem exists_ent_sq_le_blEnergy_half :
    ∃ c₂ > 0, ∀ {α : Type*} [DecidableEq α] (U : Finset α) (k : ℕ), 2 ≤ U.card →
      k = U.card / 2 → ∀ g : blSlice U k → ℝ,
        ent (unif (blSlice U k)) (fun S => g S ^ 2) ≤ c₂ / U.card * blEnergy U k g :=
  ⟨12 * (5 + Real.log 6), by positivity, fun U k hN hk g =>
    (ent_sq_le_blEnergy U k (by omega) (by omega) g).trans
      (mul_le_mul_of_nonneg_right (two_mul_blPhi_div_le hN hk) (blEnergy_nonneg U k g))⟩

end CycleCutoff
