/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.BernoulliLaplace.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Lee--Yau constant is a supersolution of the slice recursion

For `k₁, k₂ ≥ 1` with `n = k₁ + k₂ ≥ 3`, the constant
`Φ_BL(k₁, k₂) = 3n(5 + log(n/k₁) + log(n/k₂))` satisfies
`3(1 + log(n/k₁) + log(n/k₂)) + ((k₁-1)Φ_BL(k₁-1,k₂) + (k₂-1)Φ_BL(k₁,k₂-1))/(n-2) ≤ Φ_BL(k₁,k₂)`.

## Main results

* `CycleCutoff.blPhi_supersolution`: the supersolution inequality.
-/

public section

namespace CycleCutoff

/-- The colour-one half `Φ¹(k₁, k₂) = 3n(5/2 + log(n/k₁))` of `blPhi`, `n = k₁ + k₂`. -/
private noncomputable def blPhiHalf (k₁ k₂ : ℕ) : ℝ :=
  3 * ((k₁ + k₂ : ℕ) : ℝ) * (5 / 2 + Real.log (((k₁ + k₂ : ℕ) : ℝ) / k₁))

private lemma blPhi_eq_add (k₁ k₂ : ℕ) : blPhi k₁ k₂ = blPhiHalf k₁ k₂ + blPhiHalf k₂ k₁ := by
  simp only [blPhi, blPhiHalf, Nat.add_comm k₂ k₁]
  ring

/-- The colour-one inequality in real variables, case `k₁ ≥ 2`. -/
private lemma half_ineq_of_two_le (a b : ℝ) (ha : 2 ≤ a) (hb : 1 ≤ b) :
    3 * (1 / 2 + Real.log ((a + b) / a)) +
        ((a - 1) * (3 * (a - 1 + b) * (5 / 2 + Real.log ((a - 1 + b) / (a - 1)))) +
          (b - 1) * (3 * (a + (b - 1)) * (5 / 2 + Real.log ((a + (b - 1)) / a)))) /
          (a + b - 2) ≤
      3 * (a + b) * (5 / 2 + Real.log ((a + b) / a)) := by
  have hpos : 0 < a + b - 2 := by linarith
  have ha0 : 0 < a := by linarith
  have ha1 : 0 < a - 1 := by linarith
  have hn0 : 0 < a + b := by linarith
  have hn1 : 0 < a + b - 1 := by linarith
  have e1 : a - 1 + b = a + b - 1 := by ring
  have e2 : a + (b - 1) = a + b - 1 := by ring
  rw [e1, e2, Real.log_div hn0.ne' ha0.ne', Real.log_div hn1.ne' ha1.ne',
    Real.log_div hn1.ne' ha0.ne']
  have hδ : (a - 1) * (Real.log a - Real.log (a - 1)) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos ha0 ha1)
    rw [Real.log_div ha0.ne' ha1.ne'] at h
    have : a / (a - 1) - 1 = 1 / (a - 1) := by field_simp; ring
    rw [this] at h
    have := mul_le_mul_of_nonneg_left h ha1.le
    rwa [mul_one_div_cancel ha1.ne'] at this
  have hlog : Real.log (a + b - 1) ≤ Real.log (a + b) :=
    Real.log_le_log hn1 (by linarith)
  have h1 : (a + b - 1) * ((a - 1) * (Real.log a - Real.log (a - 1))) ≤ (a + b - 1) * 1 :=
    mul_le_mul_of_nonneg_left hδ hn1.le
  have h2 : 0 ≤ (a + b - 2) * (a + b - 1) * (Real.log (a + b) - Real.log (a + b - 1)) :=
    mul_nonneg (mul_nonneg hpos.le hn1.le) (by linarith)
  rw [add_comm, ← le_sub_iff_add_le, div_le_iff₀ hpos]
  nlinarith [h1, h2]

/-- The colour-one inequality in real variables, case `k₁ = 1`. -/
private lemma half_ineq_of_one (b : ℝ) (hb : 2 ≤ b) :
    3 * (1 / 2 + Real.log ((1 + b) / 1)) +
        (b - 1) * (3 * (1 + (b - 1)) * (5 / 2 + Real.log ((1 + (b - 1)) / 1))) / (1 + b - 2) ≤
      3 * (1 + b) * (5 / 2 + Real.log ((1 + b) / 1)) := by
  have hb1 : (b - 1) ≠ 0 := by linarith
  have e : 1 + b - 2 = b - 1 := by ring
  have e' : 1 + (b - 1) = b := by ring
  rw [e, e', mul_div_cancel_left₀ _ hb1, div_one, div_one]
  have hlog : Real.log b ≤ Real.log (1 + b) := Real.log_le_log (by linarith) (by linarith)
  have hlog0 : 0 ≤ Real.log (1 + b) := Real.log_nonneg (by linarith)
  have h : 0 ≤ b * (Real.log (1 + b) - Real.log b) := mul_nonneg (by linarith) (by linarith)
  nlinarith [h]

/-- The colour-one inequality: `3(1/2 + log(n/k₁)) + avg(Φ¹) ≤ Φ¹(k₁, k₂)`. -/
private lemma blPhiHalf_supersolution (k₁ k₂ : ℕ) (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂)
    (hn : 3 ≤ k₁ + k₂) :
    3 * (1 / 2 + Real.log (((k₁ + k₂ : ℕ) : ℝ) / k₁)) +
        (((k₁ : ℝ) - 1) * blPhiHalf (k₁ - 1) k₂ + ((k₂ : ℝ) - 1) * blPhiHalf k₁ (k₂ - 1)) /
          (((k₁ + k₂ : ℕ) : ℝ) - 2) ≤
      blPhiHalf k₁ k₂ := by
  rcases Nat.lt_or_ge k₁ 2 with h | h
  · obtain rfl : k₁ = 1 := by omega
    have hb : (2 : ℝ) ≤ k₂ := by exact_mod_cast (by omega : 2 ≤ k₂)
    simpa only [blPhiHalf, Nat.cast_add, Nat.cast_sub hk₂, Nat.cast_one, sub_self, zero_mul,
      zero_add] using half_ineq_of_one (k₂ : ℝ) hb
  · have ha : (2 : ℝ) ≤ k₁ := by exact_mod_cast h
    have hb : (1 : ℝ) ≤ k₂ := by exact_mod_cast hk₂
    simpa only [blPhiHalf, Nat.cast_add, Nat.cast_sub hk₂, Nat.cast_sub hk₁, Nat.cast_one] using
      half_ineq_of_two_le (k₁ : ℝ) (k₂ : ℝ) ha hb

/-- **Supersolution of the recursion.** For `k₁, k₂ ≥ 1` with `n = k₁ + k₂ ≥ 3`,
`3(1 + log(n/k₁) + log(n/k₂)) + ((k₁-1)Φ_BL(k₁-1,k₂) + (k₂-1)Φ_BL(k₁,k₂-1))/(n-2)
≤ Φ_BL(k₁,k₂)`. -/
@[cycle_cutoff "lem_bl_phi_supersolution"]
theorem blPhi_supersolution (k₁ k₂ : ℕ) (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (hn : 3 ≤ k₁ + k₂) :
    3 * (1 + Real.log (((k₁ + k₂ : ℕ) : ℝ) / k₁) + Real.log (((k₁ + k₂ : ℕ) : ℝ) / k₂)) +
        (((k₁ : ℝ) - 1) * blPhi (k₁ - 1) k₂ + ((k₂ : ℝ) - 1) * blPhi k₁ (k₂ - 1)) /
          (((k₁ + k₂ : ℕ) : ℝ) - 2) ≤
      blPhi k₁ k₂ := by
  have h₁ := blPhiHalf_supersolution k₁ k₂ hk₁ hk₂ hn
  have h₂ := blPhiHalf_supersolution k₂ k₁ hk₂ hk₁ (by omega)
  rw [Nat.add_comm k₂ k₁] at h₂
  rw [blPhi_eq_add, blPhi_eq_add, blPhi_eq_add]
  have e :
      (((k₁ : ℝ) - 1) * (blPhiHalf (k₁ - 1) k₂ + blPhiHalf k₂ (k₁ - 1)) +
          ((k₂ : ℝ) - 1) * (blPhiHalf k₁ (k₂ - 1) + blPhiHalf (k₂ - 1) k₁)) /
          (((k₁ + k₂ : ℕ) : ℝ) - 2) =
        (((k₁ : ℝ) - 1) * blPhiHalf (k₁ - 1) k₂ + ((k₂ : ℝ) - 1) * blPhiHalf k₁ (k₂ - 1)) /
            (((k₁ + k₂ : ℕ) : ℝ) - 2) +
          (((k₂ : ℝ) - 1) * blPhiHalf (k₂ - 1) k₁ + ((k₁ : ℝ) - 1) * blPhiHalf k₂ (k₁ - 1)) /
            (((k₁ + k₂ : ℕ) : ℝ) - 2) := by
    rw [← add_div]; ring_nf
  rw [e]
  linarith

end CycleCutoff
