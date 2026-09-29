/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Integrated.Defs
public import CycleCutoff.Integrated.SeparationLaw
public import CycleCutoff.Generator.SemigroupRowsum
public import CycleCutoff.Generator.SemigroupSymmetric

/-!
# The coincidence probability as a correlation

For every `t`, `C_{n,m}(t) - 1/m = m ⟨v, P^{𝒯_{n,m}}_t v⟩_{ϖ_{n,m}}`, where `v = 1[X = Y] - 1/m` is
the centred coincidence indicator.

## Main results

* `CycleCutoff.coincidenceProb_sub_eq_innerP`: `C_{n,m}(t) - 1/m = m ⟨v, P_t v⟩_ϖ`.

## Implementation notes

The identity is stated for every real `t`, every `n ≥ 1` and every `m ≤ n`. For `m = 0` the state
space is empty and both sides vanish.
-/

public section

open Finset Matrix

namespace CycleCutoff

variable {n : ℕ} [NeZero n] {m : ℕ}

/-- **Coincidence as a correlation**: `C_{n,m}(t) - 1/m = m ⟨v, P^{𝒯_{n,m}}_t v⟩_{ϖ_{n,m}}`. -/
@[cycle_cutoff "lem_coincidence_correlation"]
theorem coincidenceProb_sub_eq_innerP (hm : m ≤ n) (t : ℝ) :
    coincidenceProb n m t - 1 / (m : ℝ) =
      m * innerP (unif (TwoCopyState (ZMod n) m)) (centredCoincidence n m)
        ((twoCopy n m).semigroup t *ᵥ centredCoincidence n m) := by
  set P := (twoCopy n m).semigroup t
  set u := (Fintype.card (TwoCopyState (ZMod n) m) : ℝ)⁻¹
  set D : TwoCopyState (ZMod n) m → ℝ := fun w => if w.x = w.y then 1 else 0
  have hcard : (Fintype.card (TwoCopyState (ZMod n) m) : ℝ) = (n.choose m : ℝ) * m * m := by
    rw [TwoCopyState.card_eq, ZMod.card]; push_cast; ring
  have hζ : (((n.choose m : ℕ) : ℝ) * m)⁻¹ = m * u := by
    rcases Nat.eq_zero_or_pos m with rfl | hm₁
    · simp
    have : (m : ℝ) ≠ 0 := by exact_mod_cast hm₁.ne'
    rw [show u = ((n.choose m : ℝ) * m * m)⁻¹ from by rw [← hcard]]
    field_simp
  have hD : ∑ w, u * D w = 1 / (m : ℝ) := by
    have h := expectation_indicator_x_sub_y_eq hm 0
    simp only [if_true, sub_eq_zero, expectation, unif] at h
    exact h
  have hPD : ∑ w, u * (P *ᵥ D) w = 1 / (m : ℝ) := by
    rw [← hD]
    simp only [mulVec, dotProduct, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun w' _ => ?_
    calc ∑ w, u * (P w w' * D w') = u * D w' * ∑ w, P w' w := by
          rw [mul_sum]
          exact sum_congr rfl fun w _ => by
            rw [show P w w' = P w' w from (twoCopy n m).semigroup_apply_comm t w w']; ring
      _ = u * D w' := by rw [(twoCopy n m).sum_semigroup_apply t w', mul_one]
  have hPv : P *ᵥ centredCoincidence n m = P *ᵥ D - fun _ => 1 / (m : ℝ) := by
    have hv : centredCoincidence n m = D - fun _ => 1 / (m : ℝ) := by
      funext w; simp [centredCoincidence_apply, D]
    rw [hv, mulVec_sub]
    congr 1
    funext w
    simp [mulVec, dotProduct, ← sum_mul, P, (twoCopy n m).sum_semigroup_apply]
  have hC : coincidenceProb n m t = m * ∑ w, u * (D w * (P *ᵥ D) w) := by
    rw [coincidenceProb, sum_filter, mul_sum]
    refine sum_congr rfl fun w _ => ?_
    rw [exposureWeight_of_mem w.card_R w.x_mem, hζ]
    simp only [D, mulVec, dotProduct, sum_filter]
    split_ifs <;> simp [mul_ite, P]; ring
  rw [hPv, hC, innerP, expectation]
  change _ = (m : ℝ) * ∑ w, u * ((D w - 1 / (m : ℝ)) * ((P *ᵥ D) w - 1 / (m : ℝ)))
  have hexp : ∑ w, u * ((D w - 1 / (m : ℝ)) * ((P *ᵥ D) w - 1 / (m : ℝ))) =
      ∑ w, u * (D w * (P *ᵥ D) w) - 1 / (m : ℝ) * ∑ w, u * D w -
        1 / (m : ℝ) * ∑ w, u * (P *ᵥ D) w +
          (1 / (m : ℝ)) ^ 2 * ∑ _w : TwoCopyState (ZMod n) m, u := by
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun _ _ => by ring
  have hu : ∑ w : TwoCopyState (ZMod n) m, u = 1 / (m : ℝ) * m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm₁
    · simp [u, hcard]
    have : (m : ℝ) ≠ 0 := by exact_mod_cast hm₁.ne'
    have hC0 : (n.choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hm).ne'
    simp only [sum_const, card_univ, nsmul_eq_mul, u, hcard]
    field_simp
  rw [hexp, hD, hPD, hu]
  rcases Nat.eq_zero_or_pos m with rfl | hm₁
  · simp
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm₁.ne'
  field_simp
  ring

end CycleCutoff
