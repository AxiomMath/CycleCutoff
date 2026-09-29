/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Integrated.Defs
public import CycleCutoff.LocalGap.CycleTwoCopyPoincare
public import CycleCutoff.Integrated.CoincidenceCorrelation
public import CycleCutoff.Generator.CorrelationRepresentation
public import CycleCutoff.Integrated.SeparationLaw
public import CycleCutoff.Generator.PoissonSolvable
public import CycleCutoff.Integrated.SourceOrthogonal
public import CycleCutoff.Integrated.CorrectorIdentity
public import CycleCutoff.Generator.HMinusOneAttained

/-!
# The integrated coincidence

For `n ≥ 3` and `1 ≤ m ≤ n`,
`∫_0^∞ (C_{n,m}(t) - 1/m) dt = n(m-1)(n+1)/(24m²) + (n-1)²/(4m) 𝓡_{n,m}`.

## Main results

* `CycleCutoff.integral_coincidenceProb_sub`: the value of `∫_0^∞ (C_{n,m}(t) - 1/m) dt`.

## Implementation notes

The integral over `[0, ∞)` is taken over `Set.Ioi 0`, which differs from `Set.Ici 0` by a null set.
-/

public section

open Finset Matrix MeasureTheory

namespace CycleCutoff

variable {n : ℕ} [NeZero n] {m : ℕ}

/-- **The integrated coincidence.**
`∫_0^∞ (C_{n,m}(t) - 1/m) dt = n(m-1)(n+1)/(24m²) + (n-1)²/(4m) 𝓡_{n,m}`. -/
@[cycle_cutoff "lem_return_integral"]
theorem integral_coincidenceProb_sub (hn : 3 ≤ n) (hm₁ : 1 ≤ m) (hm : m ≤ n) :
    ∫ t in Set.Ioi 0, (coincidenceProb n m t - 1 / (m : ℝ)) =
      (n : ℝ) * ((m : ℝ) - 1) * ((n : ℝ) + 1) / (24 * (m : ℝ) ^ 2) +
        ((n : ℝ) - 1) ^ 2 / (4 * m) * resolventQuantity n m := by
  set 𝒯 := twoCopy n m
  set ϖ := unif (TwoCopyState (ZMod n) m)
  set v := centredCoincidence n m
  set b := twoCopySource n m
  set φ : TwoCopyState (ZMod n) m → ℝ := fun w => corrector n m (w.x - w.y)
  set a : ℝ := ((n : ℝ) - 1) / (2 * m) with ha
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  obtain ⟨K, hK, hP⟩ := exists_variance_le_twoCopy
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hA : 0 < K * (n : ℝ) ^ 2 := by positivity
  have hPn : ∀ f, variance ϖ f ≤ K * (n : ℝ) ^ 2 * 𝒯.dirichletForm f := hP n m
  have hcard : (Fintype.card (TwoCopyState (ZMod n) m) : ℝ) ≠ 0 := by
    rw [TwoCopyState.card_eq, ZMod.card]
    have := Nat.choose_pos hm
    exact_mod_cast (by positivity : 0 < n.choose m * m * m).ne'
  have hconst : ∀ c : ℝ, expectation ϖ (fun _ => c) = c := fun c => by
    rw [expectation_unif, sum_const, card_univ, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hcard, one_mul]
  have hD : expectation ϖ (fun w => if w.x = w.y then 1 else 0) = 1 / (m : ℝ) := by
    have h := expectation_indicator_x_sub_y_eq hm (0 : ZMod n)
    simpa only [sub_eq_zero, if_true] using h
  have hv : expectation ϖ v = 0 := by
    change expectation ϖ (fun w => (if w.x = w.y then 1 else 0) - 1 / (m : ℝ)) = 0
    rw [expectation_sub, hD, hconst, sub_self]
  have hint : ∫ t in Set.Ioi 0, (coincidenceProb n m t - 1 / (m : ℝ)) =
      m * 𝒯.hMinusOneNormSq v := by
    simp_rw [coincidenceProb_sub_eq_innerP hm]
    rw [integral_const_mul, 𝒯.integral_innerP_semigroup _ hA hPn v hv]
  have hb : expectation ϖ b = 0 := by
    have h := innerP_twoCopySource_comp_sub_eq_zero (by omega) hm (fun _ => (1 : ℝ))
    simpa [innerP] using h
  obtain ⟨ψ, hψ⟩ := 𝒯.exists_neg_generator_eq _ hPn b hb
  have hgen : ∀ (f g : TwoCopyState (ZMod n) m → ℝ) (c : ℝ) w,
      𝒯.generator (fun w => f w - c * g w) w = 𝒯.generator f w - c * 𝒯.generator g w := by
    intro f g c w
    simp only [InvFamily.generator, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun _ _ => by ring
  have hcorr := neg_twoCopy_generator_corrector hn hm₁
  have hu : (fun w => -𝒯.generator (fun w => φ w - a * ψ w) w) = v := by
    funext w
    have h1 := congrFun hcorr w
    have h2 := congrFun hψ w
    rw [hgen]
    change -𝒯.generator φ w = v w + a * b w at h1
    linear_combination h1 - a * h2
  have hnorm : 𝒯.hMinusOneNormSq v = innerP ϖ v φ - a * innerP ϖ v ψ := by
    rw [𝒯.hMinusOneNormSq_eq hu]
    simp only [innerP, mul_sub, expectation_sub]
    rw [← expectation_const_mul]
    congr 2
    funext w
    ring
  have hR : resolventQuantity n m = innerP ϖ b ψ := 𝒯.hMinusOneNormSq_eq hψ
  have hvψ : innerP ϖ v ψ = -a * resolventQuantity n m := by
    have hvφ : v = fun w => -𝒯.generator φ w - a * b w := by
      funext w
      have h1 := congrFun hcorr w
      change -𝒯.generator φ w = v w + a * b w at h1
      linarith
    have hbφ : innerP ϖ b φ = 0 := innerP_twoCopySource_comp_sub_eq_zero (by omega) hm _
    have hsym : innerP ϖ (fun w => -𝒯.generator φ w) ψ = innerP ϖ b φ := by
      calc innerP ϖ (fun w => -𝒯.generator φ w) ψ = -innerP ϖ (𝒯.generator φ) ψ := by
            simp [innerP, neg_mul]
        _ = -innerP ϖ φ (𝒯.generator ψ) := by rw [𝒯.innerP_generator_comm]
        _ = innerP ϖ φ (fun w => -𝒯.generator ψ w) := by simp [innerP, mul_neg]
        _ = innerP ϖ b φ := by rw [hψ]; simp only [innerP, mul_comm]
    rw [hR, hvφ]
    calc innerP ϖ (fun w => -𝒯.generator φ w - a * b w) ψ
        = innerP ϖ (fun w => -𝒯.generator φ w) ψ - a * innerP ϖ b ψ := by
          simp only [innerP, sub_mul, expectation_sub]
          rw [← expectation_const_mul]
          congr 2
          funext w
          ring
      _ = -a * innerP ϖ b ψ := by rw [hsym, hbφ]; ring
  set c₀ : ℝ := (n : ℝ) * ((m : ℝ) - 1) * ((n : ℝ) + 1) / (24 * (m : ℝ) ^ 2)
  have hφ0 : corrector n m 0 = c₀ := by simp [corrector_apply, c₀]
  have hEφ : expectation ϖ φ = 0 := by
    have hsplit :
        φ = fun w => ∑ r : ZMod n, corrector n m r * (if w.x - w.y = r then 1 else 0) :=
      funext fun w => by simp [φ]
    have hsum : expectation ϖ φ =
        ∑ r : ZMod n, corrector n m r *
          expectation ϖ (fun w => if w.x - w.y = r then 1 else 0) := by
      rw [hsplit]
      simp only [expectation_def, mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    rw [hsum]
    simp only [ϖ, expectation_indicator_x_sub_y_eq hm]
    set q : ℝ := ((m : ℝ) - 1) / ((m : ℝ) * ((n : ℝ) - 1))
    have hterm : ∀ r : ZMod n, corrector n m r * (if r = 0 then 1 / (m : ℝ) else q) =
        q * corrector n m r + (if r = 0 then (1 / (m : ℝ) - q) * c₀ else 0) := by
      intro r
      split_ifs with hr
      · rw [hr, hφ0]; ring
      · ring
    simp only [hterm, sum_add_distrib, ← mul_sum, sum_ite_eq', mem_univ, if_true]
    have hsumφ : ∑ r : ZMod n, corrector n m r =
        n * c₀ - (n : ℝ) * (n - 1) * (n + 1) / 6 / (4 * m) := by
      simp only [corrector_apply, sum_sub_distrib, sum_const, card_univ, ZMod.card,
        nsmul_eq_mul, ← sum_div, sum_val_mul_sub_val, c₀]
    rw [hsumφ]
    have hn1 : (n : ℝ) - 1 ≠ 0 := by
      have : (3 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    simp only [q, c₀]
    field_simp
    ring
  have hvφ : innerP ϖ v φ = c₀ / m := by
    have hpt : (fun w => v w * φ w) =
        fun w => c₀ * (if w.x = w.y then 1 else 0) - 1 / (m : ℝ) * φ w := by
      funext w
      simp only [v, centredCoincidence_apply, φ]
      split_ifs with h
      · rw [h, sub_self, hφ0]; ring
      · ring
    rw [innerP, hpt, expectation_sub, expectation_const_mul, expectation_const_mul, hD, hEφ]
    ring
  rw [hint, hnorm, hvφ, hvψ, ha]
  field_simp
  ring

end CycleCutoff
