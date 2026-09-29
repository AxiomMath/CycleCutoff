/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Cutoff.Defs
public import CycleCutoff.Cycle.CosineSum
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Wilson's statistic has mean zero under the uniform measure

Under the uniform probability vector on `Perm (ℤ/nℤ)`, `n ≥ 2`, Wilson's statistic
`F(σ) = ∑_i cos(2π (σ(i) - i) / n)` has expectation `0`.

## Main results

* `CycleCutoff.sum_cos_two_pi_val_add`: `∑_z cos(2π (z + a) / n) = 0` for `n ≥ 2`.
* `CycleCutoff.expectation_unif_wilsonStat`: `𝔼_{π_n}[F] = 0` for `n ≥ 2`.
-/

public section

open Finset Real

namespace CycleCutoff

variable {n : ℕ} [NeZero n]

/-- The real parts of the `n`-th roots of unity sum to zero: `∑_{k < n} cos(2π k / n) = 0`
for `n ≥ 2`. -/
theorem sum_range_cos_two_pi_div (hn : 2 ≤ n) :
    ∑ k ∈ range n, Real.cos (2 * π * (k : ℝ) / n) = 0 := by
  have h := sum_range_cos_two_pi_mul_div (NeZero.ne n) 1
  have h1 : ¬ n ∣ 1 := fun hd => absurd (Nat.le_of_dvd one_pos hd) (by omega)
  rw [if_neg (by exact_mod_cast h1)] at h
  simpa using h

/-- `∑_{z ∈ ℤ/nℤ} cos(2π z / n) = 0` for `n ≥ 2`. -/
theorem sum_cos_two_pi_val (hn : 2 ≤ n) :
    ∑ z : ZMod n, Real.cos (2 * π * (z.val : ℝ) / n) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← sum_range_cos_two_pi_div hn]
  exact Fin.sum_univ_eq_sum_range (fun k : ℕ => Real.cos (2 * π * (k : ℝ) / (m + 1 : ℕ))) _

/-- Shifted form: `∑_{z ∈ ℤ/nℤ} cos(2π (z + a) / n) = 0` for `n ≥ 2`. -/
theorem sum_cos_two_pi_val_add (hn : 2 ≤ n) (a : ZMod n) :
    ∑ z : ZMod n, Real.cos (2 * π * ((z + a).val : ℝ) / n) = 0 := by
  rw [← sum_cos_two_pi_val hn]
  exact Equiv.sum_comp (Equiv.addRight a) fun z : ZMod n => Real.cos (2 * π * (z.val : ℝ) / n)

/-- Wilson's statistic has mean zero under the uniform measure on `Perm (ℤ/nℤ)`:
`𝔼_{π_n}[F] = 0` for `n ≥ 2`. -/
@[cycle_cutoff "lem_F_stationary_mean"]
theorem expectation_unif_wilsonStat (hn : 2 ≤ n) :
    expectation (unif (Equiv.Perm (ZMod n))) (wilsonStat n) = 0 := by
  rw [expectation_unif]
  suffices h : ∑ σ : Equiv.Perm (ZMod n), wilsonStat n σ = 0 by rw [h, mul_zero]
  simp_rw [wilsonStat_def]
  rw [sum_comm]
  refine sum_eq_zero fun i _ => ?_
  set g : Equiv.Perm (ZMod n) → ℝ := fun σ => Real.cos (2 * π * ((σ i - i : ZMod n).val : ℝ) / n)
  have hshift (k : ZMod n) :
      ∑ σ, g σ = ∑ σ : Equiv.Perm (ZMod n), Real.cos (2 * π * ((σ i - i + k).val : ℝ) / n) := by
    rw [← Equiv.sum_comp (Equiv.mulLeft (Equiv.addRight k)) g]
    refine sum_congr rfl fun σ _ => ?_
    simp only [g, Equiv.coe_mulLeft, Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.coe_addRight]
    ring_nf
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  have key : (n : ℝ) * ∑ σ, g σ = 0 := by
    calc (n : ℝ) * ∑ σ, g σ = ∑ k : ZMod n, ∑ σ, g σ := by simp [ZMod.card]
      _ = ∑ k : ZMod n, ∑ σ : Equiv.Perm (ZMod n),
            Real.cos (2 * π * ((k + (σ i - i)).val : ℝ) / n) := by
          refine sum_congr rfl fun k _ => ?_
          rw [hshift k]
          simp_rw [add_comm (_ - i) k]
      _ = 0 := by
          rw [sum_comm]
          exact sum_eq_zero fun σ _ => sum_cos_two_pi_val_add hn _
  exact (mul_eq_zero.1 key).resolve_left hn'

end CycleCutoff
