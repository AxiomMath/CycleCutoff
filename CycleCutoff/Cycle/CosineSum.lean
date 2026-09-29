/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Orthogonality of the cosine modes on `ℤ/nℤ`

For `x ∈ ℤ`, `∑_{j<n} cos(2πjx/n) = n · 1[n ∣ x]`, the real part of the geometric sum of the
`x`-th power of a primitive `n`-th root of unity.

## Main results

* `CycleCutoff.sum_range_cos_two_pi_mul_div`: `∑_{j<n} cos(2πjx/n) = n · 1[n ∣ x]`.
* `CycleCutoff.cos_two_pi_mul_val_div`: `cos(2πjx/n)` depends only on `x mod n`.
-/

public section

open Finset

namespace CycleCutoff

/-- Orthogonality of the cosine modes: `∑_{j<n} cos(2πjx/n) = n · 1[n ∣ x]`. -/
theorem sum_range_cos_two_pi_mul_div {n : ℕ} (hn : n ≠ 0) (x : ℤ) :
    ∑ j ∈ range n, Real.cos (2 * Real.pi * j * x / n) = if (n : ℤ) ∣ x then (n : ℝ) else 0 := by
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : ℂ, ζ = Complex.exp (2 * Real.pi * Complex.I / n) := ⟨_, rfl⟩
  have hζ : IsPrimitiveRoot ζ n := hζdef ▸ Complex.isPrimitiveRoot_exp n hn
  have hterm : ∀ j : ℕ, Real.cos (2 * Real.pi * j * x / n) = ((ζ ^ x) ^ j).re := by
    intro j
    rw [hζdef, ← Complex.exp_int_mul, ← Complex.exp_nat_mul, ← Complex.exp_ofReal_mul_I_re]
    congr 2
    push_cast
    ring
  simp_rw [hterm, ← Complex.re_sum]
  split_ifs with hdvd
  · rw [(hζ.zpow_eq_one_iff_dvd x).2 hdvd]
    simp
  · have hne : ζ ^ x ≠ 1 := mt (hζ.zpow_eq_one_iff_dvd x).1 hdvd
    have hpow : (ζ ^ x) ^ n = 1 := by
      rw [← zpow_natCast, ← _root_.zpow_mul, hζ.zpow_eq_one_iff_dvd]
      exact dvd_mul_left _ _
    rw [geom_sum_eq hne, hpow, sub_self, zero_div, Complex.zero_re]

/-- The angle `2πj·x/n` depends on the integer `x` only through its class in `ℤ/nℤ`:
`cos(2πj·(x mod n)/n) = cos(2πjx/n)`, reading the class through its representative `val`. -/
theorem cos_two_pi_mul_val_div {n : ℕ} [NeZero n] (j : ℕ) (x : ℤ) :
    Real.cos (2 * Real.pi * j * ((x : ZMod n).val : ℝ) / n) =
      Real.cos (2 * Real.pi * j * x / n) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  have hval : (((x : ZMod n).val : ℕ) : ℝ) = ((x % n : ℤ) : ℝ) := by
    rw [← ZMod.val_intCast, Int.cast_natCast]
  have hx : (x : ℝ) = ((x % n : ℤ) : ℝ) + n * ((x / n : ℤ) : ℝ) :=
    mod_cast (Int.emod_add_mul_ediv x n).symm
  have harg : 2 * Real.pi * j * (x : ℝ) / n =
      2 * Real.pi * j * ((x % n : ℤ) : ℝ) / n + ((j * (x / n) : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hx]
    push_cast
    field_simp
  rw [hval, harg, Real.cos_add_int_mul_two_pi]

end CycleCutoff
