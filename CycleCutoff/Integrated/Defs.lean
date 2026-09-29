/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.TwoCopy.Defs
public import CycleCutoff.Generator.HMinusOne

/-!
# The source, the resolvent quantity and the corrector

Functions on the two-copy state space `Ω_{n,m} = {(R, X, Y) : |R| = m, X, Y ∈ R}` over `ℤ/nℤ` that
enter the integrated error: the red-neighbour count, the source `b`, the centred coincidence
indicator `v`, the resolvent quantity `𝓡_{n,m} = ‖b‖²_{-1}` and the corrector `φ`.

## Main definitions

* `CycleCutoff.redNeighbourCount`: `w(R, X, Y) = 1[X - 1 ∈ R] + 1[X + 1 ∈ R]`.
* `CycleCutoff.twoCopySource`: the source `b(R, X, Y) = 1[X = Y] (w(R, X, Y) - 2(m-1)/(n-1))`.
* `CycleCutoff.resolventQuantity`: `𝓡_{n,m} = ‖b‖²_{-1, 𝒯_{n,m}}`.
* `CycleCutoff.centredCoincidence`: `v(R, X, Y) = 1[X = Y] - 1/m`.
* `CycleCutoff.corrector`: `φ(r) = n(m-1)(n+1)/(24m²) - r(n-r)/(4m)`.

## Main results

* `CycleCutoff.sum_val_mul_sub_val`: `∑_{r ∈ ℤ/nℤ} r(n - r) = n(n-1)(n+1)/6`.
* `CycleCutoff.Delta_mulVec_corrector`: `Δφ = 1/(2m) - n/(2m) · 1[· = 0]`.

## Implementation notes

* A state `w : TwoCopyState (ZMod n) m` has coordinates `w.R`, `w.x`, `w.y`, and the uniform
  measure `ϖ_{n,m}` is `unif _`.
* All functions are real-valued, so `2(m-1)/(n-1)` and `1/m` are real divisions.
* The corrector is evaluated on the representative `r.val ∈ {0, …, n-1}` of `r : ℤ/nℤ`.
-/

@[expose] public section

open Finset

namespace CycleCutoff

variable {n m : ℕ}

/-- The red-neighbour count `w(R, X, Y) = 1[X - 1 ∈ R] + 1[X + 1 ∈ R]`. -/
@[cycle_cutoff "def_red_neighbour_count"]
def redNeighbourCount (w : TwoCopyState (ZMod n) m) : ℝ :=
  (if w.x - 1 ∈ w.R then 1 else 0) + (if w.x + 1 ∈ w.R then 1 else 0)

variable (n m)

/-- The source function `b(R, X, Y) = 1[X = Y] (w(R, X, Y) - 2(m-1)/(n-1))`. -/
@[cycle_cutoff "def_source"]
noncomputable def twoCopySource (w : TwoCopyState (ZMod n) m) : ℝ :=
  if w.x = w.y then redNeighbourCount w - 2 * ((m : ℝ) - 1) / ((n : ℝ) - 1) else 0

/-- The resolvent quantity `𝓡_{n,m} = ‖b‖²_{-1, 𝒯_{n,m}}`. -/
@[cycle_cutoff "def_Rnm"]
noncomputable def resolventQuantity [NeZero n] : ℝ :=
  (twoCopy n m).hMinusOneNormSq (twoCopySource n m)

/-- The centred coincidence indicator `v(R, X, Y) = 1[X = Y] - 1/m`. -/
@[cycle_cutoff "def_v_function"]
noncomputable def centredCoincidence (w : TwoCopyState (ZMod n) m) : ℝ :=
  (if w.x = w.y then 1 else 0) - 1 / (m : ℝ)

/-- The corrector `φ(r) = n(m-1)(n+1)/(24m²) - r(n-r)/(4m)`, evaluated on the representative
`r.val ∈ {0, …, n-1}` of `r : ℤ/nℤ`. -/
@[cycle_cutoff "def_corrector"]
noncomputable def corrector (r : ZMod n) : ℝ :=
  (n : ℝ) * ((m : ℝ) - 1) * ((n : ℝ) + 1) / (24 * (m : ℝ) ^ 2) -
    (r.val : ℝ) * ((n : ℝ) - r.val) / (4 * m)

variable {n m}

/-- The defining formula of the red-neighbour count. -/
theorem redNeighbourCount_apply (w : TwoCopyState (ZMod n) m) :
    redNeighbourCount w =
      (if w.x - 1 ∈ w.R then 1 else 0) + (if w.x + 1 ∈ w.R then 1 else 0) := rfl

/-- The defining formula of the source `b`. -/
theorem twoCopySource_apply (w : TwoCopyState (ZMod n) m) :
    twoCopySource n m w =
      if w.x = w.y then redNeighbourCount w - 2 * ((m : ℝ) - 1) / ((n : ℝ) - 1) else 0 := rfl

/-- The source `b` vanishes off the diagonal `X = Y`. -/
theorem twoCopySource_of_ne {w : TwoCopyState (ZMod n) m} (h : w.x ≠ w.y) :
    twoCopySource n m w = 0 := if_neg h

/-- The defining formula of the centred coincidence indicator `v`. -/
theorem centredCoincidence_apply (w : TwoCopyState (ZMod n) m) :
    centredCoincidence n m w = (if w.x = w.y then 1 else 0) - 1 / (m : ℝ) := rfl

/-- The defining formula of the corrector `φ`. -/
theorem corrector_apply (r : ZMod n) :
    corrector n m r =
      (n : ℝ) * ((m : ℝ) - 1) * ((n : ℝ) + 1) / (24 * (m : ℝ) ^ 2) -
        (r.val : ℝ) * ((n : ℝ) - r.val) / (4 * m) := rfl

/-- `𝓡_{n,m}` is the squared `H⁻¹` norm of the source `b` for the two-copy process. -/
theorem resolventQuantity_def [NeZero n] :
    resolventQuantity n m = (twoCopy n m).hMinusOneNormSq (twoCopySource n m) := rfl

/-- The red-neighbour count is nonnegative. -/
theorem redNeighbourCount_nonneg (w : TwoCopyState (ZMod n) m) : 0 ≤ redNeighbourCount w := by
  unfold redNeighbourCount
  split_ifs <;> norm_num

/-- The red-neighbour count is at most `2`. -/
theorem redNeighbourCount_le_two (w : TwoCopyState (ZMod n) m) : redNeighbourCount w ≤ 2 := by
  unfold redNeighbourCount
  split_ifs <;> norm_num

/-! ### The sum and the Laplacian of the corrector -/

/-- `∑_{k < N} k (x - k) = x N(N-1)/2 - (N-1)N(2N-1)/6`. -/
theorem sum_range_mul_sub (x : ℝ) (N : ℕ) :
    ∑ k ∈ range N, (k : ℝ) * (x - k) =
      x * N * (N - 1) / 2 - (N - 1) * N * (2 * N - 1) / 6 := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, ih]; push_cast; ring

/-- `∑_{r ∈ ℤ/nℤ} r(n - r) = n(n-1)(n+1)/6`, on the representatives `r ∈ {0, …, n-1}`. -/
theorem sum_val_mul_sub_val (n : ℕ) [NeZero n] :
    ∑ r : ZMod n, (r.val : ℝ) * ((n : ℝ) - r.val) = n * (n - 1) * (n + 1) / 6 := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos n)).symm⟩
  refine (Fin.sum_univ_eq_sum_range
    (fun k => (k : ℝ) * (((N + 1 : ℕ) : ℝ) - k)) (N + 1)).trans ?_
  rw [sum_range_mul_sub]
  ring

/-- The discrete Laplacian of the corrector: `Δφ = 1/(2m) - n/(2m) · 1[· = 0]`. -/
theorem Delta_mulVec_corrector [NeZero n] (hn : 2 ≤ n) (x : ZMod n) :
    Matrix.mulVec (Delta n) (corrector n m) x =
      1 / (2 * m) - if x = 0 then (n : ℝ) / (2 * m) else 0 := by
  rw [Delta_mulVec]
  simp only [corrector_apply]
  obtain ⟨k, hk, rfl⟩ : ∃ k < n, x = (k : ZMod n) :=
    ⟨x.val, ZMod.val_lt x, (ZMod.natCast_zmod_val x).symm⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have h1 : ((0 : ℕ) : ZMod n) - 1 = ((n - 1 : ℕ) : ZMod n) := by
      rw [Nat.cast_zero, zero_sub, Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one,
        zero_sub]
    have h2 : ((0 : ℕ) : ZMod n) + 1 = ((1 : ℕ) : ZMod n) := by simp
    rw [h1, h2, ZMod.val_cast_of_lt (by omega), ZMod.val_cast_of_lt (by omega),
      ZMod.val_cast_of_lt (by omega)]
    simp only [Nat.cast_zero, if_true]
    rw [Nat.cast_sub (by omega)]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have : (m : ℝ) ≠ 0 := by positivity
      field_simp
      ring
  · have hne : (k : ZMod n) ≠ 0 := by
      intro h
      rw [← ZMod.val_eq_zero, ZMod.val_cast_of_lt hk] at h
      omega
    have h1 : (k : ZMod n) - 1 = ((k - 1 : ℕ) : ZMod n) := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [if_neg hne, h1, ZMod.val_cast_of_lt (by omega), ZMod.val_cast_of_lt hk]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    rcases Nat.lt_or_ge (k + 1) n with hk1 | hk1
    · have h2 : (k : ZMod n) + 1 = ((k + 1 : ℕ) : ZMod n) := by push_cast; rfl
      rw [h2, ZMod.val_cast_of_lt hk1, Nat.cast_sub (by omega)]
      push_cast
      field_simp
      ring
    · have hkn : k + 1 = n := by omega
      have h2 : (k : ZMod n) + 1 = 0 := by
        rw [← Nat.cast_one, ← Nat.cast_add, hkn, ZMod.natCast_self]
      have hk' : (k : ℝ) = n - 1 := by
        rw [← hkn]; push_cast; ring
      rw [h2, ZMod.val_zero, Nat.cast_sub (by omega), hk']
      push_cast
      field_simp
      ring

end CycleCutoff
