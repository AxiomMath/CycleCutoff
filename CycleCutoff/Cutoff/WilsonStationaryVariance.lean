/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Cutoff.Defs
public import CycleCutoff.Cutoff.WilsonStationaryMean
public import Mathlib.GroupTheory.Perm.Basic

/-!
# The stationary variance of Wilson's statistic

For `n ≥ 3`, the variance of Wilson's statistic `F(σ) = ∑_i cos(2π (σ(i) - i) / n)` under the
uniform measure `π_n` on `Perm (ℤ/nℤ)` is at most `n`; in fact `Var_{π_n}(F) = n² / (2(n - 1))`.

## Main results

* `CycleCutoff.sub_one_mul_sum_perm_sq_sum`: for a real matrix `a` on a finite type `α` of size
  `N` with vanishing row and column sums,
  `(N - 1) ∑_σ (∑_i a(i, σ i))² = N ∑_σ ∑_i a(i, σ i)²`.
* `CycleCutoff.sum_cos_two_pi_val_sq`: `∑_{z ∈ ℤ/nℤ} cos²(2π z / n) = n / 2` for `n ≥ 3`.
* `CycleCutoff.variance_unif_wilsonStat_le`: `Var_{π_n}(F) ≤ n` for `n ≥ 3`.
-/

public section

open Finset Real

namespace CycleCutoff

/-- For a real matrix `a` on a finite type `α` with vanishing row and column sums,
`(|α| - 1) ∑_σ (∑_i a(i, σ i))² = |α| ∑_σ ∑_i a(i, σ i)²`, the sums running over all
permutations `σ` of `α`. -/
theorem sub_one_mul_sum_perm_sq_sum {α : Type*} [Fintype α] [DecidableEq α] (a : α → α → ℝ)
    (hrow : ∀ i, ∑ x, a i x = 0) (hcol : ∀ x, ∑ i, a i x = 0) :
    ((Fintype.card α : ℝ) - 1) * ∑ σ : Equiv.Perm α, (∑ i, a i (σ i)) ^ 2 =
      Fintype.card α * ∑ σ : Equiv.Perm α, ∑ i, a i (σ i) ^ 2 := by
  obtain ⟨H, hH⟩ : ∃ H : α → α → ℝ, H = fun i j => ∑ σ : Equiv.Perm α, a i (σ i) * a j (σ j) :=
    ⟨_, rfl⟩
  have hswap {i j k : α} (hij : i ≠ j) (hik : i ≠ k) :
      H i j = ∑ σ : Equiv.Perm α, a i (σ i) * a j (σ k) := by
    rw [hH, ← Equiv.sum_comp (Equiv.mulRight (Equiv.swap j k))]
    refine sum_congr rfl fun σ _ => ?_
    simp [Equiv.swap_apply_of_ne_of_ne hij hik]
  have hoff {i j : α} (hij : i ≠ j) :
      ((Fintype.card α : ℝ) - 1) * H i j = -∑ σ : Equiv.Perm α, a i (σ i) * a j (σ i) := by
    have hc : ((Fintype.card α : ℝ) - 1) = ((univ.erase i).card : ℝ) := by
      rw [card_erase_of_mem (mem_univ _), card_univ,
        Nat.cast_sub (Fintype.card_pos_iff.2 ⟨i⟩), Nat.cast_one]
    calc ((Fintype.card α : ℝ) - 1) * H i j
        = ∑ k ∈ univ.erase i, ∑ σ : Equiv.Perm α, a i (σ i) * a j (σ k) := by
          rw [hc, ← nsmul_eq_mul, ← sum_const]
          exact sum_congr rfl fun k hk => hswap hij (ne_of_mem_erase hk).symm
      _ = ∑ σ : Equiv.Perm α, a i (σ i) * ∑ k ∈ univ.erase i, a j (σ k) := by
          rw [sum_comm]
          simp_rw [mul_sum]
      _ = -∑ σ : Equiv.Perm α, a i (σ i) * a j (σ i) := by
          rw [← sum_neg_distrib]
          refine sum_congr rfl fun σ _ => ?_
          have h0 : ∑ k, a j (σ k) = 0 := (Equiv.sum_comp σ (a j)).trans (hrow j)
          rw [← add_sum_erase _ _ (mem_univ i)] at h0
          rw [eq_neg_of_add_eq_zero_right h0]
          ring
  have hrowH (i : α) :
      ((Fintype.card α : ℝ) - 1) * ∑ j, H i j = Fintype.card α * H i i := by
    rw [← add_sum_erase _ _ (mem_univ i), mul_add, mul_sum (univ.erase i),
      sum_congr rfl fun j hj => hoff (ne_of_mem_erase hj).symm, sum_neg_distrib, sum_comm]
    have : ∑ σ : Equiv.Perm α, ∑ j ∈ univ.erase i, a i (σ i) * a j (σ i) = -H i i := by
      rw [hH, ← sum_neg_distrib]
      refine sum_congr rfl fun σ _ => ?_
      rw [← mul_sum]
      have h0 := hcol (σ i)
      rw [← add_sum_erase _ _ (mem_univ i)] at h0
      rw [eq_neg_of_add_eq_zero_right h0]
      ring
    rw [this]
    ring
  calc ((Fintype.card α : ℝ) - 1) * ∑ σ : Equiv.Perm α, (∑ i, a i (σ i)) ^ 2
      = ∑ i, ((Fintype.card α : ℝ) - 1) * ∑ j, H i j := by
        rw [← mul_sum]
        congr 1
        simp_rw [hH, sq, sum_mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun i _ => sum_comm
    _ = Fintype.card α * ∑ σ : Equiv.Perm α, ∑ i, a i (σ i) ^ 2 := by
        simp_rw [hrowH, ← mul_sum, hH, sq]
        rw [sum_comm]

variable {n : ℕ} [NeZero n]

/-- `∑_{z ∈ ℤ/nℤ} cos²(2π z / n) = n / 2` for `n ≥ 3`. -/
theorem sum_cos_two_pi_val_sq (hn : 3 ≤ n) :
    ∑ z : ZMod n, Real.cos (2 * π * (z.val : ℝ) / n) ^ 2 = n / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h2 : ¬ (m + 1) ∣ 2 := fun h => absurd (Nat.le_of_dvd two_pos h) (by omega)
  have key := sum_range_cos_two_pi_mul_div (n := m + 1) (by omega) 2
  rw [if_neg (by exact_mod_cast h2)] at key
  have e : ∑ z : ZMod (m + 1), Real.cos (2 * π * (z.val : ℝ) / (m + 1 : ℕ)) ^ 2 =
      ∑ k ∈ range (m + 1), Real.cos (2 * π * (k : ℝ) / (m + 1 : ℕ)) ^ 2 :=
    Fin.sum_univ_eq_sum_range (fun k : ℕ => Real.cos (2 * π * (k : ℝ) / (m + 1 : ℕ)) ^ 2) _
  rw [e]
  simp_rw [cos_sq]
  have : ∑ k ∈ range (m + 1), Real.cos (2 * (2 * π * (k : ℝ) / (m + 1 : ℕ))) = 0 := by
    rw [← key]
    refine sum_congr rfl fun k _ => ?_
    push_cast
    ring_nf
  rw [sum_add_distrib, ← sum_div, ← sum_div, this]
  simp

/-- Averaging over rotations: for `g : ℤ/nℤ → ℝ` and `i ∈ ℤ/nℤ`,
`n ∑_σ g(σ i) = |Perm (ℤ/nℤ)| ∑_z g(z)`. -/
theorem natCast_mul_sum_perm_apply (g : ZMod n → ℝ) (i : ZMod n) :
    (n : ℝ) * ∑ σ : Equiv.Perm (ZMod n), g (σ i) =
      Fintype.card (Equiv.Perm (ZMod n)) * ∑ z, g z := by
  have hshift (k : ZMod n) :
      ∑ σ : Equiv.Perm (ZMod n), g (σ i) = ∑ σ : Equiv.Perm (ZMod n), g (σ i + k) := by
    rw [← Equiv.sum_comp (Equiv.mulLeft (Equiv.addRight k)) fun σ => g (σ i)]
    simp
  calc (n : ℝ) * ∑ σ : Equiv.Perm (ZMod n), g (σ i)
      = ∑ k : ZMod n, ∑ σ : Equiv.Perm (ZMod n), g (σ i + k) := by
        rw [← sum_congr rfl fun k _ => hshift k]
        simp [ZMod.card]
    _ = Fintype.card (Equiv.Perm (ZMod n)) * ∑ z, g z := by
        rw [sum_comm, ← nsmul_eq_mul, ← card_univ, ← sum_const]
        exact sum_congr rfl fun σ _ => Equiv.sum_comp (Equiv.addLeft (σ i)) g

/-- Wilson's statistic has stationary variance at most `n`: `Var_{π_n}(F) ≤ n` for `n ≥ 3`. -/
@[cycle_cutoff "lem_F_stationary_variance"]
theorem variance_unif_wilsonStat_le (hn : 3 ≤ n) :
    variance (unif (Equiv.Perm (ZMod n))) (wilsonStat n) ≤ n := by
  set c : ZMod n → ℝ := fun z => Real.cos (2 * π * (z.val : ℝ) / n) with hc
  set P : ℝ := (Fintype.card (Equiv.Perm (ZMod n)) : ℝ)
  have hP : 0 < P := Nat.cast_pos.2 Fintype.card_pos
  have hrow (i : ZMod n) : ∑ x, c (x - i) = 0 := by
    simp_rw [hc, sub_eq_add_neg]
    exact sum_cos_two_pi_val_add (by omega) _
  have hcol (x : ZMod n) : ∑ i, c (x - i) = 0 :=
    (Equiv.sum_comp (Equiv.subLeft x) c).trans (sum_cos_two_pi_val (by omega))
  have hmain := sub_one_mul_sum_perm_sq_sum (fun i x => c (x - i)) hrow hcol
  rw [ZMod.card] at hmain
  have hdiag (i : ZMod n) : ∑ σ : Equiv.Perm (ZMod n), c (σ i - i) ^ 2 = P / 2 := by
    have h := natCast_mul_sum_perm_apply (fun z => c (z - i) ^ 2) i
    have e : ∑ z, c (z - i) ^ 2 = n / 2 :=
      (Equiv.sum_comp (Equiv.subRight i) fun z => c z ^ 2).trans (sum_cos_two_pi_val_sq hn)
    rw [e] at h
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
    field_simp at h ⊢
    linarith
  rw [sum_comm] at hmain
  simp_rw [hdiag, sum_const, card_univ, ZMod.card, nsmul_eq_mul] at hmain
  set T := ∑ σ : Equiv.Perm (ZMod n), (∑ i, c (σ i - i)) ^ 2
  have hF : ∀ σ, wilsonStat n σ = ∑ i, c (σ i - i) := fun σ => rfl
  rw [variance, expectation_unif_wilsonStat (by omega), expectation_unif]
  simp_rw [sub_zero, hF]
  change P⁻¹ * T ≤ n
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [inv_mul_le_iff₀ hP]
  have h1 : (0 : ℝ) < n - 1 := by linarith
  refine le_of_mul_le_mul_left ?_ h1
  rw [hmain]
  nlinarith [mul_pos hP (by linarith : (0 : ℝ) < n)]

end CycleCutoff
