/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.FiniteProbability.SizeBias
public import CycleCutoff.FiniteProbability.SampleSumVariance

/-!
# A second-moment bound for the hypergeometric distribution

Let `V` be a finite set with `|V| = n ≥ 3`, let `B ⊆ V` with `|B| = s ≥ 2`, let `1 ≤ m ≤ n`, and
let `R` be a uniformly random `m`-subset of `V`, so that `K = |R ∩ B|` is hypergeometric. Then
`𝔼[((K - 1) / (s - 1) - (m - 1) / (n - 1))² 1[K ≥ 1]] ≤ 8 ρ (1 - ρ) / s`, where `ρ = m / n`.

Write `α = (m - 1) / (n - 1)` and `a = 1 + (s - 1) α`, so that the quantity is
`𝔼[(K - a)² 1[K ≥ 1]] / (s - 1)²`. The mean and variance of `K` are `s ρ` and
`s ρ (1 - ρ) (n - s) / (n - 1)`, and `𝔼 K - a = -(1 - ρ) (n - s) / (n - 1)`.

* If `s ρ ≥ 1`, drop the indicator: `𝔼[(K - a)²] ≤ s ρ (1 - ρ) + (1 - ρ)² ≤ 2 s ρ (1 - ρ)`.
* If `s ρ ≤ 1`, bound `1[K ≥ 1] ≤ K` and size-bias: `𝔼[K (K - a)²] = s ρ 𝔼[(1 + K' - a)²]`,
  where `K' = |R' ∩ (B ∖ {b₀})|` for a uniformly random `(m - 1)`-subset `R'` of `V ∖ {b₀}`.
  The mean of `K'` is exactly `a - 1`, so this is `s ρ Var K'`, which is computed explicitly.

## Main results

* `CycleCutoff.sampleAvg_hypergeometric_le`: the second-moment bound above.
-/

public section

open Finset

namespace CycleCutoff

section Helpers

variable {V : Type*} [Fintype V]

/-- The second moment of `|T ∩ C| - a` for a uniformly random `k`-subset `T`. -/
private lemma sampleAvg_card_inter_sub_sq [DecidableEq V] (hN : 2 ≤ Fintype.card V) {k : ℕ}
    (hk : k ≤ Fintype.card V) (C : Finset V) (a : ℝ) :
    sampleAvg k (fun T : Finset V => ((#(T ∩ C) : ℝ) - a) ^ 2) =
      (k * (Fintype.card V - k) : ℝ) / (Fintype.card V * (Fintype.card V - 1)) *
        (#C * (Fintype.card V - #C) / Fintype.card V) +
        (k * #C / Fintype.card V - a) ^ 2 := by
  set w : V → ℝ := fun y => if y ∈ C then 1 else 0
  have hw : ∀ T : Finset V, ∑ y ∈ T, w y = #(T ∩ C) := fun T => by simp [w]
  have hwu : ∑ y, w y = #C := by rw [hw, univ_inter]
  have hN0 : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hmean : sampleAvg k (fun T : Finset V => (#(T ∩ C) : ℝ)) =
      k * #C / Fintype.card V := by
    have h := sampleAvg_sum k hk w
    simp only [hw, univ_inter] at h
    rw [h]
    ring
  have hsq : ∑ y, (w y - (Fintype.card V : ℝ)⁻¹ * ∑ y', w y') ^ 2 =
      #C * (Fintype.card V - #C) / Fintype.card V := by
    rw [hwu]
    set d : ℝ := (Fintype.card V : ℝ)⁻¹ * #C
    have hpt : ∀ y, (w y - d) ^ 2 = (1 - 2 * d) * w y + d ^ 2 := fun y => by
      simp only [w]
      split_ifs <;> ring
    simp only [hpt, sum_add_distrib, ← mul_sum, hwu, sum_const, card_univ, nsmul_eq_mul, d]
    field_simp
    ring
  have hvar := sampleAvg_sq_sub hN k hk w
  rw [hsq] at hvar
  simp only [hw, hmean] at hvar
  rw [sampleAvg_sub_const_sq hk, hmean, hvar]

end Helpers

/-- For reals `3 ≤ n`, `2 ≤ s ≤ n` and `1 ≤ m ≤ n` with `n ≤ s m`, writing `ρ = m / n` and
`a = 1 + (s - 1) (m - 1) / (n - 1)`,
`s ρ (1 - ρ) (n - s) / (n - 1) + (s ρ - a)² ≤ 8 ρ (1 - ρ) (s - 1)² / s`. -/
private lemma hypergeometric_aux_large {n s m : ℝ} (hn : 3 ≤ n) (hs : 2 ≤ s) (hsn : s ≤ n)
    (hm₁ : 1 ≤ m) (hmn : m ≤ n) (hsm : n ≤ s * m) :
    m * (n - m) / (n * (n - 1)) * (s * (n - s) / n) +
        (m * s / n - (1 + (s - 1) * ((m - 1) / (n - 1)))) ^ 2 ≤
      8 * (m / n) * (1 - m / n) / s * (s - 1) ^ 2 := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  have hs0 : 0 < s := by linarith
  set ρ := m / n with hρ
  set t := (n - s) / (n - 1) with ht
  have e1 : m * (n - m) / (n * (n - 1)) * (s * (n - s) / n) = s * ρ * (1 - ρ) * t := by
    rw [hρ, ht]; field_simp
  have e2 : m * s / n - (1 + (s - 1) * ((m - 1) / (n - 1))) = -((1 - ρ) * t) := by
    rw [hρ, ht]; field_simp; ring
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 := by rw [hρ, div_le_one hn0]; exact hmn
  have hq : 0 ≤ 1 - ρ := by linarith
  have hsρ : 1 ≤ s * ρ := by rw [hρ, mul_div_assoc', le_div_iff₀ hn0]; linarith
  have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg (by linarith) hn1.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hn1]; linarith
  rw [e1, e2]
  have h1 : s * ρ * (1 - ρ) * t + (-((1 - ρ) * t)) ^ 2 ≤ 2 * (s * ρ * (1 - ρ)) := by
    nlinarith [mul_nonneg (mul_nonneg hs0.le hρ0) hq, mul_nonneg hq ht0, sq_nonneg (1 - ρ),
      mul_nonneg (mul_nonneg hq hq) ht0]
  have h2 : 2 * (s * ρ * (1 - ρ)) ≤ 8 * ρ * (1 - ρ) / s * (s - 1) ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hs0]
    have hs4 : s ^ 2 ≤ 4 * (s - 1) ^ 2 := by nlinarith
    have hp : 0 ≤ ρ * (1 - ρ) := by positivity
    nlinarith
  linarith

/-- For reals `3 ≤ n`, `2 ≤ s ≤ n` and `1 ≤ m ≤ n` with `s m ≤ n`, writing `ρ = m / n`,
`s ρ · (m - 1) (n - m) / ((n - 1) (n - 2)) · (s - 1) (n - s) / (n - 1)` is at most
`8 ρ (1 - ρ) (s - 1)² / s`. -/
private lemma hypergeometric_aux_small {n s m : ℝ} (hn : 3 ≤ n) (hs : 2 ≤ s) (hsn : s ≤ n)
    (hm₁ : 1 ≤ m) (hmn : m ≤ n) (hsm : s * m ≤ n) :
    s * m / n * ((m - 1) * (n - 1 - (m - 1)) / ((n - 1) * (n - 1 - 1)) *
        ((s - 1) * (n - 1 - (s - 1)) / (n - 1))) ≤
      8 * (m / n) * (1 - m / n) / s * (s - 1) ^ 2 := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  have hn2 : 0 < n - 2 := by linarith
  have hs0 : 0 < s := by linarith
  have hs1 : 0 < s - 1 := by linarith
  set c : ℝ := m * (n - m) * (s - 1) / (n ^ 2 * s * (n - 1) ^ 2 * (n - 2)) with hc
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
      (by positivity)
  have eL : s * m / n * ((m - 1) * (n - 1 - (m - 1)) / ((n - 1) * (n - 1 - 1)) *
        ((s - 1) * (n - 1 - (s - 1)) / (n - 1))) = c * (s ^ 2 * (m - 1) * (n - s) * n) := by
    rw [hc, show n - 1 - 1 = n - 2 by ring]
    field_simp
    ring
  have eR : 8 * (m / n) * (1 - m / n) / s * (s - 1) ^ 2 =
      c * (8 * (s - 1) * (n - 1) ^ 2 * (n - 2)) := by
    rw [hc]
    field_simp
  rw [eL, eR]
  apply mul_le_mul_of_nonneg_left _ hc0
  have k1 : s * (m - 1) ≤ n := by nlinarith
  have hns : (0 : ℝ) ≤ n - s := by linarith
  have k2 : s ^ 2 * (m - 1) * (n - s) * n ≤ s * n * (n - s) * n := by
    nlinarith [mul_nonneg (mul_nonneg hs0.le hns) hn0.le]
  have k3 : s * n * (n - s) * n ≤ s * n ^ 2 * (n - 2) := by
    nlinarith [mul_nonneg hs0.le (sq_nonneg n)]
  have k4 : s * n ^ 2 ≤ 8 * (s - 1) * (n - 1) ^ 2 := by
    nlinarith [sq_nonneg n, sq_nonneg (n - 2)]
  linarith [mul_le_mul_of_nonneg_right k4 hn2.le]

/-- If `|B| m ≤ |V|`, then for a uniformly random `m`-subset `R` of `V`, with
`a = 1 + (|B| - 1) (m - 1) / (|V| - 1)` and `ρ = m / |V|`,
`𝔼[(|R ∩ B| - a)² 1[|R ∩ B| ≥ 1]] ≤ 8 ρ (1 - ρ) (|B| - 1)² / |B|`. -/
private lemma sampleAvg_card_inter_sub_sq_ite_le_of_mul_le {V : Type*} [Fintype V] [DecidableEq V]
    (hn : 3 ≤ Fintype.card V) (m : ℕ) (hm₁ : 1 ≤ m) (hm : m ≤ Fintype.card V) (B : Finset V)
    (hs : 2 ≤ #B) (hsm : #B * m ≤ Fintype.card V) :
    sampleAvg m (fun R : Finset V => if 1 ≤ #(R ∩ B) then
        ((#(R ∩ B) : ℝ) - (1 + ((#B : ℝ) - 1) * (((m : ℝ) - 1) / (Fintype.card V - 1)))) ^ 2
          else 0) ≤
      8 * ((m : ℝ) / Fintype.card V) * (1 - (m : ℝ) / Fintype.card V) / #B *
        ((#B : ℝ) - 1) ^ 2 := by
  set a : ℝ := 1 + ((#B : ℝ) - 1) * (((m : ℝ) - 1) / (Fintype.card V - 1)) with ha
  obtain ⟨b₀, hb₀⟩ : B.Nonempty := card_pos.1 (by omega)
  have hcard : Fintype.card {v : V // v ≠ b₀} = Fintype.card V - 1 := by
    simp [Fintype.card_subtype, filter_ne', card_erase_of_mem]
  have hcardB : #(B.subtype (· ≠ b₀)) = #B - 1 := by
    rw [card_subtype, filter_ne', card_erase_of_mem hb₀]
  have hle : sampleAvg m (fun R : Finset V =>
        if 1 ≤ #(R ∩ B) then ((#(R ∩ B) : ℝ) - a) ^ 2 else 0) ≤
      sampleAvg m (fun R : Finset V => (#(R ∩ B) : ℝ) *
        (fun k : ℤ => ((k : ℝ) - a) ^ 2) #(R ∩ B)) := by
    refine sampleAvg_mono fun R _ => ?_
    simp only [Int.cast_natCast]
    split_ifs with h
    · nlinarith [sq_nonneg ((#(R ∩ B) : ℝ) - a), (by exact_mod_cast h : (1 : ℝ) ≤ #(R ∩ B))]
    · positivity
  rw [sampleAvg_card_inter_mul B m hm₁ hm b₀ hb₀ (fun k : ℤ => ((k : ℝ) - a) ^ 2)] at hle
  have hfun : (fun R' : Finset {v : V // v ≠ b₀} =>
        (fun k : ℤ => ((k : ℝ) - a) ^ 2) (1 + #(R' ∩ B.subtype (· ≠ b₀)))) =
      fun R' => ((#(R' ∩ B.subtype (· ≠ b₀)) : ℝ) - (a - 1)) ^ 2 := by
    funext R'
    push_cast
    ring
  rw [hfun, sampleAvg_card_inter_sub_sq (by omega) (by omega), hcard, hcardB] at hle
  rw [Nat.cast_sub hm₁, Nat.cast_sub (by omega : 1 ≤ Fintype.card V),
    Nat.cast_sub (by omega : 1 ≤ #B), Nat.cast_one] at hle
  have hzero : (m - 1) * (#B - 1) / (Fintype.card V - 1) - (a - 1) = (0 : ℝ) := by
    rw [ha]; ring
  rw [hzero] at hle
  refine hle.trans (le_of_eq_of_le ?_ (hypergeometric_aux_small (by exact_mod_cast hn)
    (by exact_mod_cast hs) (by exact_mod_cast card_le_univ B) (by exact_mod_cast hm₁)
    (by exact_mod_cast hm) (by exact_mod_cast hsm)))
  ring

/-- **Second-moment bound for the hypergeometric distribution.** For a uniformly random
`m`-subset `R` of `V`, with `n = |V| ≥ 3`, `1 ≤ m ≤ n`, `B ⊆ V`, `s = |B| ≥ 2` and
`K = |R ∩ B|`,
`𝔼[((K - 1) / (s - 1) - (m - 1) / (n - 1))² 1[K ≥ 1]] ≤ 8 (m / n) (1 - m / n) / s`. -/
@[cycle_cutoff "lem_hypergeometric"]
theorem sampleAvg_hypergeometric_le {V : Type*} [Fintype V] [DecidableEq V]
    (hn : 3 ≤ Fintype.card V) (m : ℕ) (hm₁ : 1 ≤ m) (hm : m ≤ Fintype.card V) (B : Finset V)
    (hs : 2 ≤ #B) :
    sampleAvg m (fun R : Finset V => if 1 ≤ #(R ∩ B) then
        (((#(R ∩ B) : ℝ) - 1) / (#B - 1) - ((m : ℝ) - 1) / (Fintype.card V - 1)) ^ 2 else 0) ≤
      8 * ((m : ℝ) / Fintype.card V) * (1 - (m : ℝ) / Fintype.card V) / #B := by
  have hsr : (2 : ℝ) ≤ #B := by exact_mod_cast hs
  set a : ℝ := 1 + ((#B : ℝ) - 1) * (((m : ℝ) - 1) / (Fintype.card V - 1)) with ha
  have hs1 : (#B : ℝ) - 1 ≠ 0 := by linarith
  have hpt : (fun R : Finset V => if 1 ≤ #(R ∩ B) then
        (((#(R ∩ B) : ℝ) - 1) / (#B - 1) - ((m : ℝ) - 1) / (Fintype.card V - 1)) ^ 2 else 0) =
      fun R => (if 1 ≤ #(R ∩ B) then ((#(R ∩ B) : ℝ) - a) ^ 2 else 0) / ((#B : ℝ) - 1) ^ 2 := by
    funext R
    split_ifs
    · rw [ha]; field_simp; ring
    · simp
  rw [hpt, sampleAvg_div_const, div_le_iff₀ (by positivity)]
  rcases le_or_gt (#B * m) (Fintype.card V) with hsm | hsm
  · rw [ha]
    exact sampleAvg_card_inter_sub_sq_ite_le_of_mul_le hn m hm₁ hm B hs hsm
  · have hle : sampleAvg m (fun R : Finset V =>
          if 1 ≤ #(R ∩ B) then ((#(R ∩ B) : ℝ) - a) ^ 2 else 0) ≤
        sampleAvg m (fun R : Finset V => ((#(R ∩ B) : ℝ) - a) ^ 2) := by
      refine sampleAvg_mono fun R _ => ?_
      split_ifs
      exacts [le_rfl, by positivity]
    rw [sampleAvg_card_inter_sub_sq (by omega) hm] at hle
    exact hle.trans (hypergeometric_aux_large (by exact_mod_cast hn) hsr
      (by exact_mod_cast card_le_univ B) (by exact_mod_cast hm₁) (by exact_mod_cast hm)
      (by exact_mod_cast hsm.le))

end CycleCutoff
