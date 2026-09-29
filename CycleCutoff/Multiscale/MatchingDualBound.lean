/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Multiscale.Defs
public import CycleCutoff.Multiscale.LevelDepth
public import CycleCutoff.Multiscale.LevelTelescope
public import CycleCutoff.Multiscale.LeafDualBound
public import CycleCutoff.Multiscale.LevelDualBound

/-!
# The dual bound for one matching

There is an absolute constant `K > 0` such that for all `n ≥ 3`, `2 ≤ m ≤ n - 1`, every matching
`M` of cycle edges, every `z` with `e_z ∉ M` and every `f`,
`⟨f, g_{M,ℤ/nℤ}⟩²_{ϖ_{n,m}} ≤ K (n - m)/(nm) (1 + log n)² 𝒟_{n,m}(f)`.

## Main results

* `CycleCutoff.exists_innerP_blockSource_univ_sq_le`: the dual bound for one matching
  `⟨f, g_{M,ℤ/nℤ}⟩²_{ϖ_{n,m}} ≤ K (n - m)/(nm) (1 + log n)² 𝒟_{n,m}(f)`.
-/

public section

open Finset

namespace CycleCutoff

/-- **The dual bound for one matching.** There is an absolute constant `K > 0` such that for
all `n ≥ 3`, `2 ≤ m < n`, every matching `M` with `e_z ∉ M` and every `f`,
`⟨f, g_{M,ℤ/nℤ}⟩²_{ϖ_{n,m}} ≤ K (n - m)/(nm) (1 + log n)² 𝒟_{n,m}(f)`. -/
@[cycle_cutoff "lem_matching_dual_bound"]
theorem exists_innerP_blockSource_univ_sq_le :
    ∃ K > 0, ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ m : ℕ, 2 ≤ m → m < n →
      ∀ (z : ZMod n) (M : Finset (ZMod n)), IsCycleMatching n M → z ∉ M →
        ∀ f : TwoCopyState (ZMod n) m → ℝ,
          innerP (unif (TwoCopyState (ZMod n) m)) f (blockSource n m M univ) ^ 2 ≤
            K * (((n : ℝ) - m) / (n * m)) * (1 + Real.log n) ^ 2 *
              (twoCopy n m).dirichletForm f := by
  obtain ⟨Kl, hKl, hleaf⟩ := exists_innerP_sum_leaf_sq_le
  obtain ⟨Kv, hKv, hlevel⟩ := exists_innerP_sum_levelIncrement_sq_le
  refine ⟨(√Kl + 4 * √Kv) ^ 2, by positivity, fun n _ hn m hm hmn z M hM hz f => ?_⟩
  set ν := unif (TwoCopyState (ZMod n) m)
  set L := ⌈4 * Real.log n⌉₊
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hL : 4 * Real.log n ≤ L := Nat.le_ceil _
  have hL' : (L : ℝ) ≤ 4 * (1 + Real.log n) :=
    (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 4 * Real.log n)).le.trans (by linarith)
  set A : TwoCopyState (ZMod n) m → ℝ := fun w => ∑ B ∈ levelPartition n z M L,
    (blockSource n m M (cutInterval n z B.1 B.2) w - blockMean n m M (cutInterval n z B.1 B.2) w)
  set U : ℕ → TwoCopyState (ZMod n) m → ℝ := fun ℓ w =>
    ∑ B ∈ levelPartition n z M ℓ \ cutAtoms n z M, levelIncrement n m z M B.1 B.2 w
  have hsplit : innerP ν f (blockSource n m M univ) =
      innerP ν f A + ∑ ℓ ∈ range L, innerP ν f (U ℓ) := by
    rw [blockSource_univ_eq_sum (m := m) hM hz L]
    simp only [A, U, innerP, expectation, mul_add, mul_sum, sum_add_distrib]
    exact congrArg _ sum_comm
  set c := ((n : ℝ) - m) / (n * m) * (twoCopy n m).dirichletForm f
  have hD : 0 ≤ (twoCopy n m).dirichletForm f := (twoCopy n m).dirichletForm_nonneg f
  have hc : 0 ≤ c :=
    mul_nonneg (div_nonneg (sub_nonneg.2 (by exact_mod_cast hmn.le)) (by positivity)) hD
  have hA : |innerP ν f A| ≤ √Kl * √c := by
    rw [← Real.sqrt_mul hKl.le]
    refine Real.abs_le_sqrt ?_
    simpa only [c, mul_assoc] using hleaf n hn m hm hmn z M hz L
      (fun B hB => mem_cutAtoms_of_mem_levelPartition hM hz hL hB) f
  have hU : ∀ ℓ, |innerP ν f (U ℓ)| ≤ √Kv * √c := fun ℓ => by
    rw [← Real.sqrt_mul hKv.le]
    refine Real.abs_le_sqrt ?_
    simpa only [c, mul_assoc] using hlevel n hn m hm hmn z M hM hz ℓ f
  have habs : |innerP ν f (blockSource n m M univ)| ≤ (√Kl + L * √Kv) * √c := by
    rw [hsplit]
    calc |innerP ν f A + ∑ ℓ ∈ range L, innerP ν f (U ℓ)|
        ≤ |innerP ν f A| + ∑ ℓ ∈ range L, |innerP ν f (U ℓ)| :=
          (abs_add_le _ _).trans (by gcongr; exact abs_sum_le_sum_abs _ _)
      _ ≤ √Kl * √c + ∑ ℓ ∈ range L, √Kv * √c :=
          add_le_add hA (sum_le_sum fun ℓ _ => hU ℓ)
      _ = (√Kl + L * √Kv) * √c := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  have hle : √Kl + L * √Kv ≤ (√Kl + 4 * √Kv) * (1 + Real.log n) := by
    have h1 : √Kl ≤ √Kl * (1 + Real.log n) :=
      le_mul_of_one_le_right (Real.sqrt_nonneg _) (by linarith)
    have h2 : (L : ℝ) * √Kv ≤ 4 * (1 + Real.log n) * √Kv :=
      mul_le_mul_of_nonneg_right hL' (Real.sqrt_nonneg _)
    linarith
  calc innerP ν f (blockSource n m M univ) ^ 2 ≤ ((√Kl + L * √Kv) * √c) ^ 2 :=
        sq_le_sq' (neg_le_of_abs_le habs) (le_of_abs_le habs)
    _ = (√Kl + L * √Kv) ^ 2 * c := by rw [mul_pow, Real.sq_sqrt hc]
    _ ≤ ((√Kl + 4 * √Kv) * (1 + Real.log n)) ^ 2 * c :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hle 2) hc
    _ = _ := by simp only [c]; ring

end CycleCutoff
