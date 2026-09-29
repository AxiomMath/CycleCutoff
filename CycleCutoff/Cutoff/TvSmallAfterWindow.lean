/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Cycle.Defs
public import CycleCutoff.Cutoff.EntropyAtWindow
public import CycleCutoff.Cycle.CycleEntropyDecay
public import CycleCutoff.Cycle.MuPositive
public import CycleCutoff.Cycle.LambdaLower
public import CycleCutoff.Generator.RelEntMonotone
public import CycleCutoff.FiniteProbability.Pinsker
public import CycleCutoff.Cycle.DnSymmetry
public import CycleCutoff.Generator.SemigroupLower
public import CycleCutoff.Generator.SemigroupRowsum

/-!
# Small total variation after the cutoff window

There is an absolute constant `C > 0` such that for every `ε ∈ (0, 1)` there are `K_ε > 0`
and `N₀` with `d_n(t_n + C n² log log n + K_ε n²) ≤ ε` for all `n ≥ N₀`.

## Main results

* `CycleCutoff.exists_dn_le_after_window`: the upper bound on `d_n` after the window.

## References

* C. Defant, *Cutoff for the Adjacent Transposition Shuffle on a Cycle*, Section 7.1.
-/

public section

open Finset Real Matrix

namespace CycleCutoff

variable {n : ℕ} [NeZero n]

/-- **Small total variation after the window**: there is an absolute constant `C > 0` such that
for every `ε ∈ (0, 1)` there are `K_ε > 0` and `N₀` with
`d_n(t_n + C n² log log n + K_ε n²) ≤ ε` for all `n ≥ N₀`. -/
@[cycle_cutoff "lem_tv_small_after_window"]
theorem exists_dn_le_after_window :
    ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ Kε > (0 : ℝ), ∃ N₀ : ℕ,
      ∀ (n : ℕ) [NeZero n], N₀ ≤ n →
        dn n (tn n + C * (n : ℝ) ^ 2 * Real.log (Real.log n) + Kε * (n : ℝ) ^ 2) ≤ ε := by
  obtain ⟨K, hK, N₁, hwin⟩ := exists_relEnt_muT_window_le
  obtain ⟨c₅, hc₅, hdec⟩ := exists_relEnt_cycleShuffle_semigroup_le
  refine ⟨3 / (8 * c₅), by positivity, fun ε hε _ => ?_⟩
  set M := max 0 (Real.log (K / (2 * ε ^ 2))) with hM
  have hM0 : 0 ≤ M := le_max_left _ _
  refine ⟨(1 + M / c₅) / 16, by positivity, max N₁ (⌈Real.exp 2⌉₊ + 3), fun n _ hN => ?_⟩
  have hN₁ : N₁ ≤ n := le_of_max_le_left hN
  have hn3 : ⌈Real.exp 2⌉₊ + 3 ≤ n := le_of_max_le_right hN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set L := Real.log n with hL
  have hL2 : 2 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hn0]
    calc Real.exp 2 ≤ ⌈Real.exp 2⌉₊ := Nat.le_ceil _
      _ ≤ n := by exact_mod_cast (by omega : ⌈Real.exp 2⌉₊ ≤ n)
  set lam := lambdaN n with hlam_def
  have hlam16 : 16 / (n : ℝ) ^ 2 ≤ lam := sixteen_div_sq_le_lambdaN (by omega)
  have hlam : 0 < lam := lt_of_lt_of_le (by positivity) hlam16
  have hinv : 1 / lam ≤ (n : ℝ) ^ 2 / 16 := by
    rw [div_le_div_iff₀ hlam (by norm_num)]
    rw [div_le_iff₀ (by positivity)] at hlam16
    linarith
  have htn : 0 < tn n := div_pos (by linarith) (by positivity)
  set T := tn n + 1 / lam with hT
  have hT0 : 0 < T := by have := one_div_pos.2 hlam; linarith
  have hlog1 : 0 ≤ Real.log (1 + L) := Real.log_nonneg (by linarith)
  have hloglog : Real.log (1 + L) ≤ 2 * Real.log L := by
    rw [← Real.log_rpow (by linarith), Real.rpow_two]
    exact Real.log_le_log (by linarith) (by nlinarith)
  set u := 3 / c₅ * Real.log (1 + L) + M / c₅ with hu
  have hu0 : 0 ≤ u := by positivity
  set s := u / lam with hs
  have hs0 : 0 ≤ s := div_nonneg hu0 hlam.le
  have hα := isProbVec_muT (n := n) hT0.le
  have hαpos : ∀ σ, 0 < muT n T σ := muT_pos hT0
  have hdecay := hdec n (by omega) (muT n T) hα hαpos s hs0
  rw [← muT_add] at hdecay
  have hwin' := hwin n hN₁
  have hexp : Real.exp (-c₅ * lam * s) * (K * (1 + L) ^ 3) ≤ 2 * ε ^ 2 := by
    have e1 : -c₅ * lam * s = -(Real.log ((1 + L) ^ 3)) + -M := by
      rw [hs, hu, Real.log_pow]
      field_simp
      push_cast
      ring
    have hpos : 0 < (1 + L) ^ 3 := by positivity
    rw [e1, Real.exp_add, Real.exp_neg, Real.exp_log hpos]
    have hexpM : Real.exp (-M) ≤ 2 * ε ^ 2 / K := by
      have h1 : Real.log (K / (2 * ε ^ 2)) ≤ M := le_max_right _ _
      calc Real.exp (-M) ≤ Real.exp (-Real.log (K / (2 * ε ^ 2))) :=
            Real.exp_le_exp.2 (by linarith)
        _ = 2 * ε ^ 2 / K := by
            rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
    calc ((1 + L) ^ 3)⁻¹ * Real.exp (-M) * (K * (1 + L) ^ 3) = K * Real.exp (-M) := by
          field_simp
      _ ≤ K * (2 * ε ^ 2 / K) := by gcongr
      _ = 2 * ε ^ 2 := by field_simp
  have hH : relEnt (muT n (T + s)) (unif (Equiv.Perm (ZMod n))) ≤ 2 * ε ^ 2 :=
    hdecay.trans ((mul_le_mul_of_nonneg_left hwin' (Real.exp_pos _).le).trans hexp)
  set T' := tn n + 3 / (8 * c₅) * (n : ℝ) ^ 2 * Real.log L + (1 + M / c₅) / 16 * (n : ℝ) ^ 2
    with hT'
  have hTT' : T + s ≤ T' := by
    have h1 : 1 / lam + s = (1 + u) * (1 / lam) := by rw [hs]; field_simp
    have h2 : (1 + u) * (1 / lam) ≤ (1 + u) * ((n : ℝ) ^ 2 / 16) :=
      mul_le_mul_of_nonneg_left hinv (by linarith)
    have h3 : (1 + u) * ((n : ℝ) ^ 2 / 16) =
        (1 + M / c₅) / 16 * (n : ℝ) ^ 2 + 3 / (16 * c₅) * (n : ℝ) ^ 2 * Real.log (1 + L) := by
      rw [hu]; field_simp; ring
    have h4 : 3 / (16 * c₅) * (n : ℝ) ^ 2 * Real.log (1 + L) ≤
        3 / (8 * c₅) * (n : ℝ) ^ 2 * Real.log L := by
      have : 3 / (16 * c₅) * (n : ℝ) ^ 2 * (2 * Real.log L) =
          3 / (8 * c₅) * (n : ℝ) ^ 2 * Real.log L := by field_simp; ring
      rw [← this]
      gcongr
    rw [hT, hT']
    linarith
  have hmono : relEnt (muT n T') (unif (Equiv.Perm (ZMod n))) ≤
      relEnt (muT n (T + s)) (unif (Equiv.Perm (ZMod n))) := by
    have := (cycleShuffle n).antitoneOn_relEnt_semigroup _ (isProbVec_single 1)
      (Set.mem_Ici.2 (by linarith : (0 : ℝ) ≤ T + s))
      (Set.mem_Ici.2 (by linarith : (0 : ℝ) ≤ T')) hTT'
    simpa only [← muT_eq_single_vecMul] using this
  have hpin := tvDist_sq_le_relEnt (muT n T') (unif (Equiv.Perm (ZMod n)))
    (isProbVec_muT (by linarith)) isProbVec_unif (fun _ => by rw [unif_apply]; positivity)
  rw [dn_eq_tvDist_muT]
  nlinarith

end CycleCutoff
