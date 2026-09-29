/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Cycle.Defs
public import CycleCutoff.TwoCopy.Defs
public import CycleCutoff.Generator.RelEntMonotone
public import CycleCutoff.Exposure.EntropyError
public import CycleCutoff.TwoCopy.ErrorDomination
public import CycleCutoff.OneCard.HeatEntropy
public import CycleCutoff.Cutoff.TotalError
public import CycleCutoff.Cycle.LambdaUpper
public import CycleCutoff.Cycle.LambdaLower
public import CycleCutoff.Generator.SemigroupLower
public import CycleCutoff.Generator.SemigroupRowsum
public import CycleCutoff.Integrated.PaperErrorIntegrable

/-!
# The entropy at the end of the cutoff window

There are an absolute constant `K > 0` and `N₀` such that for every `n ≥ N₀`,
`H(μ_{t_n + 1/λ_n} | π_n) ≤ K (1 + log n)³`.

## Main results

* `CycleCutoff.exists_relEnt_muT_window_le`: the entropy bound at the end of the window.

## References

* C. Defant, *Cutoff for the Adjacent Transposition Shuffle on a Cycle*, Section 7.1.
-/

public section

open Finset Real MeasureTheory

namespace CycleCutoff

variable {n : ℕ} [NeZero n]

/-- The prediction error `𝔈_{n,m}(t)` is nonnegative for `t ≥ 0`. -/
private lemma predictionError_nonneg {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    0 ≤ predictionError n m t :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => mul_nonneg (exposureWeight_nonneg _ _ _)
    (sum_nonneg fun σ _ => mul_nonneg (muT_nonneg ht σ)
      (sum_nonneg fun _ _ => sq_nonneg _))

/-- **Entropy at the end of the window**: there are an absolute constant `K > 0` and `N₀` such
that for every `n ≥ N₀`, `H(μ_{t_n + 1/λ_n} | π_n) ≤ K (1 + log n)³`. -/
@[cycle_cutoff "lem_entropy_at_window"]
theorem exists_relEnt_muT_window_le :
    ∃ K > (0 : ℝ), ∃ N₀ : ℕ, ∀ (n : ℕ) [NeZero n], N₀ ≤ n →
      relEnt (muT n (tn n + 1 / lambdaN n)) (unif (Equiv.Perm (ZMod n))) ≤
        K * (1 + Real.log n) ^ 3 := by
  obtain ⟨c₈, hc₈, hheat⟩ := exists_oneCardEntropy_le
  obtain ⟨K₁, hK₁, htot⟩ := exists_sum_mul_integral_paperError_le
  refine ⟨c₈ + 3 + 8 * π ^ 2 * K₁, by positivity, ⌈Real.exp 10⌉₊ + 3, fun n _ hN => ?_⟩
  have hn : 3 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 10 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn0]
    calc Real.exp 10 ≤ ⌈Real.exp 10⌉₊ := Nat.le_ceil _
      _ ≤ n := by exact_mod_cast (by omega : ⌈Real.exp 10⌉₊ ≤ n)
  have hlam : 0 < lambdaN n :=
    lt_of_lt_of_le (by positivity) (sixteen_div_sq_le_lambdaN (by omega))
  set L := 1 + Real.log n with hL
  have hL1 : 1 ≤ L := by linarith
  have htn : a0 / lambdaN n ≤ tn n := by
    rw [tn, a0, div_le_div_iff₀ hlam (by positivity)]
    nlinarith
  have htn0 : 0 < tn n := lt_of_lt_of_le (div_pos (by norm_num [a0]) hlam) htn
  set a := tn n with ha
  set b := tn n + 1 / lambdaN n with hb
  set H := relEnt (muT n b) (unif (Equiv.Perm (ZMod n))) with hH
  set F : ℝ → ℝ := fun t => c₈ + 3 * L + 2 * ∑ m ∈ Icc 1 n, (m : ℝ) * paperError n m t
    with hF
  have hexp : ∀ t, a ≤ t → (n : ℝ) * oneCardEntropy n t ≤ c₈ := by
    intro t hat
    have h1 := hheat n hn t (htn.trans hat)
    have h2 : Real.exp (-2 * lambdaN n * t) ≤ Real.exp (-2 * lambdaN n * a) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h3 : Real.exp (-2 * lambdaN n * a) = 1 / n := by
      rw [ha, tn, show -2 * lambdaN n * (Real.log n / (2 * lambdaN n)) = -Real.log n by
        field_simp, Real.exp_neg, Real.exp_log hn0, one_div]
    calc (n : ℝ) * oneCardEntropy n t ≤ n * (c₈ * Real.exp (-2 * lambdaN n * a)) := by
          gcongr
          exact h1.trans (by gcongr)
      _ = c₈ := by rw [h3]; field_simp
  have hpt : ∀ t ∈ Set.Icc a b, H ≤ F t := by
    rintro t ⟨hat, htb⟩
    have ht0 : 0 ≤ t := by linarith
    have h1 : H ≤ relEnt (muT n t) (unif _) := by
      have := (cycleShuffle n).antitoneOn_relEnt_semigroup _ (isProbVec_single 1)
        (Set.mem_Ici.2 ht0) (Set.mem_Ici.2 (by linarith)) htb
      simpa only [← muT_eq_single_vecMul] using this
    have h2 := relEnt_muT_le hn (htn.trans hat)
    have h3 : ∑ m ∈ Icc 1 n, (m : ℝ) * predictionError n m t ≤
        ∑ m ∈ Icc 1 n, (m : ℝ) * paperError n m t :=
      sum_le_sum fun m hm => mul_le_mul_of_nonneg_left
        (predictionError_le_paperError (by omega) (mem_Icc.1 hm).1 (mem_Icc.1 hm).2 ht0)
        (Nat.cast_nonneg _)
    have h4 := hexp t hat
    simp only [hF]
    linarith
  have hint : ∀ m ∈ Icc 1 n, IntegrableOn (fun t => paperError n m t) (Set.Ioi 0) :=
    fun m hm => integrableOn_paperError hn (mem_Icc.1 hm).2
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun t ht => lt_of_lt_of_le htn0 ht.1
  have hint' : ∀ m ∈ Icc 1 n,
      IntegrableOn (fun t => (m : ℝ) * paperError n m t) (Set.Icc a b) :=
    fun m hm => ((hint m hm).mono_set hsub).const_mul _
  have hsumint : IntegrableOn (fun t => ∑ m ∈ Icc 1 n, (m : ℝ) * paperError n m t)
      (Set.Icc a b) :=
    integrable_finsetSum _ hint'
  have hFint : IntegrableOn F (Set.Icc a b) :=
    (integrable_const _).add (hsumint.const_mul _)
  have hvol : volume.real (Set.Icc a b) = 1 / lambdaN n := by
    rw [Real.volume_real_Icc_of_le (by rw [hb]; have := one_div_pos.2 hlam; linarith), hb, ha,
      add_sub_cancel_left]
  have hmono := setIntegral_mono_on (integrable_const H) hFint measurableSet_Icc hpt
  have e1 : ∫ _ in Set.Icc a b, H = H * (1 / lambdaN n) := by
    rw [setIntegral_const, hvol, smul_eq_mul, mul_comm]
  have e2 : ∫ t in Set.Icc a b, F t = (c₈ + 3 * L) * (1 / lambdaN n) +
      2 * ∑ m ∈ Icc 1 n, (m : ℝ) * ∫ t in Set.Icc a b, paperError n m t := by
    simp only [hF]
    rw [integral_add (integrable_const _) (hsumint.const_mul _), setIntegral_const, hvol,
      smul_eq_mul, integral_const_mul, integral_finsetSum _ hint', mul_comm (1 / lambdaN n)]
    simp_rw [integral_const_mul]
  have hle : ∑ m ∈ Icc 1 n, (m : ℝ) * ∫ t in Set.Icc a b, paperError n m t ≤
      ∑ m ∈ Icc 1 n, (m : ℝ) * ∫ t in Set.Ioi 0, paperError n m t := by
    refine sum_le_sum fun m hm => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine setIntegral_mono_set (hint m hm) ?_ hsub.eventuallyLE
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    exact (predictionError_nonneg ht0 m).trans
      (predictionError_le_paperError (by omega) (mem_Icc.1 hm).1 (mem_Icc.1 hm).2 ht0)
  have htot' := htot n hn
  have hmain : H * (1 / lambdaN n) ≤
      (c₈ + 3 * L) * (1 / lambdaN n) + 2 * (K₁ * (n : ℝ) ^ 2 * L ^ 3) := by
    rw [← e1]
    linarith
  have hlamU : lambdaN n * (n : ℝ) ^ 2 ≤ 4 * π ^ 2 := by
    have := lambdaN_le_four_pi_sq_div_sq n
    rwa [le_div_iff₀ (by positivity)] at this
  have hHle : H ≤ c₈ + 3 * L + 2 * K₁ * L ^ 3 * (lambdaN n * (n : ℝ) ^ 2) := by
    have := mul_le_mul_of_nonneg_left hmain hlam.le
    have e3 : lambdaN n * (H * (1 / lambdaN n)) = H := by field_simp
    have e4 : lambdaN n * ((c₈ + 3 * L) * (1 / lambdaN n) +
        2 * (K₁ * (n : ℝ) ^ 2 * L ^ 3)) =
        c₈ + 3 * L + 2 * K₁ * L ^ 3 * (lambdaN n * (n : ℝ) ^ 2) := by
      field_simp
    linarith
  have hL3 : L ≤ L ^ 3 := le_self_pow₀ hL1 (by norm_num)
  have hL3' : 1 ≤ L ^ 3 := one_le_pow₀ hL1
  have hKL : 0 ≤ 2 * K₁ * L ^ 3 := by positivity
  calc H ≤ c₈ + 3 * L + 2 * K₁ * L ^ 3 * (lambdaN n * (n : ℝ) ^ 2) := hHle
    _ ≤ c₈ * L ^ 3 + 3 * L ^ 3 + 2 * K₁ * L ^ 3 * (4 * π ^ 2) := by
        gcongr
        · nlinarith
    _ = (c₈ + 3 + 8 * π ^ 2 * K₁) * L ^ 3 := by ring

end CycleCutoff
