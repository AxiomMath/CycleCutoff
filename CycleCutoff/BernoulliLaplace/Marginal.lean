/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.BernoulliLaplace.Defs
public import CycleCutoff.FiniteProbability.EntVarBound
public import CycleCutoff.FiniteProbability.PushforwardEntropy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Entropy of the marginal of one site on the Bernoulli--Laplace slice

Let `U` be a finite set with `|U| = N`, `1 ≤ k ≤ N - 1`, and let `ν` be the uniform measure
on the slice `Ω_{U,k}`. For `g : Ω_{U,k} → ℝ`, conditioning `g²` on the indicator
`S ↦ 1[j ∈ S]` gives a function of that indicator alone, and its entropy is controlled by the
part of the Bernoulli--Laplace energy that moves `j` out of `S`:
`Ent_ν(𝔼_ν[g² ∣ 1[j ∈ S]]) ≤ (6/N)(1 + log(N/k) + log(N/(N-k))) · E`, where
`E = 𝔼_ν[1[j ∈ S] ∑_{b ∈ U \ S} (g(S \ {j} ∪ {b}) - g(S))²]`. For `j ∉ U` both sides
vanish.

## Main results

* `CycleCutoff.ent_condExp_mem_le_blSwap`: the bound above.
-/

public section

open Finset

namespace CycleCutoff

/-- Reverse triangle inequality for the Euclidean norm of finitely supported vectors:
`(√(∑ X²) - √(∑ Y²))² ≤ ∑ (X - Y)²`. -/
private lemma sqrt_sum_sq_sub_sqrt_sum_sq_sq_le {ι : Type*} (s : Finset ι) (X Y : ι → ℝ) :
    (√(∑ i ∈ s, X i ^ 2) - √(∑ i ∈ s, Y i ^ 2)) ^ 2 ≤ ∑ i ∈ s, (X i - Y i) ^ 2 := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s X Y
  have hX : √(∑ i ∈ s, X i ^ 2) ^ 2 = ∑ i ∈ s, X i ^ 2 :=
    Real.sq_sqrt (sum_nonneg fun i _ => sq_nonneg _)
  have hY : √(∑ i ∈ s, Y i ^ 2) ^ 2 = ∑ i ∈ s, Y i ^ 2 :=
    Real.sq_sqrt (sum_nonneg fun i _ => sq_nonneg _)
  have hexp : ∑ i ∈ s, (X i - Y i) ^ 2 =
      ∑ i ∈ s, X i ^ 2 + ∑ i ∈ s, Y i ^ 2 - 2 * ∑ i ∈ s, X i * Y i := by
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [hexp]
  nlinarith

/-- A variance on `Bool`: `Var_ν(r) = ν(true) ν(false) (r(true) - r(false))²`. -/
private lemma variance_bool (ν : Bool → ℝ) (hν : ν true + ν false = 1) (r : Bool → ℝ) :
    variance ν r = ν true * ν false * (r true - r false) ^ 2 := by
  have h : ν false = 1 - ν true := by linarith
  simp only [variance, expectation, Fintype.sum_bool, h]
  ring

variable {α : Type*} [DecidableEq α]

/-- **Swap coupling.** The swap `(S, b) ↦ S \ {j} ∪ {b}`, over the pairs with `j ∈ S` and
`b ∈ U \ S`, hits each `S' ∌ j` exactly `k` times: for every `F`,
`∑_{S ∋ j} ∑_{b ∈ U \ S} F(S \ {j} ∪ {b}) = k ∑_{S' ∌ j} F(S')`. -/
private lemma sum_sum_blSwap {U : Finset α} {k : ℕ} {j : α} (hj : j ∈ U)
    (F : blSlice U k → ℝ) :
    ∑ S ∈ univ.filter (fun S : blSlice U k => j ∈ (S : Finset α)),
        ∑ b ∈ U \ (S : Finset α), F (blSwap S j b) =
      k * ∑ S ∈ univ.filter (fun S : blSlice U k => j ∉ (S : Finset α)), F S := by
  have hR : k * ∑ S ∈ univ.filter (fun S : blSlice U k => j ∉ (S : Finset α)), F S =
      ∑ S ∈ univ.filter (fun S : blSlice U k => j ∉ (S : Finset α)),
        ∑ _b ∈ (S : Finset α), F S := by
    rw [mul_sum]
    exact sum_congr rfl fun S _ => by rw [sum_const, S.card_eq, nsmul_eq_mul]
  rw [hR, sum_sigma', sum_sigma']
  refine sum_nbij' (fun x => ⟨blSwap x.1 j x.2, x.2⟩) (fun x => ⟨blSwap x.1 x.2 j, x.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨S, b⟩ hx
    simp only [mem_sigma, mem_filter, mem_univ, true_and] at hx ⊢
    obtain ⟨hjS, hb⟩ := hx
    have hbj : b ≠ j := fun h => (mem_sdiff.1 hb).2 (h ▸ hjS)
    rw [blSwap_of_mem S hjS hb]
    simp [hbj.symm]
  · rintro ⟨S, b⟩ hx
    simp only [mem_sigma, mem_filter, mem_univ, true_and] at hx ⊢
    obtain ⟨hjS, hb⟩ := hx
    have hbj : b ≠ j := fun h => hjS (h ▸ hb)
    have hjb : j ∈ U \ (S : Finset α) := mem_sdiff.2 ⟨hj, hjS⟩
    rw [blSwap_of_mem S hb hjb]
    refine ⟨mem_insert_self _ _, mem_sdiff.2 ⟨S.subset hb, ?_⟩⟩
    simp [hbj]
  · rintro ⟨S, b⟩ hx
    simp only [mem_sigma, mem_filter, mem_univ, true_and] at hx
    obtain ⟨hjS, hb⟩ := hx
    have hbj : b ≠ j := fun h => (mem_sdiff.1 hb).2 (h ▸ hjS)
    have h1 := blSwap_of_mem S hjS hb
    have hb' : b ∈ ((blSwap S j b : blSlice U k) : Finset α) := by
      rw [h1]; exact mem_insert_self _ _
    have hj' : j ∈ U \ ((blSwap S j b : blSlice U k) : Finset α) := by
      rw [h1]; exact mem_sdiff.2 ⟨hj, by simp [Ne.symm hbj]⟩
    ext1
    · ext1
      rw [blSwap_of_mem _ hb' hj', h1, erase_insert (by simp [(mem_sdiff.1 hb).2]),
        insert_erase hjS]
    · rfl
  · rintro ⟨S, b⟩ hx
    simp only [mem_sigma, mem_filter, mem_univ, true_and] at hx
    obtain ⟨hjS, hb⟩ := hx
    have hbj : b ≠ j := fun h => hjS (h ▸ hb)
    have hjb : j ∈ U \ (S : Finset α) := mem_sdiff.2 ⟨hj, hjS⟩
    have h1 := blSwap_of_mem S hb hjb
    have hj' : j ∈ ((blSwap S b j : blSlice U k) : Finset α) := by
      rw [h1]; exact mem_insert_self _ _
    have hb' : b ∈ U \ ((blSwap S b j : blSlice U k) : Finset α) := by
      rw [h1]; exact mem_sdiff.2 ⟨S.subset hb, by simp [hbj]⟩
    ext1
    · ext1
      rw [blSwap_of_mem _ hj' hb', h1, erase_insert (by simp [hjS]), insert_erase hb]
    · rfl
  · exact fun _ _ => rfl

/-- **Entropy of the one-site marginal.** On the uniform slice `Ω_{U,k}`, `1 ≤ k < |U| = N`,
the entropy of `𝔼[g² ∣ 1[j ∈ S]]` is at most
`(6/N)(1 + log(N/k) + log(N/(N-k))) 𝔼[1[j ∈ S] ∑_{b ∈ U \ S} (g(S \ {j} ∪ {b}) - g(S))²]`. -/
@[cycle_cutoff "lem_bl_marginal"]
theorem ent_condExp_mem_le_blSwap (U : Finset α) (k : ℕ)
    (hk : 1 ≤ k) (hkU : k < U.card) (j : α) (g : blSlice U k → ℝ) :
    ent (unif (blSlice U k))
        (condExp (unif (blSlice U k)) (fun S => decide (j ∈ (S : Finset α)))
          (fun S => g S ^ 2)) ≤
      6 / U.card * (1 + Real.log (U.card / k) + Real.log (U.card / (U.card - k))) *
        expectation (unif (blSlice U k)) (fun S =>
          if j ∈ (S : Finset α) then
            ∑ b ∈ U \ (S : Finset α), (g (blSwap S j b) - g S) ^ 2
          else 0) := by
  classical
  have : Nonempty (blSlice U k) := blSlice_nonempty hkU.le
  by_cases hj : j ∉ U
  · have hS : ∀ S : blSlice U k, j ∉ (S : Finset α) := fun S h => hj (S.subset h)
    have S₀ : blSlice U k := Classical.arbitrary _
    have hconst : condExp (unif (blSlice U k)) (fun S => decide (j ∈ (S : Finset α)))
        (fun S => g S ^ 2) = fun _ => condExp (unif (blSlice U k))
          (fun S => decide (j ∈ (S : Finset α))) (fun S => g S ^ 2) S₀ := by
      funext S
      simp only [condExp]
      rw [fiber_eq_of_mem (mem_fiber.2 (by simp [hS]))]
    rw [hconst, ent, isProbVec_unif.expectation_const, isProbVec_unif.expectation_const]
    simp [hS]
  rw [not_not] at hj
  set N : ℝ := (U.card : ℝ) with hNdef
  set M : ℝ := (Fintype.card (blSlice U k) : ℝ) with hMdef
  set A := (univ : Finset (blSlice U k)).filter (fun S : blSlice U k => j ∈ (S : Finset α))
    with hAdef
  set B := (univ : Finset (blSlice U k)).filter (fun S : blSlice U k => j ∉ (S : Finset α))
    with hBdef
  set a : ℝ := (A.card : ℝ) with hadef
  set c : ℝ := (B.card : ℝ) with hcdef
  set SX := ∑ S ∈ A, g S ^ 2 with hSXdef
  set SY := ∑ S ∈ B, g S ^ 2 with hSYdef
  set D := ∑ S ∈ A, ∑ b ∈ U \ (S : Finset α), (g (blSwap S j b) - g S) ^ 2 with hDdef
  have hM : 0 < M := by rw [hMdef]; exact_mod_cast Fintype.card_pos
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hNk : (0 : ℝ) < N - k := by
    rw [hNdef, sub_pos]; exact_mod_cast hkU
  have hsd : ∀ S : blSlice U k, ((U \ (S : Finset α)).card : ℝ) = N - k := by
    intro S
    rw [card_sdiff_of_subset S.subset, S.card_eq, Nat.cast_sub hkU.le]
  have hac : a + c = M := by
    rw [hadef, hcdef, hMdef, ← Nat.cast_add, hAdef, hBdef,
      card_filter_add_card_filter_not, card_univ]
  have hcount : a * (N - k) = k * c := by
    have h := sum_sum_blSwap hj (fun _ : blSlice U k => (1 : ℝ))
    simp only [sum_const, nsmul_eq_mul, mul_one] at h
    rw [← hAdef, ← hBdef] at h
    rw [hadef, hcdef, ← h]
    simp only [hsd, sum_const, nsmul_eq_mul]
  have haN : a * N = M * k := by nlinarith
  have hcN : c * N = M * (N - k) := by nlinarith
  have hN : 0 < N := by linarith
  have ha : 0 < a := by
    by_contra h; push Not at h; nlinarith [mul_pos hM hk0]
  have hc : 0 < c := by
    by_contra h; push Not at h; nlinarith [mul_pos hM hNk]
  have hX2 : ∑ S ∈ A, ∑ _b ∈ U \ (S : Finset α), g S ^ 2 = (N - k) * SX := by
    rw [hSXdef, mul_sum]
    exact sum_congr rfl fun S _ => by rw [sum_const, nsmul_eq_mul, hsd]
  have hY2 : ∑ S ∈ A, ∑ b ∈ U \ (S : Finset α), g (blSwap S j b) ^ 2 = k * SY :=
    sum_sum_blSwap hj (fun S => g S ^ 2)
  have hCS : (√((N - k) * SX) - √(k * SY)) ^ 2 ≤ D := by
    rw [← hX2, ← hY2, hDdef]
    simp only [sum_sigma']
    rw [sub_sq_comm]
    exact sqrt_sum_sq_sub_sqrt_sum_sq_sq_le (A.sigma fun S => U \ (S : Finset α))
      (fun x => g (blSwap x.1 j x.2)) (fun x => g x.1)
  set φ₁ := SX / a with hφ₁
  set φ₀ := SY / c with hφ₀
  have hφ₁0 : 0 ≤ φ₁ := div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) ha.le
  have hφ₀0 : 0 ≤ φ₀ := div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) hc.le
  set r : Bool → ℝ := fun e => if e then √φ₁ else √φ₀ with hr
  have hce : condExp (unif (blSlice U k)) (fun S => decide (j ∈ (S : Finset α)))
      (fun S => g S ^ 2) =
        fun S : blSlice U k => (fun e => r e ^ 2) (decide (j ∈ (S : Finset α))) := by
    funext S
    rw [condExp_apply]
    by_cases hS : j ∈ (S : Finset α)
    · have hfib : fiber (fun S : blSlice U k => decide (j ∈ (S : Finset α))) S = A := by
        ext w; simp [mem_fiber, hAdef, hS]
      rw [hfib]
      simp only [hS, decide_true, hr, if_true, Real.sq_sqrt hφ₁0, mass, unif_apply, ← mul_sum,
        sum_const, nsmul_eq_mul]
      rw [hφ₁, hSXdef, hadef]
      field_simp
    · have hfib : fiber (fun S : blSlice U k => decide (j ∈ (S : Finset α))) S = B := by
        ext w; simp [mem_fiber, hBdef, hS]
      rw [hfib]
      simp only [hS, decide_false, hr, Bool.false_eq_true, if_false, Real.sq_sqrt hφ₀0, mass,
        unif_apply, ← mul_sum, sum_const, nsmul_eq_mul]
      rw [hφ₀, hSYdef, hcdef]
      field_simp
  rw [hce]
  refine (ent_comp (unif (blSlice U k)) (fun S : blSlice U k => decide (j ∈ (S : Finset α)))
    fun e => r e ^ 2).trans_le ?_
  set ν' := pushforward (fun S : blSlice U k => decide (j ∈ (S : Finset α)))
    (unif (blSlice U k)) with hν'
  have hν'1 : ν' true = a / M := by
    simp only [hν', pushforward, unif_apply, sum_const, nsmul_eq_mul, decide_eq_true_eq]
    rw [← hAdef, ← hadef, div_eq_mul_inv]
  have hν'0 : ν' false = c / M := by
    simp only [hν', pushforward, unif_apply, sum_const, nsmul_eq_mul, decide_eq_false_iff_not]
    rw [← hBdef, ← hcdef, div_eq_mul_inv]
  have hprob : IsProbVec ν' := isProbVec_pushforward isProbVec_unif _
  have hp : a / M = k / N := by
    rw [div_eq_div_iff hM.ne' hN.ne']; linarith
  have hq : c / M = (N - k) / N := by
    rw [div_eq_div_iff hM.ne' hN.ne']; linarith
  set νs := min (a / M) (c / M) with hνs
  have hνs0 : 0 < νs := lt_min (div_pos ha hM) (div_pos hc hM)
  have hmin : ∀ z, νs ≤ ν' z := by
    intro z
    cases z
    · rw [hν'0]; exact min_le_right _ _
    · rw [hν'1]; exact min_le_left _ _
  have hent := ent_sq_le_variance ν' hprob νs hνs0 hmin r
  have hvar : variance ν' r = a / M * (c / M) * (√φ₁ - √φ₀) ^ 2 := by
    rw [variance_bool ν' (by rw [hν'1, hν'0, ← add_div, hac, div_self hM.ne']) r, hν'1, hν'0]
    simp [hr]
  rw [hvar] at hent
  refine hent.trans ?_
  have hE : expectation (unif (blSlice U k)) (fun S =>
      if j ∈ (S : Finset α) then ∑ b ∈ U \ (S : Finset α), (g (blSwap S j b) - g S) ^ 2
      else 0) = M⁻¹ * D := by
    rw [expectation_unif, ← sum_filter]
  rw [hE]
  have hT : 0 < a * (N - k) := mul_pos ha hNk
  have hV : a / M * (c / M) * (√φ₁ - √φ₀) ^ 2 ≤ D / (N * M) := by
    have hφ₁' : φ₁ = (N - k) * SX / (a * (N - k)) := by
      rw [hφ₁]; field_simp
    have hφ₀' : φ₀ = k * SY / (a * (N - k)) := by
      rw [hφ₀, hcount]; field_simp
    have hc' : c = M * (N - k) / N := by
      rw [eq_div_iff hN.ne']; exact hcN
    rw [hφ₁', hφ₀', Real.sqrt_div' _ hT.le, Real.sqrt_div' _ hT.le, ← sub_div, div_pow,
      Real.sq_sqrt hT.le]
    have heq : a / M * (c / M) * ((√((N - k) * SX) - √(k * SY)) ^ 2 / (a * (N - k))) =
        (√((N - k) * SX) - √(k * SY)) ^ 2 / (N * M) := by
      rw [hc']; field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right hCS (mul_pos hN hM).le
  have hV0 : 0 ≤ a / M * (c / M) * (√φ₁ - √φ₀) ^ 2 := by positivity
  have hp1 : a / M ≤ 1 := by rw [div_le_one hM]; linarith
  have hq1 : c / M ≤ 1 := by rw [div_le_one hM]; linarith
  have hpq : a / M * (c / M) ≤ νs :=
    le_min (mul_le_of_le_one_right (div_pos ha hM).le hq1)
      (mul_le_of_le_one_left (div_pos hc hM).le hp1)
  have hpq0 : 0 < a / M * (c / M) := mul_pos (div_pos ha hM) (div_pos hc hM)
  have hL0 : 0 ≤ Real.log (1 / νs) :=
    Real.log_nonneg (one_le_one_div hνs0 ((min_le_left _ _).trans hp1))
  have hL : Real.log (1 / νs) ≤ Real.log (N / k) + Real.log (N / (N - k)) := by
    calc Real.log (1 / νs) ≤ Real.log (1 / (a / M * (c / M))) :=
          Real.log_le_log (one_div_pos.2 hνs0) (one_div_le_one_div_of_le hpq0 hpq)
      _ = Real.log (N / k) + Real.log (N / (N - k)) := by
          rw [← Real.log_mul (div_pos hN hk0).ne' (div_pos hN hNk).ne', hp, hq]
          congr 1
          field_simp
  calc 6 * (1 + Real.log (1 / νs)) * (a / M * (c / M) * (√φ₁ - √φ₀) ^ 2)
      ≤ 6 * (1 + (Real.log (N / k) + Real.log (N / (N - k)))) *
          (a / M * (c / M) * (√φ₁ - √φ₀) ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hV0
    _ ≤ 6 * (1 + (Real.log (N / k) + Real.log (N / (N - k)))) * (D / (N * M)) :=
        mul_le_mul_of_nonneg_left hV (by linarith)
    _ = 6 / N * (1 + Real.log (N / k) + Real.log (N / (N - k))) * (M⁻¹ * D) := by
        field_simp
        ring

end CycleCutoff
