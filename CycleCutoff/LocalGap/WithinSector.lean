/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.LocalGap.SharedComparison
public import CycleCutoff.PathShuffle.ColoredPoincare

/-!
# Within-sector variance

Let `D : Ω^p_{s,k} → Bool` record whether a state `(R, x, y)` lies on the diagonal `x = y`. There
is an absolute constant `K₂ > 0` with `𝔼_ν[Var_ν(f ∣ D)] ≤ K₂ s² 𝒟^p_{s,k}(f)` for every
`f : Ω^p_{s,k} → ℝ`, where `ν` is uniform.

## Main results

* `CycleCutoff.condExp_unif_apply`: under the uniform measure, `𝔼[g ∣ D]` is the plain average of
  `g` over the fibre.
* `CycleCutoff.expectation_condVar_unif_le`: for any involution family and any map `D`, a
  sector-by-sector Poincaré bound
  `∑_{w ∈ Σ} (f w - avg_Σ f)² ≤ (K / 2) ∑_j ∑_{w ∈ Σ} (f(T_j w) - f w)²` on every fibre `Σ` of `D`
  gives `𝔼_u[Var_u(f ∣ D)] ≤ K 𝒟(f)`.
* `CycleCutoff.sum_sq_sub_avg_le_of_equiv`: a Poincaré inequality transported to a subset along an
  intertwining bijection.
* `CycleCutoff.exists_expectation_condVar_diag_le`: `𝔼_ν[Var_ν(f ∣ D)] ≤ K₂ s² 𝒟^p_{s,k}(f)`.

## Implementation notes

* `D` is `fun w => decide (w.x = w.y)`, valued in `Bool`.
* No hypothesis on `s` or `k` is assumed: an empty sector contributes nothing.
-/

public section

open Finset

namespace CycleCutoff

/-! ### Averaging over the fibres of a map -/

section Fiberwise

variable {Ω Y : Type*} [Fintype Ω]

/-- Summing the fibre averages `(∑_{w ∈ D⁻¹D(z)} G w) / |D⁻¹D(z)|` over all `z` recovers
`∑_w G w`. -/
theorem sum_sum_fiber_div_card (D : Ω → Y) (G : Ω → ℝ) :
    ∑ z, (∑ w ∈ fiber D z, G w) / (fiber D z).card = ∑ w, G w := by
  have h1 : ∀ z, (∑ w ∈ fiber D z, G w) / (fiber D z).card =
      ∑ w ∈ fiber D z, G w / (fiber D w).card := fun z => by
    rw [sum_div]
    exact sum_congr rfl fun w hw => by rw [fiber_eq_of_mem hw]
  simp_rw [h1]
  rw [Finset.sum_comm' (t' := univ) (s' := fun w => fiber D w) (fun z w => by
    simp only [mem_univ, true_and, and_true, mem_fiber]; exact eq_comm)]
  refine sum_congr rfl fun w _ => ?_
  rw [sum_const, nsmul_eq_mul,
    mul_div_cancel₀ _ (Nat.cast_ne_zero.2 (card_ne_zero_of_mem (mem_fiber_self D w)))]

/-- The conditional expectation under the uniform measure is the plain average over the fibre. -/
theorem condExp_unif_apply (D : Ω → Y) (g : Ω → ℝ) (z : Ω) :
    condExp (unif Ω) D g z = (∑ w ∈ fiber D z, g w) / (fiber D z).card := by
  have : Nonempty Ω := ⟨z⟩
  have hΩ : ((Fintype.card Ω : ℝ))⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  simp only [condExp_apply, unif, mass, sum_const, nsmul_eq_mul, ← mul_sum]
  rw [mul_comm ((fiber D z).card : ℝ), mul_div_mul_left _ _ hΩ]

/-- A fibre-by-fibre Poincaré bound for an involution family gives the corresponding bound on the
expected conditional variance: if on every fibre `Σ` of `D`,
`∑_{w ∈ Σ} (f w - avg_Σ f)² ≤ (K / 2) ∑_j ∑_{w ∈ Σ} (f(T_j w) - f w)²`, then
`𝔼_u[Var_u(f ∣ D)] ≤ K 𝒟_𝒮(f)`. -/
theorem expectation_condVar_unif_le {ι : Type*} [Fintype ι] (𝒮 : InvFamily ι Ω) (D : Ω → Y)
    (f : Ω → ℝ) {K : ℝ}
    (h : ∀ z, ∑ w ∈ fiber D z, (f w - (∑ v ∈ fiber D z, f v) / (fiber D z).card) ^ 2 ≤
      K / 2 * ∑ j, ∑ w ∈ fiber D z, (f (𝒮.T j w) - f w) ^ 2) :
    expectation (unif Ω) (condVar (unif Ω) D f) ≤ K * 𝒮.dirichletForm f := by
  have hcV : ∀ z, condVar (unif Ω) D f z =
      (∑ w ∈ fiber D z, (f w - (∑ v ∈ fiber D z, f v) / (fiber D z).card) ^ 2) /
        (fiber D z).card := fun z => by
    rw [condVar, condExp_unif_apply]
    congr 1
    exact sum_congr rfl fun w hw => by rw [condExp_unif_apply, fiber_eq_of_mem hw]
  simp only [expectation_unif, InvFamily.dirichletForm_eq]
  calc (Fintype.card Ω : ℝ)⁻¹ * ∑ z, condVar (unif Ω) D f z
      ≤ (Fintype.card Ω : ℝ)⁻¹ * ∑ z, (∑ w ∈ fiber D z,
          K / 2 * ∑ j, (f (𝒮.T j w) - f w) ^ 2) / (fiber D z).card := by
        gcongr with z
        rw [hcV, ← mul_sum, sum_comm]
        gcongr
        exact h z
    _ = (Fintype.card Ω : ℝ)⁻¹ * ∑ w, K / 2 * ∑ j, (f (𝒮.T j w) - f w) ^ 2 := by
        rw [sum_sum_fiber_div_card]
    _ = K * (1 / 2 * ∑ j, (Fintype.card Ω : ℝ)⁻¹ * ∑ z, (f (𝒮.T j z) - f z) ^ 2) := by
        rw [← mul_sum, ← mul_sum, sum_comm]
        ring

omit [Fintype Ω] in
/-- Transport of a Poincaré inequality to a subset `B` along a bijection `e : C ≃ B` that
intertwines the two involution families: `∑_{w ∈ B} (f w - avg_B f)²` is at most `K / 2` times
`∑_j ∑_{w ∈ B} (f(S_j w) - f w)²`. -/
theorem sum_sq_sub_avg_le_of_equiv {C ι : Type*} [Fintype C] [Fintype ι]
    (𝒮 : InvFamily ι Ω) (𝒯 : InvFamily ι C) (B : Finset Ω) (e : C ≃ B)
    (he : ∀ j c, (e (𝒯.T j c) : Ω) = 𝒮.T j (e c)) {K : ℝ}
    (hP : ∀ F : C → ℝ, variance (unif C) F ≤ K * 𝒯.dirichletForm F) (f : Ω → ℝ) :
    ∑ w ∈ B, (f w - (∑ v ∈ B, f v) / B.card) ^ 2 ≤
      K / 2 * ∑ j, ∑ w ∈ B, (f (𝒮.T j w) - f w) ^ 2 := by
  have hsum : ∀ g : Ω → ℝ, ∑ c, g (e c) = ∑ w ∈ B, g w := fun g => by
    rw [Equiv.sum_comp e (fun w : B => g w), Finset.sum_coe_sort B g]
  have hcard : (Fintype.card C : ℝ) = B.card := by
    rw [Fintype.card_congr e, Fintype.card_coe]
  have hP' := hP (fun c => f (e c))
  rw [InvFamily.dirichletForm_eq] at hP'
  simp only [variance, expectation_unif, he] at hP'
  rw [hcard, hsum f, hsum (fun w => (f w - (B.card : ℝ)⁻¹ * ∑ v ∈ B, f v) ^ 2)] at hP'
  simp only [fun j => hsum (fun w => (f (𝒮.T j w) - f w) ^ 2)] at hP'
  rcases B.eq_empty_or_nonempty with rfl | hB
  · simp
  have hn : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  rw [← mul_sum] at hP'
  rw [div_eq_inv_mul]
  exact le_of_mul_le_mul_left (hP'.trans_eq (by ring)) (inv_pos.2 hn)

end Fiberwise

/-! ### The sector colouring -/

namespace TwoCopyState

variable {V : Type*} [DecidableEq V] {m : ℕ}

/-- The colouring of `V` by a two-copy state `(R, x, y)`: colour `0` at `x`, colour `1` at `y ≠ x`,
colour `2` on `R ∖ {x, y}`, colour `3` off `R`. -/
private def coloring (w : TwoCopyState V m) (p : V) : Fin 4 :=
  if p = w.x then 0 else if p = w.y then 1 else if p ∈ w.R then 2 else 3

private theorem coloring_eq_zero_iff (w : TwoCopyState V m) (p : V) :
    coloring w p = 0 ↔ p = w.x := by
  unfold coloring; split_ifs <;> simp_all

private theorem coloring_eq_one_iff (w : TwoCopyState V m) (p : V) :
    coloring w p = 1 ↔ p = w.y ∧ p ≠ w.x := by
  unfold coloring; split_ifs <;> simp_all

private theorem coloring_eq_two_iff (w : TwoCopyState V m) (p : V) :
    coloring w p = 2 ↔ p ∈ (w.R.erase w.x).erase w.y := by
  unfold coloring; split_ifs <;> simp_all

private theorem coloring_eq_three_iff (w : TwoCopyState V m) (p : V) :
    coloring w p = 3 ↔ p ∉ w.R := by
  unfold coloring
  split_ifs <;> simp_all [w.x_mem, w.y_mem]

private theorem coloring_permMap (w : TwoCopyState V m) (τ : Equiv.Perm V) (p : V) :
    coloring (w.permMap τ) p = coloring w (τ.symm p) := by
  simp only [coloring, x_permMap, y_permMap, R_permMap, mem_map_equiv, ← Equiv.symm_apply_eq]

/-- The colour counts `𝐤_1 = (1, 0, k - 1, s - k)` of the diagonal sector and
`𝐤_0 = (1, 1, k - 2, s - k)` of the off-diagonal sector. -/
private def sectorCounts (s k : ℕ) (d : Bool) : Fin 4 → ℕ :=
  ![1, if d then 0 else 1, if d then k - 1 else k - 2, s - k]

private theorem card_filter_coloring [Fintype V] (w : TwoCopyState V m) (a : Fin 4) :
    (univ.filter fun p => coloring w p = a).card =
      sectorCounts (Fintype.card V) m (decide (w.x = w.y)) a := by
  fin_cases a
  · simp [coloring_eq_zero_iff, sectorCounts, filter_eq']
  · by_cases hxy : w.x = w.y
    · simp [coloring_eq_one_iff, sectorCounts, hxy]
    · simp [coloring_eq_one_iff, sectorCounts, hxy, filter_and, filter_eq', filter_ne',
        singleton_inter_of_mem, Ne.symm hxy]
  · have : (univ.filter fun p => coloring w p = 2) = (w.R.erase w.x).erase w.y := by
      ext p; simp [coloring_eq_two_iff]
    simp only [Fin.reduceFinMk, Fin.isValue]
    by_cases hxy : w.x = w.y
    · rw [this, ← hxy, erase_eq_of_notMem (notMem_erase _ _), card_erase_of_mem w.x_mem, w.card_R]
      simp [sectorCounts, hxy]
    · rw [this, card_erase_of_mem (mem_erase.2 ⟨Ne.symm hxy, w.y_mem⟩),
        card_erase_of_mem w.x_mem, w.card_R]
      simp [sectorCounts, hxy, Nat.sub_sub]
  · simp [coloring_eq_three_iff, filter_not, card_univ_sdiff, w.card_R, sectorCounts]

end TwoCopyState

/-! ### The sector bijections -/

section Sector

open TwoCopyState

variable {s k : ℕ}

/-- The colouring of a state in the sector of `z`, as a coloured configuration. -/
private def sectorMap (z : TwoCopyState (Fin s) k)
    (w : fiber (fun w : TwoCopyState (Fin s) k => decide (w.x = w.y)) z) :
    ColoredConfig s (sectorCounts s k (decide (z.x = z.y))) :=
  ⟨coloring w.1, fun a => by
    rw [card_filter_coloring, Fintype.card_fin, ← mem_fiber.1 w.2]⟩

private theorem sectorMap_injective (z : TwoCopyState (Fin s) k) :
    Function.Injective (sectorMap z) := by
  rintro ⟨w, hw⟩ ⟨w', hw'⟩ h
  have hc : ∀ p, coloring w p = coloring w' p := fun p => congrFun (congrArg Subtype.val h) p
  have hD : decide (w.x = w.y) = decide (w'.x = w'.y) :=
    (mem_fiber.1 hw).trans (mem_fiber.1 hw').symm
  have hx : w.x = w'.x :=
    (coloring_eq_zero_iff w' w.x).1 ((hc w.x).symm.trans ((coloring_eq_zero_iff w w.x).2 rfl))
  have hR : w.R = w'.R := by
    ext p
    rw [← not_iff_not, ← coloring_eq_three_iff, ← coloring_eq_three_iff, hc]
  have hy : w.y = w'.y := by
    by_cases hxy : w.x = w.y
    · rw [← hxy, ← (by simpa [hxy] using hD : w'.x = w'.y), hx]
    · exact ((coloring_eq_one_iff w' w.y).1
        ((hc w.y).symm.trans ((coloring_eq_one_iff w w.y).2 ⟨rfl, Ne.symm hxy⟩))).1
  exact Subtype.ext (TwoCopyState.ext_iff'.2 ⟨hR, hx, hy⟩)

private theorem sectorMap_surjective (z : TwoCopyState (Fin s) k) :
    Function.Surjective (sectorMap z) := by
  rintro ⟨c, hc⟩
  have hks : k ≤ s := by simpa [z.card_R] using card_le_univ z.R
  suffices ∃ w : TwoCopyState (Fin s) k, decide (w.x = w.y) = decide (z.x = z.y) ∧
      coloring w = c by
    obtain ⟨w, hw, hwc⟩ := this
    exact ⟨⟨w, mem_fiber.2 hw⟩, Subtype.ext hwc⟩
  generalize decide (z.x = z.y) = d at hc ⊢
  obtain ⟨a₀, ha₀⟩ := card_eq_one.1 (by simpa [sectorCounts] using hc 0)
  have h₀ : ∀ p, c p = 0 ↔ p = a₀ := fun p => by simpa using congrArg (p ∈ ·) ha₀
  have h₃ : (univ.filter fun p => c p ≠ 3).card = k := by
    rw [filter_not, card_sdiff_of_subset (filter_subset _ _), card_univ, Fintype.card_fin, hc 3]
    simp only [sectorCounts, Matrix.cons_val]
    lia
  obtain ⟨y, h₁, hya⟩ : ∃ y : Fin s, (∀ p, c p = 1 ↔ p = y ∧ p ≠ a₀) ∧ (d = true ↔ y = a₀) := by
    cases d
    · obtain ⟨a₁, ha₁⟩ := card_eq_one.1 (by simpa [sectorCounts] using hc 1)
      have h₁ : ∀ p, c p = 1 ↔ p = a₁ := fun p => by simpa using congrArg (p ∈ ·) ha₁
      have hne : a₁ ≠ a₀ := fun h => absurd ((h₁ a₁).2 rfl) (by rw [h, (h₀ a₀).2 rfl]; decide)
      exact ⟨a₁, fun p => (h₁ p).trans ⟨fun h => ⟨h, h ▸ hne⟩, And.left⟩, by simp [hne]⟩
    · have hc1 : ∀ p, c p ≠ 1 := by simpa [sectorCounts] using hc 1
      exact ⟨a₀, fun p => iff_of_false (hc1 p) fun h => h.2 h.1, by simp⟩
  have hmem : ∀ p, p ∈ univ.filter (fun p => c p ≠ 3) ↔ c p ≠ 3 := fun p => by simp
  have ha₀R : a₀ ∈ univ.filter (fun p => c p ≠ 3) := by
    rw [hmem, (h₀ a₀).2 rfl]; decide
  have hyR : y ∈ univ.filter (fun p => c p ≠ 3) := by
    rcases eq_or_ne y a₀ with rfl | hy
    · exact ha₀R
    · rw [hmem, (h₁ y).2 ⟨rfl, hy⟩]; decide
  refine ⟨⟨(univ.filter fun p => c p ≠ 3, a₀, y), h₃, ha₀R, hyR⟩, ?_, ?_⟩
  · simp only [x_mk, y_mk]
    cases d <;> simp_all [eq_comm]
  · funext p
    simp only [coloring, x_mk, y_mk, R_mk, hmem]
    split_ifs with hp₀ hp₁ hp₃
    · exact ((h₀ p).2 hp₀).symm
    · exact ((h₁ p).2 ⟨hp₁, hp₀⟩).symm
    · have n0 : c p ≠ 0 := mt (h₀ p).1 hp₀
      have n1 : c p ≠ 1 := fun h => hp₁ ((h₁ p).1 h).1
      grind
    · exact (not_not.1 hp₃).symm

private theorem sectorMap_sharedChain (z : TwoCopyState (Fin s) k) (j : Fin (s - 1))
    (w : fiber (fun w : TwoCopyState (Fin s) k => decide (w.x = w.y)) z)
    (hw : (sharedChain s k).T j w.1 ∈
      fiber (fun w : TwoCopyState (Fin s) k => decide (w.x = w.y)) z) :
    sectorMap z ⟨_, hw⟩ = (coloredProcess s _).T j (sectorMap z w) := by
  refine Subtype.ext (funext fun p => ?_)
  simp [sectorMap, sharedChain_T, coloredProcess_T_val, coloring_permMap, adjSwap,
    Equiv.symm_swap]

private theorem sharedChain_mem_fiber (z : TwoCopyState (Fin s) k) (j : Fin (s - 1))
    {w : TwoCopyState (Fin s) k}
    (hw : w ∈ fiber (fun w : TwoCopyState (Fin s) k => decide (w.x = w.y)) z) :
    (sharedChain s k).T j w ∈ fiber (fun w : TwoCopyState (Fin s) k => decide (w.x = w.y)) z := by
  rw [mem_fiber] at hw ⊢
  simpa [sharedChain_T, (adjSwap s j).injective.eq_iff] using hw

end Sector

/-- **Within-sector variance.** There is an absolute constant `K₂ > 0` such that, with
`D(R, x, y) = 1[x = y]` and `ν` uniform on `Ω^p_{s,k}`, `𝔼_ν[Var_ν(f ∣ D)] ≤ K₂ s² 𝒟^p_{s,k}(f)`
for every `f`. -/
@[cycle_cutoff "lem_within_sector"]
theorem exists_expectation_condVar_diag_le :
    ∃ K₂ > 0, ∀ s k : ℕ, ∀ f : TwoCopyState (Fin s) k → ℝ,
      expectation (unif (TwoCopyState (Fin s) k))
          (condVar (unif (TwoCopyState (Fin s) k)) (fun w => decide (w.x = w.y)) f) ≤
        K₂ * (s : ℝ) ^ 2 * (pathTwoCopy s k).dirichletForm f := by
  obtain ⟨c, hc, hP⟩ := exists_variance_le_coloredProcess.{0}
  refine ⟨2 * c, by positivity, fun s k f => ?_⟩
  have hsec := expectation_condVar_unif_le (sharedChain s k)
    (fun w : TwoCopyState (Fin s) k => decide (w.x = w.y)) f (K := c * (s : ℝ) ^ 2)
    (fun z => by
      have hb : Function.Bijective (sectorMap z) :=
        ⟨sectorMap_injective z, sectorMap_surjective z⟩
      refine sum_sq_sub_avg_le_of_equiv (sharedChain s k) (coloredProcess s _) _
        (Equiv.ofBijective _ hb).symm (fun j c' => ?_) (fun F => by convert hP s _ F) f
      obtain ⟨w, rfl⟩ := (Equiv.ofBijective _ hb).surjective c'
      have key : (coloredProcess s _).T j (Equiv.ofBijective _ hb w) =
          Equiv.ofBijective _ hb ⟨_, sharedChain_mem_fiber z j w.2⟩ :=
        (sectorMap_sharedChain z j w _).symm
      rw [key, Equiv.symm_apply_apply, Equiv.symm_apply_apply])
  calc _ ≤ c * (s : ℝ) ^ 2 * (sharedChain s k).dirichletForm f := hsec
    _ ≤ c * (s : ℝ) ^ 2 * (2 * (pathTwoCopy s k).dirichletForm f) :=
        mul_le_mul_of_nonneg_left (dirichletForm_sharedChain_le s k f) (by positivity)
    _ = _ := by ring

end CycleCutoff
