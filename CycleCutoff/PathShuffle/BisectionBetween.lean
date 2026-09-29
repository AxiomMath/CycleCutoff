/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.BernoulliLaplace.LsiBalanced
public import CycleCutoff.PathShuffle.TranspositionComparison
public import CycleCutoff.PathShuffle.BisectionWithin
public import CycleCutoff.Generator.DirichletFormula
public import CycleCutoff.Generator.LsiTensorization
public import CycleCutoff.FiniteProbability.PushforwardEntropy
public import CycleCutoff.FiniteProbability.CondExpPullOut

/-!
# Bisection: the between-block term

Let `N ≥ 2`, `k = ⌊N / 2⌋`, and let `S_k(σ)` be the set of cards in the first `k` positions of
`σ ∈ 𝔖_N`. There is an absolute constant `c₄ > 0` such that for every `f : 𝔖_N → ℝ`,
`Ent_u(𝔼_u[f² ∣ S_k]) ≤ c₄ N² 𝒟_{𝒯^path_N}(f)`.

## Main results

* `CycleCutoff.pushforward_bisectionSlice`: `S_k` pushes the uniform measure on `𝔖_N` to the
  uniform measure on `Ω_{[N],k}`.
* `CycleCutoff.ent_condExp_bisectionSet_le_of_ent_le`: the between-block bound for any `k ≤ N`,
  given a log-Sobolev inequality `Ent_u(g²) ≤ C 𝒟^BL(g)` on the slice.
* `CycleCutoff.exists_ent_condExp_bisectionSet_le`: the between-block bound for `k = ⌊N / 2⌋`.
-/

public section

open Finset Equiv

namespace CycleCutoff

variable {N k : ℕ}

/-- Every `k`-subset of `Fin N` is the bisection set `S_k(σ)` of some permutation `σ`. -/
theorem exists_bisectionSet_eq {A : Finset (Fin N)} (hA : A.card = k) :
    ∃ σ : Perm (Fin N), bisectionSet N k σ = A := by
  classical
  have hk : k ≤ N := hA ▸ (card_le_univ A).trans_eq (Fintype.card_fin N)
  let e : {a // a ∈ A} ≃ {i : Fin N // (i : ℕ) < k} := Fintype.equivOfCardEq (by
    rw [Fintype.card_coe, hA, Fintype.card_subtype, Fin.card_filter_val_lt, min_eq_right hk])
  refine ⟨e.extendSubtype, ?_⟩
  ext a
  rw [mem_bisectionSet]
  by_cases ha : a ∈ A
  · simp only [ha, iff_true, e.extendSubtype_apply_of_mem a ha]
    exact (e ⟨a, ha⟩).2
  · simp only [ha, iff_false]
    exact e.extendSubtype_not_mem a ha

/-- Right multiplication by `(a b)`, for `a ∈ A` and `b ∉ A`, moves the fibre `{S_k = A}` onto
the fibre `{S_k = A \ {a} ∪ {b}}`. -/
theorem bisectionSet_mul_swap_eq_iff {τ : Perm (Fin N)} {A : Finset (Fin N)} {a b : Fin N}
    (ha : a ∈ A) (hb : b ∉ A) :
    bisectionSet N k (τ * swap a b) = insert b (A.erase a) ↔ bisectionSet N k τ = A := by
  have hab : a ≠ b := fun h => hb (h ▸ ha)
  have hs : ∀ c, swap a b c ∈ A ↔ c ∈ insert b (A.erase a) := by
    intro c
    by_cases hca : c = a
    · subst hca
      simp [hab, hb]
    by_cases hcb : c = b
    · subst hcb
      simp [ha]
    · rw [swap_apply_of_ne_of_ne hca hcb]
      simp [hca, hcb]
  simp only [Finset.ext_iff, mem_bisectionSet, Perm.mul_apply, ← hs]
  exact (swap a b).forall_congr_right (q := fun c => ((τ c : ℕ) < k ↔ c ∈ A))

/-- Every fibre `{S_k = A}` of the bisection set has `k! (N - k)!` elements. -/
theorem card_filter_bisectionSet_eq {A : Finset (Fin N)} (hA : A.card = k) :
    (univ.filter fun σ : Perm (Fin N) => bisectionSet N k σ = A).card =
      k.factorial * (N - k).factorial := by
  classical
  have hk : k ≤ N := hA ▸ (card_le_univ A).trans_eq (Fintype.card_fin N)
  obtain ⟨σ₀, hσ₀⟩ := exists_bisectionSet_eq hA
  have : (univ.filter fun σ : Perm (Fin N) => bisectionSet N k σ = A) =
      fiber (bisectionSet N k) σ₀ := by
    ext σ
    simp [mem_fiber, hσ₀]
  rw [this, fiber_bisectionSet_eq_image hk σ₀, card_image_of_injective _
    (fun p q h => blockPerm_injective hk (mul_right_cancel h))]
  simp [Fintype.card_perm]

/-- The bisection set pushes the uniform measure on `𝔖_N` to the uniform measure on the slice
`Ω_{[N],k}`. -/
theorem pushforward_bisectionSlice (hk : k ≤ N) :
    pushforward (bisectionSlice N k hk) (unif (Perm (Fin N))) =
      unif (blSlice (univ : Finset (Fin N)) k) := by
  classical
  funext A
  have hcard := card_filter_bisectionSet_eq (N := N) A.card_eq
  have hA : (@filter _ (fun σ => bisectionSlice N k hk σ = A)
      (fun _ => Classical.propDecidable _) univ).card = k.factorial * (N - k).factorial := by
    convert hcard using 2
    ext σ
    simp [Subtype.ext_iff]
  simp only [pushforward, unif_apply, sum_const, nsmul_eq_mul]
  rw [hA, card_blSlice, card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.choose_mul_factorial_mul_factorial hk]
  have h1 : (k.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((N - k).factorial : ℝ) ≠ 0 := by positivity
  have h3 : ((N.choose k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos hk).ne'
  push_cast
  field_simp

/-- **Bisection, between-block term**, for any block size `k ≤ N`: if the uniform measure on the
slice `Ω_{[N],k}` satisfies `Ent_u(g²) ≤ C 𝒟^BL(g)`, then
`Ent_u(𝔼_u[f² ∣ S_k]) ≤ 8 C N³ 𝒟_{𝒯^path_N}(f)` for every `f : 𝔖_N → ℝ`. -/
theorem ent_condExp_bisectionSet_le_of_ent_le (hk : k ≤ N) {C : ℝ} (hC : 0 ≤ C)
    (hLSI : ∀ g : blSlice (univ : Finset (Fin N)) k → ℝ,
      ent (unif (blSlice (univ : Finset (Fin N)) k)) (fun A => g A ^ 2) ≤
        C * blEnergy univ k g)
    (f : Perm (Fin N) → ℝ) :
    ent (unif (Perm (Fin N)))
        (condExp (unif (Perm (Fin N))) (bisectionSet N k) fun σ => f σ ^ 2) ≤
      8 * C * (N : ℝ) ^ 3 * (pathShuffle N).dirichletForm f := by
  set u := unif (Perm (Fin N))
  set Φ := bisectionSlice N k hk
  have hu : ∀ σ, 0 < u σ := fun _ => inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos)
  let B : blSlice (univ : Finset (Fin N)) k → Finset (Perm (Fin N)) :=
    fun A => univ.filter fun σ => bisectionSet N k σ = A
  let μ := fun A => condMeasure u (B A)
  have hμ : ∀ A σ, 0 ≤ μ A σ := fun A σ =>
    div_nonneg (by split_ifs <;> simp [(hu σ).le]) (sum_nonneg fun τ _ => (hu τ).le)
  have hmass : ∀ A A', mass u (B A) = mass u (B A') := by
    intro A A'
    simp only [mass, u, unif_apply, sum_const, nsmul_eq_mul, B,
      card_filter_bisectionSet_eq A.card_eq, card_filter_bisectionSet_eq A'.card_eq]
  have hfib : ∀ σ, fiber (bisectionSet N k) σ = B (Φ σ) := fun σ => by
    ext τ
    rw [mem_fiber]
    exact ⟨fun h => Finset.mem_filter.2 ⟨mem_univ _, h⟩, fun h => (Finset.mem_filter.1 h).2⟩
  have hce : ∀ F σ, condExp u (bisectionSet N k) F σ = expectation (μ (Φ σ)) F :=
    fun F σ => by simp only [condExp, hfib]; rfl
  let G := fun A => expectation (μ A) fun σ => f σ ^ 2
  let g := fun A => √(G A)
  have hG : ∀ A, 0 ≤ G A := fun A => expectation_nonneg (hμ A) fun _ => sq_nonneg _
  have hswap : ∀ (A : blSlice (univ : Finset (Fin N)) k) (a b : Fin N),
      a ∈ (A : Finset (Fin N)) → b ∈ univ \ (A : Finset (Fin N)) → ∀ F : Perm (Fin N) → ℝ,
      expectation (μ (blSwap A a b)) F = expectation (μ A) fun σ => F (σ * swap a b) := by
    intro A a b ha hb F
    have hb' : b ∉ (A : Finset (Fin N)) := (mem_sdiff.1 hb).2
    simp only [μ, condMeasure, expectation]
    rw [← Equiv.sum_comp (Equiv.mulRight (swap a b)), hmass (blSwap A a b) A]
    refine sum_congr rfl fun σ _ => ?_
    have : Equiv.mulRight (swap a b) σ ∈ B (blSwap A a b) ↔ σ ∈ B A := by
      simp only [Equiv.coe_mulRight, B, mem_filter, mem_univ, true_and, blSwap_of_mem A ha hb]
      exact bisectionSet_mul_swap_eq_iff ha hb'
    by_cases hσ : σ ∈ B A
    · rw [if_pos (this.2 hσ), if_pos hσ]
      rfl
    · rw [if_neg (mt this.1 hσ), if_neg hσ]
      rfl
  have hpair : ∀ (A : blSlice (univ : Finset (Fin N)) k) (a b : Fin N),
      a ∈ (A : Finset (Fin N)) → b ∈ univ \ (A : Finset (Fin N)) →
      (g (blSwap A a b) - g A) ^ 2 ≤ expectation (μ A) fun σ => (f (σ * swap a b) - f σ) ^ 2 := by
    intro A a b ha hb
    simp only [g, G, hswap A a b ha hb]
    exact sq_sqrt_sub_sqrt_le (hμ A) _ _
  set X : Fin N → Fin N → Perm (Fin N) → ℝ := fun a b σ => (f (σ * swap a b) - f σ) ^ 2
  set h : Fin N → Fin N → Finset (Fin N) → ℝ := fun a b S => if a ∈ S ∧ b ∉ S then 1 else 0
  have hsplit : ∀ (S : Finset (Fin N)) (Y : Fin N → Fin N → ℝ),
      ∑ a ∈ S, ∑ b ∈ univ \ S, Y a b = ∑ a, ∑ b, h a b S * Y a b := by
    intro S Y
    calc ∑ a ∈ S, ∑ b ∈ univ \ S, Y a b
        = ∑ a, if a ∈ S then ∑ b, (if b ∈ univ \ S then Y a b else 0) else 0 := by
          simp only [sum_ite_mem, univ_inter]
      _ = _ := sum_congr rfl fun a _ => by
          split_ifs with ha
          · exact sum_congr rfl fun b _ => by by_cases hb : b ∈ S <;> simp [h, ha, hb]
          · exact (sum_eq_zero fun b _ => by simp [h, ha]).symm
  have hE : blEnergy univ k g ≤
      expectation u fun σ => ∑ a, ∑ b, h a b (bisectionSet N k σ) * X a b σ := by
    calc blEnergy univ k g
        ≤ expectation (unif (blSlice (univ : Finset (Fin N)) k)) fun A =>
            ∑ a, ∑ b, h a b A * expectation (μ A) (X a b) := by
          refine expectation_mono (fun _ => inv_nonneg.2 (Nat.cast_nonneg _)) fun A => ?_
          rw [← hsplit]
          exact sum_le_sum fun a ha => sum_le_sum fun b hb => hpair A a b ha hb
      _ = expectation u fun σ =>
            ∑ a, ∑ b, h a b (bisectionSet N k σ) * condExp u (bisectionSet N k) (X a b) σ := by
          rw [← pushforward_bisectionSlice hk, ← expectation_comp]
          simp only [hce]
          rfl
      _ = _ := by
          simp only [expectation_sum]
          exact sum_congr rfl fun a _ => sum_congr rfl fun b _ =>
            (expectation_mul_condExp u hu (bisectionSet N k) (h a b) (X a b)).symm
  have hpt : ∀ σ, ∑ a, ∑ b, h a b (bisectionSet N k σ) * X a b σ ≤
      ∑ i : Fin N, ∑ j : Fin N with i < j, (f (swap i j * σ) - f σ) ^ 2 := by
    intro σ
    have : ∑ a, ∑ b, h a b (bisectionSet N k σ) * X a b σ = ∑ i : Fin N, ∑ j : Fin N,
        (if (i : ℕ) < k ∧ ¬ (j : ℕ) < k then 1 else 0) * (f (swap i j * σ) - f σ) ^ 2 := by
      conv_rhs => rw [← Equiv.sum_comp σ]
      refine sum_congr rfl fun a _ => ?_
      conv_rhs => rw [← Equiv.sum_comp σ]
      refine sum_congr rfl fun b _ => ?_
      simp only [h, X, mem_bisectionSet, mul_swap_eq_swap_mul]
    rw [this]
    refine sum_le_sum fun i _ => ?_
    rw [sum_filter]
    refine sum_le_sum fun j _ => ?_
    split_ifs with h1 h2 h2
    · simp
    · exact absurd (Fin.lt_def.2 (by omega)) h2
    · simp only [zero_mul]; positivity
    · simp
  calc ent u (condExp u (bisectionSet N k) fun σ => f σ ^ 2)
      = ent (unif (blSlice (univ : Finset (Fin N)) k)) fun A => g A ^ 2 := by
        rw [← pushforward_bisectionSlice hk, ← ent_comp]
        congr 1
        funext σ
        rw [hce]
        exact (Real.sq_sqrt (hG _)).symm
    _ ≤ C * blEnergy univ k g := hLSI g
    _ ≤ C * (8 * (N : ℝ) ^ 3 * (pathShuffle N).dirichletForm f) := by
        gcongr
        calc blEnergy univ k g
            ≤ expectation u fun σ =>
                ∑ i : Fin N, ∑ j : Fin N with i < j, (f (swap i j * σ) - f σ) ^ 2 :=
              hE.trans (expectation_mono (fun σ => (hu σ).le) hpt)
          _ = ∑ i : Fin N, ∑ j : Fin N with i < j,
                expectation u fun σ => (f (swap i j * σ) - f σ) ^ 2 := by
              simp only [expectation_sum]
          _ ≤ _ := sum_expectation_swap_sq_le N f
          _ = _ := by
              rw [InvFamily.dirichletForm_eq]
              ring
    _ = 8 * C * (N : ℝ) ^ 3 * (pathShuffle N).dirichletForm f := by ring

/-- **Bisection, between-block term.** There is an absolute constant `c₄ > 0` such that for all
`N ≥ 2`, `k = ⌊N / 2⌋` and `f : 𝔖_N → ℝ`, `Ent_u(𝔼_u[f² ∣ S_k]) ≤ c₄ N² 𝒟_{𝒯^path_N}(f)`. -/
@[cycle_cutoff "lem_bisection_between"]
theorem exists_ent_condExp_bisectionSet_le :
    ∃ c₄ > 0, ∀ N : ℕ, 2 ≤ N → ∀ f : Equiv.Perm (Fin N) → ℝ,
      ent (unif (Equiv.Perm (Fin N)))
          (condExp (unif (Equiv.Perm (Fin N))) (bisectionSet N (N / 2)) (fun σ => f σ ^ 2)) ≤
        c₄ * (N : ℝ) ^ 2 * (pathShuffle N).dirichletForm f := by
  obtain ⟨c₂, hc₂, hBL⟩ := exists_ent_sq_le_blEnergy_half
  refine ⟨8 * c₂, by positivity, fun N hN f => ?_⟩
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hLSI : ∀ g : blSlice (univ : Finset (Fin N)) (N / 2) → ℝ,
      ent (unif (blSlice (univ : Finset (Fin N)) (N / 2))) (fun A => g A ^ 2) ≤
        c₂ / N * blEnergy univ (N / 2) g := fun g => by
    have := hBL (univ : Finset (Fin N)) (N / 2) (by simp [hN]) (by simp) g
    rwa [card_univ, Fintype.card_fin] at this
  exact (ent_condExp_bisectionSet_le_of_ent_le (Nat.div_le_self N 2) (by positivity)
    hLSI f).trans_eq (by field_simp)

end CycleCutoff
