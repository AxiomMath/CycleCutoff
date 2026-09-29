/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.PathShuffle.Defs
public import CycleCutoff.Generator.LsiTensorization
public import CycleCutoff.Generator.DirichletTransport
public import CycleCutoff.FiniteProbability.PushforwardEntropy
public import CycleCutoff.FiniteProbability.CondExpPullOut
public import Mathlib.GroupTheory.Perm.Finite

/-!
# Bisection: the within-block term

Let `N ≥ 2`, `k = ⌊N / 2⌋`, and suppose the path shuffles on `𝔖_k` and `𝔖_{N-k}` satisfy
log-Sobolev inequalities with constants `A₁` and `A₂`. Then for every `f : 𝔖_N → ℝ`,
`𝔼_u[Ent_u(f² ∣ S_k)] ≤ max(A₁, A₂) 𝒟_{𝒯^path_N}(f)`,
where `S_k(σ)` is the set of cards in the first `k` positions. The bound holds for every block
size `k ≤ N` when both blocks satisfy the inequality with a common constant `A ≥ 0`.

## Main definitions

* `CycleCutoff.blockEquiv`: the block identification `Fin k ⊕ Fin (N - k) ≃ Fin N`.
* `CycleCutoff.blockPerm`: the block permutation `e (π₁ ⊕ π₂) e⁻¹` of `Fin N`.
* `CycleCutoff.blockIndex`: the embedding of the adjacent transpositions of the two blocks into
  those of `Fin N`.

## Main results

* `CycleCutoff.fiber_bisectionSet_eq_image`: the fibre of `S_k` through `σ₀` is
  `{π σ₀ : π a block permutation}`.
* `CycleCutoff.expectation_condEnt_bisectionSet_le_of_le`: the within-block bound for any
  `k ≤ N`.
* `CycleCutoff.expectation_condEnt_bisectionSet_le`: the within-block bound for `k = ⌊N / 2⌋`.
-/

public section

open Finset Equiv

namespace CycleCutoff

section Block

variable {N k : ℕ}

/-- The block identification `Fin k ⊕ Fin (N - k) ≃ Fin N`, for `k ≤ N`. -/
def blockEquiv (hk : k ≤ N) : Fin k ⊕ Fin (N - k) ≃ Fin N :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hk))

/-- The block identification sends `a` in the first block to position `a`. -/
@[simp] theorem val_blockEquiv_inl (hk : k ≤ N) (a : Fin k) :
    (blockEquiv hk (.inl a) : ℕ) = a := by
  simp [blockEquiv]

/-- The block identification sends `b` in the second block to position `k + b`. -/
@[simp] theorem val_blockEquiv_inr (hk : k ≤ N) (b : Fin (N - k)) :
    (blockEquiv hk (.inr b) : ℕ) = k + b := by
  simp [blockEquiv]

/-- A position lies in `[0, k)` iff it comes from the first block. -/
theorem val_blockEquiv_lt_iff (hk : k ≤ N) (s : Fin k ⊕ Fin (N - k)) :
    (blockEquiv hk s : ℕ) < k ↔ s.isLeft := by
  cases s with
  | inl a => simp [a.isLt]
  | inr b => simp

/-- The block permutation `e (π₁ ⊕ π₂) e⁻¹` of `Fin N`: `π₁` acts on the positions `[0, k)` and
`π₂` on the positions `[k, N)`. -/
def blockPerm (hk : k ≤ N) (p : Perm (Fin k) × Perm (Fin (N - k))) : Perm (Fin N) :=
  (blockEquiv hk).permCongr (Perm.sumCongr p.1 p.2)

/-- The map `(π₁, π₂) ↦ e (π₁ ⊕ π₂) e⁻¹` is injective. -/
theorem blockPerm_injective (hk : k ≤ N) : Function.Injective (blockPerm (N := N) hk) := by
  intro p q h
  apply Perm.sumCongrHom_injective
  simpa [Perm.sumCongrHom_apply, blockPerm] using h

/-- A block permutation preserves the block `[0, k)`. -/
theorem val_blockPerm_lt_iff (hk : k ≤ N) (p : Perm (Fin k) × Perm (Fin (N - k))) (i : Fin N) :
    (blockPerm hk p i : ℕ) < k ↔ (i : ℕ) < k := by
  obtain ⟨s, rfl⟩ := (blockEquiv hk).surjective i
  cases s with
  | inl a => simp [blockPerm, Equiv.permCongr_apply, a.isLt, (p.1 a).isLt]
  | inr b => simp [blockPerm, Equiv.permCongr_apply]

/-- Every permutation of `Fin N` preserving the block `[0, k)` is a block permutation. -/
theorem exists_blockPerm_eq (hk : k ≤ N) {π : Perm (Fin N)}
    (hπ : ∀ i, (π i : ℕ) < k ↔ (i : ℕ) < k) : ∃ p, blockPerm hk p = π := by
  set π' : Perm (Fin k ⊕ Fin (N - k)) := (blockEquiv hk).symm.permCongr π
  have hmaps : Set.MapsTo π' (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro _ ⟨a, rfl⟩
    have h : (blockEquiv hk (π' (.inl a)) : ℕ) < k := by
      simp only [π', Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
      exact (hπ _).2 (by simp [a.isLt])
    rw [val_blockEquiv_lt_iff, Sum.isLeft_iff] at h
    obtain ⟨b, hb⟩ := h
    exact ⟨b, hb.symm⟩
  obtain ⟨p, hp⟩ := Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hmaps
  refine ⟨p, ?_⟩
  rw [Perm.sumCongrHom_apply] at hp
  rw [blockPerm, hp]
  change (blockEquiv hk).permCongr ((blockEquiv hk).symm.permCongr π) = π
  rw [← Equiv.permCongr_symm, Equiv.apply_symm_apply]

/-- The fibre of the bisection set `S_k` through `σ₀` is `{π σ₀}` over the block permutations
`π`. -/
theorem fiber_bisectionSet_eq_image (hk : k ≤ N) (σ₀ : Perm (Fin N)) :
    fiber (bisectionSet N k) σ₀ = univ.image fun p => blockPerm hk p * σ₀ := by
  ext σ
  rw [mem_fiber, mem_image]
  constructor
  · intro h
    have hπ : ∀ i, ((σ * σ₀⁻¹) i : ℕ) < k ↔ (i : ℕ) < k := by
      intro i
      obtain ⟨a, rfl⟩ := σ₀.surjective i
      simpa [Perm.mul_apply] using congrArg (a ∈ ·) h
    obtain ⟨p, hp⟩ := exists_blockPerm_eq hk hπ
    exact ⟨p, mem_univ _, by rw [hp, inv_mul_cancel_right]⟩
  · rintro ⟨p, -, rfl⟩
    ext a
    simp [Perm.mul_apply, val_blockPerm_lt_iff]

/-- The index embedding `Fin (k - 1) ⊕ Fin (N - k - 1) ↪ Fin (N - 1)`: the adjacent
transpositions inside the first block, then those inside the second block shifted by `k`. -/
def blockIndex (hk : k ≤ N) : Fin (k - 1) ⊕ Fin (N - k - 1) ↪ Fin (N - 1) where
  toFun
    | .inl j => ⟨j, by omega⟩
    | .inr j => ⟨k + j, by omega⟩
  inj' := by
    rintro (a | a) (b | b) h <;> simp only [Fin.mk.injEq] at h
    · exact congrArg _ (Fin.ext h)
    · omega
    · omega
    · exact congrArg _ (Fin.ext (by omega))

/-- Block permutations intertwine the product of the two path shuffles with the path shuffle
on `Fin N`, along `blockIndex`. -/
theorem blockPerm_prod_T (hk : k ≤ N) (e : Fin (k - 1) ⊕ Fin (N - k - 1))
    (p : Perm (Fin k) × Perm (Fin (N - k))) :
    blockPerm hk (((pathShuffle k).prod (pathShuffle (N - k))).T e p) =
      adjSwap N (blockIndex hk e) * blockPerm hk p := by
  cases e with
  | inl j =>
    change (blockEquiv hk).permCongr (Perm.sumCongr (adjSwap k j * p.1) p.2) = _
    rw [show Perm.sumCongr (adjSwap k j * p.1) p.2 = Perm.sumCongr (adjSwap k j) 1 *
        Perm.sumCongr p.1 p.2 by rw [Perm.sumCongr_mul, one_mul], Equiv.permCongr_mul, adjSwap,
      Perm.sumCongr_swap_one, Equiv.permCongr_def, Equiv.symm_trans_swap_trans]
    congr 2
  | inr j =>
    change (blockEquiv hk).permCongr (Perm.sumCongr p.1 (adjSwap (N - k) j * p.2)) = _
    rw [show Perm.sumCongr p.1 (adjSwap (N - k) j * p.2) = Perm.sumCongr 1 (adjSwap (N - k) j) *
        Perm.sumCongr p.1 p.2 by rw [Perm.sumCongr_mul, one_mul], Equiv.permCongr_mul, adjSwap,
      Perm.sumCongr_one_swap, Equiv.permCongr_def, Equiv.symm_trans_swap_trans]
    congr 2

end Block

/-- **Bisection, within-block term**, for any block size `k ≤ N`: if the path shuffles on `𝔖_k`
and `𝔖_{N-k}` satisfy log-Sobolev inequalities with constant `A`, then
`𝔼_u[Ent_u(f² ∣ S_k)] ≤ A 𝒟_{𝒯^path_N}(f)`. -/
theorem expectation_condEnt_bisectionSet_le_of_le (N k : ℕ) (hk : k ≤ N) (A : ℝ) (hA : 0 ≤ A)
    (h₁ : ∀ f : Perm (Fin k) → ℝ,
      ent (unif (Perm (Fin k))) (fun σ => f σ ^ 2) ≤ A * (pathShuffle k).dirichletForm f)
    (h₂ : ∀ f : Perm (Fin (N - k)) → ℝ,
      ent (unif (Perm (Fin (N - k)))) (fun σ => f σ ^ 2) ≤
        A * (pathShuffle (N - k)).dirichletForm f)
    (f : Perm (Fin N) → ℝ) :
    expectation (unif (Perm (Fin N)))
        (condEnt (unif (Perm (Fin N))) (bisectionSet N k) (fun σ => f σ ^ 2)) ≤
      A * (pathShuffle N).dirichletForm f := by
  set u := unif (Perm (Fin N))
  set g : Fin (N - 1) → Perm (Fin N) → ℝ := fun j σ => (f (adjSwap N j * σ) - f σ) ^ 2
  have hu : ∀ σ, 0 < u σ := fun _ => inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos)
  have hfib : ∀ σ₀, condEnt u (bisectionSet N k) (fun σ => f σ ^ 2) σ₀ ≤
      A * ((1 / 2) * ∑ e, condExp u (bisectionSet N k) (g (blockIndex hk e)) σ₀) := by
    intro σ₀
    set Ψ := fun p => blockPerm hk p * σ₀
    have hΨ : pushforward Ψ (unif _) = condMeasure u (fiber (bisectionSet N k) σ₀) := by
      rw [pushforward_unif_of_injective fun p q h => blockPerm_injective hk
        (mul_right_cancel h), fiber_bisectionSet_eq_image hk σ₀]
    change ent (condMeasure u _) _ ≤ _
    rw [← hΨ, ← ent_comp]
    refine (InvFamily.ent_sq_le_prod (pathShuffle k) (pathShuffle (N - k)) A hA h₁ h₂
      (fun p => f (Ψ p))).trans (le_of_eq ?_)
    rw [InvFamily.dirichletForm_eq]
    congr 2
    refine sum_congr rfl fun e _ => ?_
    change _ = expectation (condMeasure u _) _
    rw [← hΨ, ← expectation_comp]
    congr 1
    funext p
    simp only [Ψ, g, blockPerm_prod_T, mul_assoc]
  have htower : ∀ j, expectation u (condExp u (bisectionSet N k) (g j)) = expectation u (g j) :=
    fun j => by
      simpa only [one_mul] using
        (expectation_mul_condExp u hu (bisectionSet N k) (fun _ => 1) (g j)).symm
  have hg : ∀ j, 0 ≤ expectation u (g j) :=
    fun j => expectation_nonneg (fun σ => (hu σ).le) fun _ => sq_nonneg _
  calc expectation u (condEnt u (bisectionSet N k) (fun σ => f σ ^ 2))
      ≤ expectation u (fun σ₀ =>
          A * ((1 / 2) * ∑ e, condExp u (bisectionSet N k) (g (blockIndex hk e)) σ₀)) :=
        expectation_mono (fun σ => (hu σ).le) hfib
    _ = A * ((1 / 2) * ∑ e, expectation u (g (blockIndex hk e))) := by
        simp only [expectation_const_mul, expectation_sum, htower]
    _ ≤ A * ((1 / 2) * ∑ j, expectation u (g j)) := by
        gcongr
        rw [← sum_map univ (blockIndex hk) (fun j => expectation u (g j))]
        exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _ => hg j
    _ = A * (pathShuffle N).dirichletForm f := by
        rw [InvFamily.dirichletForm_eq]
        rfl

/-- **Bisection, within-block term.** Let `N ≥ 2` and `k = ⌊N / 2⌋`. If
`Ent_u(f²) ≤ A₁ 𝒟_{𝒯^path_k}(f)` on `𝔖_k` and `Ent_u(f²) ≤ A₂ 𝒟_{𝒯^path_{N-k}}(f)` on `𝔖_{N-k}`,
then `𝔼_u[Ent_u(f² ∣ S_k)] ≤ max(A₁, A₂) 𝒟_{𝒯^path_N}(f)` for every `f : 𝔖_N → ℝ`. -/
@[cycle_cutoff "lem_bisection_within"]
theorem expectation_condEnt_bisectionSet_le (N : ℕ) (_hN : 2 ≤ N) (A₁ A₂ : ℝ) (hA₁ : 0 ≤ A₁)
    (_hA₂ : 0 ≤ A₂)
    (h₁ : ∀ f : Equiv.Perm (Fin (N / 2)) → ℝ,
      ent (unif (Equiv.Perm (Fin (N / 2)))) (fun σ => f σ ^ 2) ≤
        A₁ * (pathShuffle (N / 2)).dirichletForm f)
    (h₂ : ∀ f : Equiv.Perm (Fin (N - N / 2)) → ℝ,
      ent (unif (Equiv.Perm (Fin (N - N / 2)))) (fun σ => f σ ^ 2) ≤
        A₂ * (pathShuffle (N - N / 2)).dirichletForm f)
    (f : Equiv.Perm (Fin N) → ℝ) :
    expectation (unif (Equiv.Perm (Fin N)))
        (condEnt (unif (Equiv.Perm (Fin N))) (bisectionSet N (N / 2)) (fun σ => f σ ^ 2)) ≤
      max A₁ A₂ * (pathShuffle N).dirichletForm f :=
  expectation_condEnt_bisectionSet_le_of_le N (N / 2) (Nat.div_le_self N 2) (max A₁ A₂)
    (le_max_of_le_left hA₁)
    (fun f => (h₁ f).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (InvFamily.dirichletForm_nonneg _ f)))
    (fun f => (h₂ f).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (InvFamily.dirichletForm_nonneg _ f)))
    f

end CycleCutoff
