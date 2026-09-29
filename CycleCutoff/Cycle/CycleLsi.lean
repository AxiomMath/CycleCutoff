/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Cycle.Defs
public import CycleCutoff.PathShuffle.Defs
public import CycleCutoff.PathShuffle.Lsi
public import CycleCutoff.Generator.DirichletFormula
public import CycleCutoff.FiniteProbability.PushforwardEntropy
public import CycleCutoff.Generator.DirichletTransport
public import Mathlib.Data.ZMod.Basic

/-!
# The log-Sobolev inequality for the cycle shuffle

There is an absolute constant `c > 0` such that for all `n ≥ 3` and all `f : 𝔖_n → ℝ`,
`Ent_{π_n}(f²) ≤ c n² 𝒟_{𝒯_n}(f)`.

## Main results

* `CycleCutoff.exists_ent_sq_le_cycleShuffle_dirichletForm`: the log-Sobolev inequality
  `Ent_{π_n}(f²) ≤ c n² 𝒟_{𝒯_n}(f)`.
-/

public section

open Finset

namespace CycleCutoff

/-- Conjugating by a bijection carries a left multiplication by `swap a b` to a left
multiplication by `swap (e a) (e b)`. -/
private theorem permCongr_swap_mul {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (a b : α) (σ : Equiv.Perm α) :
    e.permCongr (Equiv.swap a b * σ) = Equiv.swap (e a) (e b) * e.permCongr σ := by
  ext x
  simp [Equiv.permCongr_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

/-- The ring isomorphism `Fin n ≃+* ℤ/nℤ` sends the successor `j + 1 < n` of `j` to
`e j + 1`. -/
private theorem finEquiv_succ (n : ℕ) [NeZero n] (j : Fin (n - 1)) :
    ZMod.finEquiv n (⟨j + 1, by omega⟩ : Fin n) = ZMod.finEquiv n ⟨j, by omega⟩ + 1 := by
  rw [← map_one (ZMod.finEquiv n), ← map_add]
  congr 1
  ext
  rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  exact (Nat.mod_eq_of_lt (by omega)).symm

/-- **Log-Sobolev inequality for the cycle shuffle.** There is an absolute constant `c > 0` such
that for all `n ≥ 3` and all `f : 𝔖_n → ℝ`, `Ent_{π_n}(f²) ≤ c n² 𝒟_{𝒯_n}(f)`. -/
@[cycle_cutoff "lem_cycle_lsi"]
theorem exists_ent_sq_le_cycleShuffle_dirichletForm :
    ∃ c > (0 : ℝ), ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ f : Equiv.Perm (ZMod n) → ℝ,
      ent (unif (Equiv.Perm (ZMod n))) (fun σ => f σ ^ 2) ≤
        c * (n : ℝ) ^ 2 * (cycleShuffle n).dirichletForm f := by
  obtain ⟨c₁, hc₁, hL⟩ := exists_ent_sq_le_pathShuffle
  refine ⟨c₁, hc₁, fun n _ _ f => ?_⟩
  set e : Fin n ≃ ZMod n := (ZMod.finEquiv n).toEquiv
  set Ψ : Equiv.Perm (Fin n) ≃ Equiv.Perm (ZMod n) := e.permCongr
  set g : Fin (n - 1) → ZMod n := fun j => e ⟨j, by omega⟩
  have hg : Function.Injective g := fun i j h => Fin.ext (Fin.mk.inj_iff.1 (e.injective h))
  let 𝒯m : InvFamily (Fin (n - 1)) (Equiv.Perm (ZMod n)) :=
    { T := fun j => (cycleShuffle n).T (g j)
      involutive := fun j => (cycleShuffle n).involutive (g j) }
  have hcomm : ∀ j σ, Ψ ((pathShuffle n).T j σ) = 𝒯m.T (Equiv.refl _ j) (Ψ σ) := by
    intro j σ
    simp only [pathShuffle_T, adjSwap, Ψ, permCongr_swap_mul, 𝒯m, cycleShuffle_T,
      Equiv.refl_apply, g]
    congr 2
    exact finEquiv_succ n j
  have hΨ := pushforward_unif_equiv Ψ
  have hD : (pathShuffle n).dirichletForm (f ∘ Ψ) = 𝒯m.dirichletForm f :=
    InvFamily.dirichletForm_comp _ _ (Equiv.refl _) Ψ hΨ hcomm f
  have hsub : 𝒯m.dirichletForm f ≤ (cycleShuffle n).dirichletForm f := by
    rw [InvFamily.dirichletForm_eq, InvFamily.dirichletForm_eq]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    set F : ZMod n → ℝ := fun x =>
      expectation (unif _) fun z => (f ((cycleShuffle n).T x z) - f z) ^ 2
    calc ∑ j, F (g j) = ∑ x ∈ univ.image g, F x := (sum_image fun i _ j _ h => hg h).symm
      _ ≤ ∑ x, F x := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ =>
        expectation_nonneg (fun _ => inv_nonneg.2 (Nat.cast_nonneg _)) fun _ => sq_nonneg _
  have hent : ent (unif (Equiv.Perm (ZMod n))) (fun σ => f σ ^ 2) =
      ent (unif (Equiv.Perm (Fin n))) (fun σ => (f ∘ Ψ) σ ^ 2) := by
    rw [← hΨ, ← ent_comp]
    rfl
  rw [hent]
  refine (hL n NeZero.one_le (f ∘ Ψ)).trans ?_
  rw [hD]
  gcongr

end CycleCutoff
