/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.Defs

/-!
# Lumping of semigroups along an intertwining map

Let `Q` and `Q'` be real square matrices indexed by finite sets `Ω` and `Ω'`, and `Ψ : Ω → Ω'` a
map with `Q (f ∘ Ψ) = (Q' f) ∘ Ψ` for every `f : Ω' → ℝ`. Then the semigroups are intertwined in
the same way, `P^Q_t (f ∘ Ψ) = (P^{Q'}_t f) ∘ Ψ`, and in particular
`∑_{w ∈ Ψ⁻¹(y)} P^Q_t(z, w) = P^{Q'}_t(Ψ z, y)`.

## Main results

* `CycleCutoff.semigroup_mulVec_comp`: `P^Q_t (f ∘ Ψ) = (P^{Q'}_t f) ∘ Ψ`.
* `CycleCutoff.sum_semigroup_fiber`: `∑_{w ∈ Ψ⁻¹(y)} P^Q_t(z, w) = P^{Q'}_t(Ψ z, y)`.
-/

public section

open Finset Matrix

namespace CycleCutoff

variable {Ω Ω' : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω']

/-- If `Q (f ∘ Ψ) = (Q' f) ∘ Ψ` for every `f`, then the semigroups are intertwined in the same way:
`P^Q_t (f ∘ Ψ) = (P^{Q'}_t f) ∘ Ψ`. -/
theorem semigroup_mulVec_comp (Q : Matrix Ω Ω ℝ) (Q' : Matrix Ω' Ω' ℝ) (Ψ : Ω → Ω')
    (h : ∀ f : Ω' → ℝ, Q *ᵥ (f ∘ Ψ) = (Q' *ᵥ f) ∘ Ψ) (t : ℝ) (f : Ω' → ℝ) :
    semigroup Q t *ᵥ (f ∘ Ψ) = (semigroup Q' t *ᵥ f) ∘ Ψ := by
  let : NormedRing (Matrix Ω Ω ℝ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Matrix Ω Ω ℝ) := Matrix.linftyOpNormedAlgebra
  let : NormedRing (Matrix Ω' Ω' ℝ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Matrix Ω' Ω' ℝ) := Matrix.linftyOpNormedAlgebra
  have hpow : ∀ (n : ℕ) (g : Ω' → ℝ), (t • Q) ^ n *ᵥ (g ∘ Ψ) = ((t • Q') ^ n *ᵥ g) ∘ Ψ := by
    intro n
    induction n with
    | zero => intro g; simp
    | succ n ih =>
      intro g
      rw [pow_succ, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, h, ← Pi.smul_comp, ih,
        pow_succ, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec]
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Q)).map
    (Matrix.mulVec.addMonoidHomLeft (f ∘ Ψ)) (continuous_id.matrix_mulVec continuous_const)
  have hs' := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Q')).map
    (Matrix.mulVec.addMonoidHomLeft f) (continuous_id.matrix_mulVec continuous_const)
  funext z
  refine (Pi.hasSum.1 hs z).unique ?_
  convert Pi.hasSum.1 hs' (Ψ z) using 1
  · funext n
    simpa [Matrix.smul_mulVec] using
      congrArg (fun v => (n.factorial : ℝ)⁻¹ * v z) (hpow n f)
  · rfl

/-- **Lumping.** If `Q (f ∘ Ψ) = (Q' f) ∘ Ψ` for every `f : Ω' → ℝ`, then the semigroup of `Q`
summed over a fibre of `Ψ` is the semigroup of `Q'`:
`∑_{w ∈ Ψ⁻¹(y)} P^Q_t(z, w) = P^{Q'}_t(Ψ z, y)`. -/
@[cycle_cutoff "lem_lumping"]
theorem sum_semigroup_fiber (Q : Matrix Ω Ω ℝ) (Q' : Matrix Ω' Ω' ℝ) (Ψ : Ω → Ω')
    (h : ∀ f : Ω' → ℝ, Q *ᵥ (f ∘ Ψ) = (Q' *ᵥ f) ∘ Ψ) (t : ℝ) (z : Ω) (y : Ω') :
    ∑ w with Ψ w = y, semigroup Q t z w = semigroup Q' t (Ψ z) y := by
  have key := congrFun (semigroup_mulVec_comp Q Q' Ψ h t (Pi.single y 1)) z
  simpa [mulVec, dotProduct, Pi.single_apply, Finset.sum_filter] using key

end CycleCutoff
