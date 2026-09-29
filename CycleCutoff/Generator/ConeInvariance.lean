/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.LieTrotter

/-!
# Invariance of a closed convex cone under a perturbed semigroup

Let `K` be a closed convex cone in a finite-dimensional real vector space (`K + K ⊆ K` and
`[0, ∞) K ⊆ K`), and let `P`, `C` be linear operators with `P(K) ⊆ K` and `exp(s C)(K) ⊆ K` for all
`s ≥ 0`. Then `exp(t (P + C))(K) ⊆ K` for all `t ≥ 0`.

## Main results

* `CycleCutoff.pow_mulVec_mem_of_mulVec_mem`: if a matrix maps a set into itself, so does each of
  its powers.
* `CycleCutoff.exp_smul_mulVec_mem_of_cone`: if `A(K) ⊆ K` for a closed convex cone `K`, then
  `exp(s A)(K) ⊆ K` for `s ≥ 0`.
* `CycleCutoff.semigroup_mulVec_mem_of_cone`: if `P(K) ⊆ K` and `exp(s C)(K) ⊆ K` for all `s ≥ 0`,
  then `exp(t (P + C))(K) ⊆ K` for all `t ≥ 0`.

## Implementation notes

Linear operators on a finite-dimensional real space are real square matrices acting on `n → ℝ` by
`Matrix.mulVec`; the cone is an arbitrary closed subset `K` of `n → ℝ` stable under addition and
non-negative scaling. No nonemptiness assumption is needed: the zero vector lies in `K` whenever
some `x` does, as `0 • x`.

## References

* B. C. Hall, *Lie groups, Lie algebras, and representations*, 2nd ed., Theorem 2.11
-/

public section

open NormedSpace Filter Topology Matrix

namespace CycleCutoff

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- `Matrix.mulVec` is continuous in its matrix argument: if a sequence of matrices converges, so
do its actions on a fixed vector. -/
private theorem tendsto_mulVec_of_tendsto {M : ℕ → Matrix n n ℝ} {A : Matrix n n ℝ}
    (h : Tendsto M atTop (𝓝 A)) (x : n → ℝ) :
    Tendsto (fun k => M k *ᵥ x) atTop (𝓝 (A *ᵥ x)) :=
  ((continuous_id.matrix_mulVec continuous_const
    (B := fun _ : Matrix n n ℝ => x)).tendsto _).comp h

/-- If a square matrix `A` maps a set `K` into itself, so does every power `A ^ k`. -/
theorem pow_mulVec_mem_of_mulVec_mem {K : Set (n → ℝ)} {A : Matrix n n ℝ}
    (hA : ∀ x ∈ K, A *ᵥ x ∈ K) (k : ℕ) : ∀ x ∈ K, (A ^ k) *ᵥ x ∈ K := by
  induction k with
  | zero => simp
  | succ k ih =>
    intro x hx
    rw [pow_succ, ← mulVec_mulVec]
    exact ih _ (hA x hx)

/-- If a square matrix `A` maps a closed convex cone `K` into itself, then so does `exp(s A)` for
every `s ≥ 0`. -/
theorem exp_smul_mulVec_mem_of_cone {K : Set (n → ℝ)} (hK : IsClosed K)
    (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K) (hsmul : ∀ c : ℝ, 0 ≤ c → ∀ x ∈ K, c • x ∈ K)
    {A : Matrix n n ℝ} (hA : ∀ x ∈ K, A *ᵥ x ∈ K) {s : ℝ} (hs : 0 ≤ s) :
    ∀ x ∈ K, exp (s • A) *ᵥ x ∈ K := by
  intro x hx
  let _ : NormedRing (Matrix n n ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix n n ℝ) := Matrix.linftyOpNormedAlgebra
  refine hK.mem_of_tendsto (tendsto_mulVec_of_tendsto
    (exp_series_hasSum_exp' (𝕂 := ℝ) (s • A)).tendsto_sum_nat x) (.of_forall fun k => ?_)
  simp only [sum_mulVec]
  refine Finset.sum_induction _ (· ∈ K) (fun a b ha hb => hadd a ha b hb)
    (by simpa using hsmul 0 le_rfl x hx) fun j _ => ?_
  rw [smul_pow, smul_smul, smul_mulVec]
  exact hsmul _ (by positivity) _ (pow_mulVec_mem_of_mulVec_mem hA j x hx)

/-- **Cone invariance.** If `P` maps a closed convex cone `K` into itself and the semigroup of `C`
preserves `K`, then the semigroup `exp(t (P + C))` preserves `K` for every `t ≥ 0`. -/
@[cycle_cutoff "lem_cone_invariance"]
theorem semigroup_mulVec_mem_of_cone (K : Set (n → ℝ))
    (hK : IsClosed K) (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K)
    (hsmul : ∀ c : ℝ, 0 ≤ c → ∀ x ∈ K, c • x ∈ K) (P C : Matrix n n ℝ)
    (hP : ∀ x ∈ K, P *ᵥ x ∈ K)
    (hC : ∀ s : ℝ, 0 ≤ s → ∀ x ∈ K, semigroup C s *ᵥ x ∈ K) {t : ℝ} (ht : 0 ≤ t) :
    ∀ x ∈ K, semigroup (P + C) t *ᵥ x ∈ K := by
  intro x hx
  rw [semigroup, smul_add]
  refine hK.mem_of_tendsto (tendsto_mulVec_of_tendsto (tendsto_exp_mul_exp_pow (t • P) (t • C)) x)
    (.of_forall fun k => ?_)
  have hk : 0 ≤ (k : ℝ)⁻¹ * t := by positivity
  have hS : ∀ y ∈ K, (exp ((k : ℝ)⁻¹ • t • P) * exp ((k : ℝ)⁻¹ • t • C)) *ᵥ y ∈ K := by
    intro y hy
    rw [← mulVec_mulVec, smul_smul, smul_smul]
    exact exp_smul_mulVec_mem_of_cone hK hadd hsmul hP hk _ (hC _ hk y hy)
  exact pow_mulVec_mem_of_mulVec_mem hS k x hx

end CycleCutoff
