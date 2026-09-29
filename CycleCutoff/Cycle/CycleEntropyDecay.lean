/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Cycle.Defs
public import CycleCutoff.Cycle.CycleLsi
public import CycleCutoff.Generator.LsiEntropyDecay
public import CycleCutoff.Cycle.LambdaUpper

/-!
# Entropy decay for the cycle shuffle

There is an absolute constant `c₅ > 0` such that for all `n ≥ 3`, every probability vector `α`
on `Sₙ` with positive entries and every `t ≥ 0`, `H(α P_t ∣ π_n) ≤ e^{-c₅ λ_n t} H(α ∣ π_n)`,
where `P_t` is the semigroup of the cycle shuffle.

## Main results

* `CycleCutoff.exists_relEnt_cycleShuffle_semigroup_le`: entropy decay for the cycle shuffle at
  rate `c₅ λ_n`.
-/

public section

open Finset Matrix Real

namespace CycleCutoff

/-- **Entropy decay for the cycle shuffle.** There is an absolute constant `c₅ > 0` such that
for all `n ≥ 3`, every positive probability vector `α` on `Sₙ` and every `t ≥ 0`,
`H(α P_t ∣ π_n) ≤ e^{-c₅ λ_n t} H(α ∣ π_n)`. -/
@[cycle_cutoff "lem_cycle_entropy_decay"]
theorem exists_relEnt_cycleShuffle_semigroup_le :
    ∃ c₅ > (0 : ℝ), ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ α : Equiv.Perm (ZMod n) → ℝ,
      IsProbVec α → (∀ σ, 0 < α σ) → ∀ t : ℝ, 0 ≤ t →
        relEnt (α ᵥ* (cycleShuffle n).semigroup t) (unif (Equiv.Perm (ZMod n))) ≤
          Real.exp (-c₅ * lambdaN n * t) * relEnt α (unif (Equiv.Perm (ZMod n))) := by
  obtain ⟨c, hc, hLSI⟩ := exists_ent_sq_le_cycleShuffle_dirichletForm
  refine ⟨1 / (c * π ^ 2), by positivity, fun n _ hn α hα hαpos t ht => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hA : 0 < c * (n : ℝ) ^ 2 := by positivity
  have hdecay := (cycleShuffle n).relEnt_semigroup_le_of_lsi (c * (n : ℝ) ^ 2) hA
    (fun f => by simpa [mul_assoc] using hLSI n hn f) α hα hαpos ht
  refine hdecay.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_)
    (relEnt_nonneg hα isProbVec_unif fun _ => by rw [unif_apply]; positivity))
  have hrate : 1 / (c * π ^ 2) * lambdaN n ≤ 4 / (c * (n : ℝ) ^ 2) :=
    (mul_le_mul_of_nonneg_left (lambdaN_le_four_pi_sq_div_sq n) (by positivity)).trans_eq
      (by field_simp)
  calc -4 * t / (c * (n : ℝ) ^ 2) = -(4 / (c * (n : ℝ) ^ 2) * t) := by ring
    _ ≤ _ := by linarith [mul_le_mul_of_nonneg_right hrate ht]

end CycleCutoff
