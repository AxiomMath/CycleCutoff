/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Multiscale.Defs
public import CycleCutoff.Multiscale.BlockFibrePoincare
public import CycleCutoff.FiniteProbability.CondExpPullOut
public import CycleCutoff.FiniteProbability.CondVarOnEvent

/-!
# The single-block dual bound

There is an absolute constant `K > 0` such that for every block `B = I^z[a, b)` of the cycle
`ℤ/nℤ`, every `U : Ω_{n,m} → ℝ` vanishing off the event `E = {X ∈ B, Y ∈ B}` with
`𝔼_ϖ[U ∣ π_B] = 0`, and every `f : Ω_{n,m} → ℝ`, `⟨f, U⟩²_ϖ ≤ K |B|² 𝔼_ϖ[U²] 𝒟_B(f)`.

## Main results

* `CycleCutoff.innerP_sq_le_mul_expectation_indicator_condVar`: the dual bound for a general
  conditioning map `Φ` and a `Φ`-measurable event.
* `CycleCutoff.expectation_mul_sq_le`: Cauchy–Schwarz for an expectation against a non-negative
  weight vector.
* `CycleCutoff.exists_innerP_sq_le_blockDirichlet`: the single-block dual bound
  `⟨f, U⟩²_ϖ ≤ K |B|² 𝔼_ϖ[U²] 𝒟_B(f)`.

## Implementation notes

The paper's standing hypotheses `n ≥ 3`, `1 ≤ m ≤ n` and `a < b` are not needed; only `b ≤ n` is
assumed.
-/

public section

open Finset

namespace CycleCutoff

/-- **Cauchy–Schwarz** for an expectation against non-negative weights:
`𝔼_ν[f g]² ≤ 𝔼_ν[f²] 𝔼_ν[g²]`. -/
theorem expectation_mul_sq_le {Ω : Type*} [Fintype Ω] {ν : Ω → ℝ} (hν : ∀ z, 0 ≤ ν z)
    (f g : Ω → ℝ) :
    expectation ν (fun z => f z * g z) ^ 2 ≤
      expectation ν (fun z => f z ^ 2) * expectation ν (fun z => g z ^ 2) :=
  sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun z _ => mul_nonneg (hν z) (sq_nonneg _))
    (fun z _ => mul_nonneg (hν z) (sq_nonneg _)) fun z _ => le_of_eq (by ring)

/-- **Dual bound on a `Φ`-measurable event.** If `U` vanishes off the event `E = Φ⁻¹(E_Y)` and
`𝔼_ν[U ∣ Φ] = 0`, then `⟨f, U⟩²_ν ≤ 𝔼_ν[U²] 𝔼_ν[𝟙_E Var_ν(f ∣ Φ)]`. -/
theorem innerP_sq_le_mul_expectation_indicator_condVar {Ω Y : Type*} [Fintype Ω]
    {ν : Ω → ℝ} (hν : ∀ z, 0 < ν z) (Φ : Ω → Y) (E : Set Y) {U : Ω → ℝ}
    (hU : ∀ w, Φ w ∉ E → U w = 0) (hUc : condExp ν Φ U = fun _ => 0) (f : Ω → ℝ) :
    innerP ν f U ^ 2 ≤ expectation ν (fun w => U w ^ 2) *
      expectation ν (fun w => (Φ ⁻¹' E).indicator (fun _ => (1 : ℝ)) w * condVar ν Φ f w) := by
  obtain ⟨h, hh⟩ := exists_condExp_eq_comp ν Φ f
  have horth : expectation ν (fun w => condExp ν Φ f w * U w) = 0 := by
    simp [hh, expectation_mul_condExp ν hν Φ h U, hUc]
  have hinner : innerP ν f U = expectation ν (fun w =>
      ((Φ ⁻¹' E).indicator (fun _ => (1 : ℝ)) w * (f w - condExp ν Φ f w)) * U w) := by
    have : innerP ν f U = expectation ν (fun w => f w * U w - condExp ν Φ f w * U w) := by
      rw [expectation_sub, horth, sub_zero]
      rfl
    rw [this]
    congr 1
    ext w
    by_cases hw : Φ w ∈ E
    · simp [Set.indicator, hw, sub_mul]
    · simp [Set.indicator, hw, hU w hw]
  have hsq : (fun w => ((Φ ⁻¹' E).indicator (fun _ => (1 : ℝ)) w * (f w - condExp ν Φ f w)) ^ 2)
      = fun w => (Φ ⁻¹' E).indicator (fun _ => (1 : ℝ)) w * (f w - condExp ν Φ f w) ^ 2 := by
    ext w
    by_cases hw : Φ w ∈ E <;> simp [Set.indicator, hw]
  have hCS := expectation_mul_sq_le (fun w => (hν w).le)
    (fun w => (Φ ⁻¹' E).indicator (fun _ => (1 : ℝ)) w * (f w - condExp ν Φ f w)) U
  rw [← hinner, hsq, expectation_indicator_sq_sub_condExp ν hν Φ E f] at hCS
  linarith

/-- **Single-block dual bound.** There is an absolute constant `K > 0` such that for a block
`B = I^z[a, b)` with `b ≤ n`, a function `U` vanishing off `{X, Y ∈ B}` with `𝔼[U ∣ π_B] = 0`, and
any `f`, `⟨f, U⟩² ≤ K |B|² 𝔼[U²] 𝒟_B(f)`. -/
@[cycle_cutoff "lem_block_dual"]
theorem exists_innerP_sq_le_blockDirichlet :
    ∃ K > 0, ∀ (n : ℕ) [NeZero n] (m : ℕ) (z : ZMod n) (a b : ℕ), b ≤ n →
      ∀ U : TwoCopyState (ZMod n) m → ℝ,
        (∀ w, ¬(w.x ∈ cutInterval n z a b ∧ w.y ∈ cutInterval n z a b) → U w = 0) →
        condExp (unif (TwoCopyState (ZMod n) m)) (blockProj (cutInterval n z a b)) U =
          (fun _ => 0) →
        ∀ f : TwoCopyState (ZMod n) m → ℝ,
          innerP (unif (TwoCopyState (ZMod n) m)) f U ^ 2 ≤
            K * (#(cutInterval n z a b) : ℝ) ^ 2 *
              expectation (unif (TwoCopyState (ZMod n) m)) (fun w => U w ^ 2) *
                blockDirichlet n m z a b f := by
  obtain ⟨K, hK, hP⟩ := exists_expectation_indicator_condVar_le_blockDirichlet
  refine ⟨K, hK, fun n _ m z a b hb U hU hUc f => ?_⟩
  have hν : ∀ w, 0 < unif (TwoCopyState (ZMod n) m) w := unif_pos
  have hE : ∀ w : TwoCopyState (ZMod n) m,
      blockProj (cutInterval n z a b) w ∈ {y | y.2.1 = none ∧ y.2.2 = none} ↔
        w.x ∈ cutInterval n z a b ∧ w.y ∈ cutInterval n z a b := fun w => by
    simp [blockProj]
  have key := innerP_sq_le_mul_expectation_indicator_condVar hν (blockProj (cutInterval n z a b))
    {y | y.2.1 = none ∧ y.2.2 = none} (fun w hw => hU w ((hE w).not.1 hw)) hUc f
  have hind : ∀ w : TwoCopyState (ZMod n) m,
      (blockProj (cutInterval n z a b) ⁻¹' {y | y.2.1 = none ∧ y.2.2 = none}).indicator
        (fun _ => (1 : ℝ)) w =
      if w.x ∈ cutInterval n z a b ∧ w.y ∈ cutInterval n z a b then 1 else 0 := fun w => by
    by_cases h : w.x ∈ cutInterval n z a b ∧ w.y ∈ cutInterval n z a b <;>
      simp only [Set.indicator, Set.mem_preimage, hE, h, if_false]
  simp only [hind] at key
  exact (key.trans (mul_le_mul_of_nonneg_left (hP n m z a b hb f)
    (expectation_nonneg (fun w => (hν w).le) fun w => sq_nonneg _))).trans_eq (by ring)

end CycleCutoff
