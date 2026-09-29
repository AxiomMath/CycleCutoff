/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Multiscale.Defs
public import CycleCutoff.Multiscale.IncrementCentered
public import CycleCutoff.Multiscale.BlockSecondMoment
public import CycleCutoff.Multiscale.SplitBalance
public import CycleCutoff.Multiscale.BlockMeanCondExp
public import CycleCutoff.Multiscale.LevelStructure
public import CycleCutoff.FiniteProbability.CondExpTower
public import CycleCutoff.FiniteProbability.CondExpResidualBound

/-!
# Second moment of a level increment

Let `n ≥ 3`, `1 ≤ m ≤ n`, let `M` be a matching of the cycle `ℤ/nℤ` and `z` a point with `e_z ∉ M`.
If a block `B` of the level partition `𝒫_ℓ` is not an atom, then under the uniform measure
`ϖ_{n,m}` its level increment satisfies `𝔼[U_B²] ≤ 64 (m/n) (1 - m/n) / (m² |B|)`.

## Main results

* `CycleCutoff.expectation_levelIncrement_sq_le`:
  `𝔼_{ϖ_{n,m}}[U_B²] ≤ 64 (m/n) (1 - m/n) / (m² |B|)` for a non-atom block `B ∈ 𝒫_ℓ`.
-/

public section

open Finset

namespace CycleCutoff

variable {n : ℕ} [NeZero n] {m : ℕ} {z : ZMod n} {M : Finset (ZMod n)}

/-- Adding a `Φ`-measurable function to a `Φ`-centred one only increases the second moment. -/
theorem expectation_sq_le_expectation_add_sq {Ω Y : Type*} [Fintype Ω] (ν : Ω → ℝ)
    (hν : ∀ z, 0 < ν z) (Φ : Ω → Y) (f g : Ω → ℝ) (hf : condExp ν Φ f = fun _ => 0)
    (hg : condExp ν Φ g = g) :
    expectation ν (fun z => f z ^ 2) ≤ expectation ν (fun z => (f z + g z) ^ 2) := by
  have h := expectation_sq_sub_condExp_le ν hν Φ (fun z => f z + g z)
  rw [condExp_add, hf, hg] at h
  simpa using h

/-- The block mean is a function of the block projection: `𝔼_{ϖ_{n,m}}[F_B ∣ π_B] = F_B`. -/
theorem condExp_blockMean (hn : 2 ≤ n) (M B : Finset (ZMod n)) :
    condExp (unif (TwoCopyState (ZMod n) m)) (blockProj B) (blockMean n m M B) =
      blockMean n m M B := by
  rw [blockMean_eq_condExp (m := m) hn M B]
  exact condExp_condExp_comp _ unif_pos (blockProj B) id _

/-- The halves `I^z[a, p)` and `I^z[p, b)` of a split block of a level partition are disjoint. -/
theorem disjoint_cutInterval_of_splitInterval (hz : z ∉ M) {ℓ a b p : ℕ} (hap : a < p)
    (hB : (a, b) ∈ levelPartition n z M ℓ)
    (hsplit : splitInterval n z M a b = {(a, p), (p, b)}) :
    Disjoint (cutInterval n z a p) (cutInterval n z p b) := by
  have hmem : ∀ C ∈ ({(a, p), (p, b)} : Finset (ℕ × ℕ)), C ∈ levelPartition n z M (ℓ + 1) :=
    fun C hC => by
      rw [levelPartition_succ]
      exact mem_biUnion.2 ⟨(a, b), hB, hsplit ▸ hC⟩
  refine disjoint_left.2 fun v hv₁ hv₂ => ?_
  have h := ((levelPartition_structure hz (ℓ + 1)).2 v).unique
    ⟨hmem (a, p) (by simp), hv₁⟩ ⟨hmem (p, b) (by simp), hv₂⟩
  simp only [Prod.mk.injEq] at h
  omega

/-- For disjoint blocks `B₁`, `B₂`, `𝔼[(F_{B₁} + F_{B₂})²] = 𝔼[F_{B₁}²] + 𝔼[F_{B₂}²]`. -/
theorem expectation_blockMean_add_sq_of_disjoint {I₁ I₂ : Finset (ZMod n)}
    (hdisj : Disjoint I₁ I₂) (M : Finset (ZMod n)) :
    expectation (unif (TwoCopyState (ZMod n) m))
        (fun w => (blockMean n m M I₁ w + blockMean n m M I₂ w) ^ 2) =
      expectation (unif (TwoCopyState (ZMod n) m)) (fun w => blockMean n m M I₁ w ^ 2) +
        expectation (unif (TwoCopyState (ZMod n) m)) (fun w => blockMean n m M I₂ w ^ 2) := by
  have h : ∀ w : TwoCopyState (ZMod n) m, blockMean n m M I₁ w * blockMean n m M I₂ w = 0 :=
    fun w => by
      by_cases hx : w.x ∈ I₁
      · simp [blockMean, disjoint_left.1 hdisj hx]
      · simp [blockMean, hx]
  rw [← expectation_add]
  congr 1
  funext w
  linear_combination 2 * h w

private theorem div_add_div_le_of_le_four_mul {a s K k₁ k₂ : ℝ} (ha : 0 ≤ a) (hs : 0 < s)
    (hK : 0 < K) (h₁ : K ≤ 4 * k₁) (h₂ : K ≤ 4 * k₂) :
    a / (s * k₁) + a / (s * k₂) ≤ 8 * a / (s * K) := by
  have key : ∀ {k : ℝ}, K ≤ 4 * k → a / (s * k) ≤ 4 * a / (s * K) := fun {k} hk => by
    have hk0 : 0 < k := by linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg ha hs.le]
  have e : 8 * a / (s * K) = 4 * a / (s * K) + 4 * a / (s * K) := by ring
  linarith [key h₁, key h₂]

/-- **Second moment of an increment.** For a block `B ∈ 𝒫_ℓ` that is not an atom,
`𝔼_{ϖ_{n,m}}[U_B²] ≤ 64 (m/n) (1 - m/n) / (m² |B|)`. -/
@[cycle_cutoff "lem_increment_second_moment"]
theorem expectation_levelIncrement_sq_le (hn : 3 ≤ n) (hm₁ : 1 ≤ m) (hm : m ≤ n)
    (hM : IsCycleMatching n M) (hz : z ∉ M) {ℓ : ℕ} {B : ℕ × ℕ}
    (hB : B ∈ levelPartition n z M ℓ) (hBA : B ∉ cutAtoms n z M) :
    expectation (unif (TwoCopyState (ZMod n) m)) (fun w => levelIncrement n m z M B.1 B.2 w ^ 2) ≤
      64 * ((m : ℝ) / n) * (1 - (m : ℝ) / n) / ((m : ℝ) ^ 2 * #(cutInterval n z B.1 B.2)) := by
  have hcent := condExp_levelIncrement_eq_zero (m := m) hM hz hB hBA
  obtain ⟨a, b⟩ := B
  obtain ⟨p, hap, hpb, hsplit, hc₁, hc₂⟩ := splitInterval_balanced hM hz hB hBA
  dsimp only at hap hpb hsplit hc₁ hc₂ hcent ⊢
  have hdisj := disjoint_cutInterval_of_splitInterval hz hap hB hsplit
  set ν := unif (TwoCopyState (ZMod n) m)
  set I := cutInterval n z a b
  set I₁ := cutInterval n z a p
  set I₂ := cutInterval n z p b
  set F := blockMean n m M I
  set W : TwoCopyState (ZMod n) m → ℝ := fun w => blockMean n m M I₁ w + blockMean n m M I₂ w
  have hU : levelIncrement n m z M a b = fun w => W w - F w := by
    funext w
    rw [levelIncrement, hsplit, sum_pair (by simp only [ne_eq, Prod.mk.injEq]; omega)]
  have hWU : W = fun w => levelIncrement n m z M a b w + F w := by
    funext w
    rw [hU]
    ring
  have hres : expectation ν (fun w => levelIncrement n m z M a b w ^ 2) ≤
      expectation ν (fun w => W w ^ 2) := by
    rw [hWU]
    exact expectation_sq_le_expectation_add_sq ν unif_pos (blockProj I) _ F hcent
      (condExp_blockMean (by omega) M I)
  have hne : ∀ {c d : ℕ}, c < d → (cutInterval n z c d).Nonempty := fun {c d} hcd =>
    ⟨_, (mem_cutInterval n).2 ⟨c, le_rfl, hcd, rfl⟩⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm₁
  have hρ : 0 ≤ 1 - (m : ℝ) / n := sub_nonneg.2 ((div_le_one hn0).2 (by exact_mod_cast hm))
  calc expectation ν (fun w => levelIncrement n m z M a b w ^ 2)
      ≤ expectation ν (fun w => blockMean n m M I₁ w ^ 2) +
          expectation ν (fun w => blockMean n m M I₂ w ^ 2) :=
        hres.trans (expectation_blockMean_add_sq_of_disjoint hdisj M).le
    _ ≤ 8 * ((m : ℝ) / n) * (1 - (m : ℝ) / n) / ((m : ℝ) ^ 2 * #I₁) +
          8 * ((m : ℝ) / n) * (1 - (m : ℝ) / n) / ((m : ℝ) ^ 2 * #I₂) :=
        add_le_add (expectation_blockMean_sq_le hn hm₁ hm hM (hne hap))
          (expectation_blockMean_sq_le hn hm₁ hm hM (hne hpb))
    _ ≤ 8 * (8 * ((m : ℝ) / n) * (1 - (m : ℝ) / n)) / ((m : ℝ) ^ 2 * #I) :=
        div_add_div_le_of_le_four_mul (by positivity) (by positivity)
          (by exact_mod_cast (hne (hap.trans hpb)).card_pos)
          (by exact_mod_cast hc₁) (by exact_mod_cast hc₂)
    _ = 64 * ((m : ℝ) / n) * (1 - (m : ℝ) / n) / ((m : ℝ) ^ 2 * #I) := by ring

end CycleCutoff
