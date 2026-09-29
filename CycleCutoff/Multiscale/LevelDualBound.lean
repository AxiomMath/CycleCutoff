/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Multiscale.Defs
public import CycleCutoff.Multiscale.IncrementCentered
public import CycleCutoff.Multiscale.BlockDual
public import CycleCutoff.Multiscale.LevelStructure
public import CycleCutoff.Multiscale.SplitBalance
public import CycleCutoff.Generator.DirichletFormula
public import CycleCutoff.Multiscale.IncrementSecondMoment

/-!
# The dual bound for one level

There is an absolute constant `K > 0` such that for all `n ≥ 3`, `2 ≤ m ≤ n - 1`, every matching
`M` of the cycle `ℤ/nℤ`, every `z` with `e_z ∉ M`, every level `ℓ` and every `f : Ω_{n,m} → ℝ`,
`⟨f, ∑_{B ∈ 𝒫_ℓ ∖ 𝔄_{M,z}} U_B⟩²_ϖ ≤ K (n - m) / (n m) 𝒟_{n,m}(f)`.

## Main results

* `CycleCutoff.pairwiseDisjoint_cutInterval_levelPartition`: the blocks of a level partition have
  pairwise disjoint sets.
* `CycleCutoff.sum_blockDirichlet_le_dirichletForm`: the block Dirichlet forms of a family of
  blocks of one level partition add up to at most the Dirichlet form of `𝒯_{n,m}`.
* `CycleCutoff.exists_innerP_sum_levelIncrement_sq_le`: the dual bound for one level
  `⟨f, ∑_{B ∈ 𝒫_ℓ ∖ 𝔄_{M,z}} U_B⟩²_ϖ ≤ K (n - m) / (n m) 𝒟_{n,m}(f)`.
-/

public section

open Finset

namespace CycleCutoff

variable {n : ℕ} {z : ZMod n} {M : Finset (ZMod n)}

/-- The sets `I^z[a, b)` of the blocks `(a, b)` of a level partition are pairwise disjoint. -/
theorem pairwiseDisjoint_cutInterval_levelPartition [NeZero n] (hz : z ∉ M) (ℓ : ℕ) :
    (levelPartition n z M ℓ : Set (ℕ × ℕ)).PairwiseDisjoint
      fun B => cutInterval n z B.1 B.2 := by
  intro B hB B' hB' hne
  refine disjoint_left.2 fun v hv hv' => hne ?_
  exact ((levelPartition_structure hz ℓ).2 v).unique ⟨hB, hv⟩ ⟨hB', hv'⟩

/-- For `b ≤ n`, a sum over `I^z[a, b)` is the sum over the positions `a ≤ p < b`. -/
theorem sum_cutInterval {β : Type*} [AddCommMonoid β] {a b : ℕ} (hb : b ≤ n)
    (g : ZMod n → β) :
    ∑ x ∈ cutInterval n z a b, g x = ∑ p ∈ Ico a b, g (z + 1 + (p : ZMod n)) := by
  rw [cutInterval, sum_image]
  intro p hp q hq h
  simp only [coe_Ico, Set.mem_Ico] at hp hq
  exact eq_of_add_natCast_eq (by omega) (by omega) h

/-- The block Dirichlet forms of a family `P` of blocks of one level partition add up to at most
the Dirichlet form of `𝒯_{n,m}`. -/
theorem sum_blockDirichlet_le_dirichletForm [NeZero n] (m : ℕ) (hz : z ∉ M) {ℓ : ℕ}
    {P : Finset (ℕ × ℕ)} (hP : P ⊆ levelPartition n z M ℓ)
    (f : TwoCopyState (ZMod n) m → ℝ) :
    ∑ B ∈ P, blockDirichlet n m z B.1 B.2 f ≤ (twoCopy n m).dirichletForm f := by
  set g : ZMod n → ℝ := fun x =>
    (expectation (unif _) fun w => (f ((twoCopy n m).T (.sh x) w) - f w) ^ 2) +
      (expectation (unif _) fun w => (f ((twoCopy n m).T (.one x) w) - f w) ^ 2) +
      (expectation (unif _) fun w => (f ((twoCopy n m).T (.two x) w) - f w) ^ 2)
  have hν : ∀ w, 0 ≤ unif (TwoCopyState (ZMod n) m) w := fun w => (unif_pos w).le
  have hg0 : ∀ x, 0 ≤ g x := fun x => by
    simp only [g]
    refine add_nonneg (add_nonneg ?_ ?_) ?_ <;>
      exact expectation_nonneg hν fun w => sq_nonneg _
  have hD : (twoCopy n m).dirichletForm f = (1 / 2) * ∑ x, g x := by
    rw [InvFamily.dirichletForm_eq, TwoCopyMove.sum_eq, ← sum_add_distrib, ← sum_add_distrib]
  have hB : ∀ B ∈ P, blockDirichlet n m z B.1 B.2 f ≤
      (1 / 2) * ∑ x ∈ cutInterval n z B.1 B.2, g x := by
    intro B hBP
    have hbn := ((levelPartition_structure hz ℓ).1 B (hP hBP)).2.1
    rw [blockDirichlet_eq, sum_cutInterval hbn]
    gcongr
    · exact fun p _ _ => hg0 _
    · exact filter_subset _ _
  have hdisj : (P : Set (ℕ × ℕ)).PairwiseDisjoint fun B => cutInterval n z B.1 B.2 :=
    (pairwiseDisjoint_cutInterval_levelPartition hz ℓ).subset (coe_subset.2 hP)
  calc ∑ B ∈ P, blockDirichlet n m z B.1 B.2 f
      ≤ ∑ B ∈ P, (1 / 2) * ∑ x ∈ cutInterval n z B.1 B.2, g x := sum_le_sum hB
    _ = (1 / 2) * ∑ x ∈ P.biUnion fun B => cutInterval n z B.1 B.2, g x := by
        rw [sum_biUnion hdisj, mul_sum]
    _ ≤ (1 / 2) * ∑ x, g x := by
        gcongr
        · exact fun x _ _ => hg0 x
        · exact subset_univ _
    _ = _ := hD.symm

/-- **Dual bound for one level.** There is an absolute constant `K > 0` such that for `n ≥ 3`,
`2 ≤ m < n`, a matching `M` with `e_z ∉ M` and the increments of the non-atom blocks of the level
partition `𝒫_ℓ`, `⟨f, ∑_{B ∈ 𝒫_ℓ ∖ 𝔄_{M,z}} U_B⟩² ≤ K (n - m) / (n m) 𝒟_{n,m}(f)`. -/
@[cycle_cutoff "lem_level_dual_bound"]
theorem exists_innerP_sum_levelIncrement_sq_le :
    ∃ K > 0, ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ m : ℕ, 2 ≤ m → m < n →
      ∀ (z : ZMod n) (M : Finset (ZMod n)), IsCycleMatching n M → z ∉ M →
        ∀ (ℓ : ℕ) (f : TwoCopyState (ZMod n) m → ℝ),
          innerP (unif (TwoCopyState (ZMod n) m)) f (fun w =>
              ∑ B ∈ levelPartition n z M ℓ \ cutAtoms n z M, levelIncrement n m z M B.1 B.2 w) ^ 2 ≤
            K * (((n : ℝ) - m) / (n * m)) * (twoCopy n m).dirichletForm f := by
  obtain ⟨K, hK, hdual⟩ := exists_innerP_sq_le_blockDirichlet
  refine ⟨64 * K, by positivity, fun n _ hn m hm₂ hmn z M hM hz ℓ f => ?_⟩
  set P := levelPartition n z M ℓ \ cutAtoms n z M
  set ν := unif (TwoCopyState (ZMod n) m)
  have hν : ∀ w, 0 ≤ ν w := fun w => (unif_pos w).le
  have hPsub : P ⊆ levelPartition n z M ℓ := sdiff_subset
  set c : ℕ × ℕ → ℝ := fun B => (#(cutInterval n z B.1 B.2) : ℝ)
  set E : ℕ × ℕ → ℝ := fun B =>
    expectation ν (fun w => levelIncrement n m z M B.1 B.2 w ^ 2)
  set D : ℕ × ℕ → ℝ := fun B => blockDirichlet n m z B.1 B.2 f
  have hlin : innerP ν f (fun w => ∑ B ∈ P, levelIncrement n m z M B.1 B.2 w) =
      ∑ B ∈ P, innerP ν f (levelIncrement n m z M B.1 B.2) := by
    simp only [innerP, expectation, mul_sum]
    exact sum_comm
  have hblock : ∀ B ∈ P, innerP ν f (levelIncrement n m z M B.1 B.2) ^ 2 ≤
      (K * c B ^ 2 * E B) * D B := by
    intro B hBP
    obtain ⟨hB, hBA⟩ := mem_sdiff.1 hBP
    have hbn := ((levelPartition_structure hz ℓ).1 B hB).2.1
    obtain ⟨p, hap, hpb, hsplit, -, -⟩ := splitInterval_balanced hM hz hB hBA
    have hvan : ∀ w : TwoCopyState (ZMod n) m,
        ¬(w.x ∈ cutInterval n z B.1 B.2 ∧ w.y ∈ cutInterval n z B.1 B.2) →
          levelIncrement n m z M B.1 B.2 w = 0 := by
      intro w hw
      have h0 : ∀ C : Finset (ZMod n), C ⊆ cutInterval n z B.1 B.2 →
          blockMean n m M C w = 0 := fun C hC =>
        if_neg fun h => hw ⟨hC h.2.1, hC h.2.2⟩
      have hsub : ∀ {a b : ℕ}, B.1 ≤ a → b ≤ B.2 →
          cutInterval n z a b ⊆ cutInterval n z B.1 B.2 := fun ha hb =>
        image_subset_image (Ico_subset_Ico ha hb)
      rw [levelIncrement, hsplit, sum_pair (by simp only [ne_eq, Prod.mk.injEq]; omega),
        h0 _ (hsub le_rfl hpb.le), h0 _ (hsub hap.le le_rfl), h0 _ subset_rfl]
      ring
    exact (hdual n m z B.1 B.2 hbn _ hvan (condExp_levelIncrement_eq_zero hM hz hB hBA)
      f).trans_eq (by simp only [c, E, D, ν])
  have hD0 : ∀ B, 0 ≤ D B := fun B => by
    simp only [D, blockDirichlet_eq]
    refine mul_nonneg (by norm_num) (sum_nonneg fun p _ => ?_)
    refine add_nonneg (add_nonneg ?_ ?_) ?_ <;>
      exact expectation_nonneg hν fun w => sq_nonneg _
  have hE0 : ∀ B, 0 ≤ E B := fun B => expectation_nonneg hν fun w => sq_nonneg _
  have hbd0 : ∀ B ∈ P, 0 ≤ K * c B ^ 2 * E B :=
    fun B _ => mul_nonneg (mul_nonneg hK.le (sq_nonneg _)) (hE0 B)
  have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul (s := P)
    (r := fun B => innerP ν f (levelIncrement n m z M B.1 B.2))
    (f := fun B => K * c B ^ 2 * E B) (g := D) hbd0 (fun B _ => hD0 B) hblock
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  have hρ : 0 ≤ 1 - (m : ℝ) / n := sub_nonneg.2 ((div_le_one hn0).2 (by exact_mod_cast hmn.le))
  set γ := 64 * ((m : ℝ) / n) * (1 - (m : ℝ) / n) / (m : ℝ) ^ 2
  have hγ0 : 0 ≤ γ := by positivity
  have hcard : ∑ B ∈ P, c B ≤ n := by
    have hdisj : (P : Set (ℕ × ℕ)).PairwiseDisjoint fun B => cutInterval n z B.1 B.2 :=
      (pairwiseDisjoint_cutInterval_levelPartition hz ℓ).subset (coe_subset.2 hPsub)
    simp only [c]
    rw [← Nat.cast_sum, ← card_biUnion hdisj]
    exact_mod_cast (card_le_univ _).trans_eq (ZMod.card n)
  have hsum : ∑ B ∈ P, K * c B ^ 2 * E B ≤ 64 * K * (((n : ℝ) - m) / (n * m)) := by
    calc ∑ B ∈ P, K * c B ^ 2 * E B ≤ ∑ B ∈ P, K * γ * c B := by
          refine sum_le_sum fun B hBP => ?_
          obtain ⟨hB, hBA⟩ := mem_sdiff.1 hBP
          have hlt := ((levelPartition_structure hz ℓ).1 B hB).1
          have hc0 : 0 < c B := by
            simp only [c]
            exact_mod_cast card_pos.2
              ⟨_, (mem_cutInterval n).2 ⟨B.1, le_rfl, hlt, rfl⟩⟩
          have h2 := expectation_levelIncrement_sq_le hn (by omega) hmn.le hM hz hB hBA
          have h2' : E B ≤ γ / c B := by
            simp only [E, γ, c]
            rw [div_div]
            convert h2 using 2
          calc K * c B ^ 2 * E B ≤ K * c B ^ 2 * (γ / c B) := by gcongr
            _ = K * γ * c B := by field_simp
      _ = K * γ * ∑ B ∈ P, c B := by rw [mul_sum]
      _ ≤ K * γ * n := by gcongr
      _ = 64 * K * (((n : ℝ) - m) / (n * m)) := by
          simp only [γ]; field_simp
  rw [hlin]
  calc (∑ B ∈ P, innerP ν f (levelIncrement n m z M B.1 B.2)) ^ 2
      ≤ (∑ B ∈ P, K * c B ^ 2 * E B) * ∑ B ∈ P, D B := hcs
    _ ≤ (64 * K * (((n : ℝ) - m) / (n * m))) * (twoCopy n m).dirichletForm f :=
        mul_le_mul hsum (sum_blockDirichlet_le_dirichletForm m hz hPsub f)
          (sum_nonneg fun B _ => hD0 B) ((sum_nonneg hbd0).trans hsum)

end CycleCutoff
