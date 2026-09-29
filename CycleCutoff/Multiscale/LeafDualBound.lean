/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Multiscale.Defs
public import CycleCutoff.Multiscale.BlockMeanCondExp
public import CycleCutoff.Multiscale.BlockDual
public import CycleCutoff.Multiscale.LevelStructure
public import CycleCutoff.Multiscale.LevelDualBound
public import CycleCutoff.Generator.DirichletFormula
public import CycleCutoff.FiniteProbability.CondExpTower
public import CycleCutoff.FiniteProbability.CondExpResidualBound
public import Mathlib.Algebra.Order.Chebyshev

/-!
# The dual bound at the leaves

Let `n ≥ 3`, `2 ≤ m ≤ n - 1`, let `M` be a set of cycle edges of `ℤ/nℤ` and `z` a point with
`e_z ∉ M`, and let `L` be a level all of whose blocks `B ∈ 𝒫_L` are atoms of `𝔄_{M,z}`. Then for
every `f : Ω_{n,m} → ℝ`, `⟨f, ∑_{B ∈ 𝒫_L} (g_{M,B} - F_B)⟩²_{ϖ_{n,m}} ≤ K (n - m)/(nm) 𝒟_{n,m}(f)`
for an absolute constant `K`.

## Main results

* `CycleCutoff.exists_innerP_sum_leaf_sq_le`: the dual bound at the leaves
  `⟨f, ∑_{B ∈ 𝒫_L} (g_{M,B} - F_B)⟩²_{ϖ_{n,m}} ≤ K (n - m)/(nm) 𝒟_{n,m}(f)`.

## Implementation notes

The paper assumes that `M` is a matching; the statement here holds for every set `M` of cycle edges
with `e_z ∉ M`.
-/

public section

open Finset

namespace CycleCutoff

section Counting

variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

omit [Fintype V] in
/-- The diagonal sum of `1[q = (v, v)] (1[v' ∈ R] - α)²` over `R ×ˢ R` splits according to
whether `R` contains `v` and `v'`. -/
private theorem sum_product_ite_diag_mul_sub_sq (α : ℝ) (v v' : V) (R : Finset V) :
    ∑ q ∈ R ×ˢ R, (if q.1 = v ∧ q.2 = v then (1 : ℝ) else 0) *
        ((if v' ∈ R then (1 : ℝ) else 0) - α) ^ 2 =
      (1 - 2 * α) * (if ({v, v'} : Finset V) ⊆ R then 1 else 0) +
        α ^ 2 * (if ({v} : Finset V) ⊆ R then 1 else 0) := by
  rw [sum_product]
  simp only [ite_and, ite_mul, one_mul, zero_mul, insert_subset_iff, singleton_subset_iff]
  by_cases h : v ∈ R <;> by_cases h' : v' ∈ R <;> simp [h, h', sub_sq]

/-- Under `ϖ` on `TwoCopyState V m`, for `v ≠ v'` and `α = (m - 1)/(|V| - 1)`,
`𝔼[1[X = Y = v] (1[v' ∈ R] - α)²] = α(1 - α)/(|V| m)`. -/
private theorem expectation_ite_diag_mul_sq_eq (hm : 2 ≤ m) (hmV : m ≤ Fintype.card V) {v v' : V}
    (hvv' : v ≠ v') :
    expectation (unif (TwoCopyState V m)) (fun w =>
        (if w.x = v ∧ w.y = v then (1 : ℝ) else 0) *
          ((if v' ∈ w.R then (1 : ℝ) else 0) -
            ((m : ℝ) - 1) / ((Fintype.card V : ℝ) - 1)) ^ 2) =
      ((m : ℝ) - 1) / ((Fintype.card V : ℝ) - 1) *
          (1 - ((m : ℝ) - 1) / ((Fintype.card V : ℝ) - 1)) /
        ((Fintype.card V : ℝ) * m) := by
  set N := Fintype.card V with hN
  set α : ℝ := ((m : ℝ) - 1) / ((N : ℝ) - 1) with hα
  have key := TwoCopyState.sum_eq_sum_product (V := V) (m := m) (fun t =>
    (if t.2.1 = v ∧ t.2.2 = v then (1 : ℝ) else 0) * ((if v' ∈ t.1 then (1 : ℝ) else 0) - α) ^ 2)
  have hcard := TwoCopyState.sum_eq_sum_product (V := V) (m := m) (fun _ => (1 : ℝ))
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at hcard
  rw [sum_congr rfl fun R hR => by rw [card_product, (mem_powersetCard.1 hR).2]] at hcard
  simp only [sum_const, card_powersetCard, card_univ, nsmul_eq_mul] at hcard
  rw [expectation_unif]
  change _ * ∑ w : TwoCopyState V m, (fun t : Finset V × V × V =>
    (if t.2.1 = v ∧ t.2.2 = v then (1 : ℝ) else 0) *
      ((if v' ∈ t.1 then (1 : ℝ) else 0) - α) ^ 2) w.1 = _
  rw [key, hcard]
  simp only [sum_product_ite_diag_mul_sub_sq, sum_add_distrib, ← mul_sum, sum_boole]
  rw [card_filter_powersetCard_subset _ _ _ (subset_univ _) (by rw [card_pair hvv']; omega),
    card_filter_powersetCard_subset _ _ _ (subset_univ _) (by rw [card_singleton]; omega),
    card_pair hvv', card_singleton, card_univ, ← hN]
  have hN2 : 2 ≤ N := by simpa [card_pair hvv'] using card_le_univ ({v, v'} : Finset V)
  rw [hα]
  obtain ⟨N', hN'⟩ : ∃ N', N = N' + 2 := ⟨N - 2, by omega⟩
  rw [hN']
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [show N' + 2 - 2 = N' from rfl, show k + 2 - 2 = k from rfl,
    show N' + 2 - 1 = N' + 1 from rfl, show k + 2 - 1 = k + 1 from rfl]
  have hc0 : ((N' + 2).choose (k + 2) : ℝ) = (N' + 2) * (N' + 1).choose (k + 1) / (k + 2) := by
    rw [eq_div_iff (by positivity)]
    exact_mod_cast (Nat.add_one_mul_choose_eq (N' + 1) (k + 1)).symm
  have hc2 : ((N').choose k : ℝ) = (N' + 1).choose (k + 1) * (k + 1) / (N' + 1) := by
    rw [eq_div_iff (by positivity), mul_comm]
    exact_mod_cast (Nat.add_one_mul_choose_eq N' k)
  have hpos : (0 : ℝ) < (N' + 1).choose (k + 1) := by
    exact_mod_cast Nat.choose_pos (by omega)
  rw [hc0, hc2]
  have h1 : ((N' + 2 : ℕ) : ℝ) - 1 = N' + 1 := by push_cast; ring
  have h2 : ((k + 2 : ℕ) : ℝ) - 1 = k + 1 := by push_cast; ring
  rw [h1, h2]
  push_cast
  field_simp
  ring

end Counting

section Blocks

variable {n : ℕ} {m : ℕ}

/-- The block source `g_{M,B}` vanishes off the event `{X ∈ B, Y ∈ B}`. -/
private theorem blockSource_eq_zero {M B : Finset (ZMod n)} {w : TwoCopyState (ZMod n) m}
    (hw : ¬(w.x ∈ B ∧ w.y ∈ B)) : blockSource n m M B w = 0 := by
  refine sum_eq_zero fun x hx => ?_
  rw [mem_filter, insert_subset_iff, singleton_subset_iff] at hx
  have h1 : ¬(w.x = x ∧ w.y = x) := fun h => hw ⟨h.1 ▸ hx.2.1, h.2 ▸ hx.2.1⟩
  have h2 : ¬(w.x = x + 1 ∧ w.y = x + 1) := fun h => hw ⟨h.1 ▸ hx.2.2, h.2 ▸ hx.2.2⟩
  simp [h1, h2]

/-- The block mean `F_B` vanishes off the event `{X ∈ B, Y ∈ B}`. -/
private theorem blockMean_eq_zero {M B : Finset (ZMod n)} {w : TwoCopyState (ZMod n) m}
    (hw : ¬(w.x ∈ B ∧ w.y ∈ B)) : blockMean n m M B w = 0 := by
  rw [blockMean, if_neg fun h => hw h.2]

variable [NeZero n]

/-- The residual `g_{M,B} - F_B` is centred given `π_B`. -/
private theorem condExp_blockSource_sub_blockMean (hn : 2 ≤ n) (M B : Finset (ZMod n)) :
    condExp (unif (TwoCopyState (ZMod n) m)) (blockProj B)
        (fun w => blockSource n m M B w - blockMean n m M B w) = fun _ => 0 := by
  rw [blockMean_eq_condExp hn]
  funext w
  change expectation _ (fun v => blockSource n m M B v -
    condExp (unif (TwoCopyState (ZMod n) m)) (blockProj B) (blockSource n m M B) v) = 0
  rw [expectation_sub]
  exact sub_eq_zero.2 (congrFun (condExp_condExp_comp _
    (unif_pos (Ω := TwoCopyState (ZMod n) m)) (blockProj B) id (blockSource n m M B)) w).symm

/-- `𝔼[(g_{M,B} - F_B)²] ≤ 𝔼[g_{M,B}²]`. -/
private theorem expectation_blockSource_sub_blockMean_sq_le (hn : 2 ≤ n) (M B : Finset (ZMod n)) :
    expectation (unif (TwoCopyState (ZMod n) m))
        (fun w => (blockSource n m M B w - blockMean n m M B w) ^ 2) ≤
      expectation (unif (TwoCopyState (ZMod n) m)) (fun w => blockSource n m M B w ^ 2) := by
  rw [blockMean_eq_condExp hn]
  exact expectation_sq_sub_condExp_le _ (unif_pos (Ω := TwoCopyState (ZMod n) m)) _ _

end Blocks

section Atoms

variable {n : ℕ} {m : ℕ}

/-- The block source of a block with fewer than two points vanishes. -/
private theorem blockSource_eq_zero_of_card_lt (hn : 2 ≤ n) {M B : Finset (ZMod n)} (hB : #B < 2)
    (w : TwoCopyState (ZMod n) m) : blockSource n m M B w = 0 := by
  have : Fact (1 < n) := ⟨hn⟩
  refine sum_eq_zero fun x hx => absurd (card_le_card (mem_filter.1 hx).2) ?_
  rw [card_pair (by simp)]
  omega

/-- The block source of the two-point block `{v, v + 1}`, `v ∈ M`. -/
private theorem blockSource_pair (hn : 3 ≤ n) {M : Finset (ZMod n)} {v : ZMod n} (hv : v ∈ M)
    (w : TwoCopyState (ZMod n) m) :
    blockSource n m M {v, v + 1} w =
      (if w.x = v ∧ w.y = v then 1 else 0) *
          ((if v + 1 ∈ w.R then 1 else 0) - ((m : ℝ) - 1) / ((n : ℝ) - 1)) +
        (if w.x = v + 1 ∧ w.y = v + 1 then 1 else 0) *
          ((if v ∈ w.R then 1 else 0) - ((m : ℝ) - 1) / ((n : ℝ) - 1)) := by
  have : Fact (1 < n) := ⟨by omega⟩
  have h2 : (2 : ZMod n) ≠ 0 := fun h => by
    have := Nat.le_of_dvd two_pos ((ZMod.natCast_eq_zero_iff 2 n).1 (by exact_mod_cast h))
    omega
  have hfilt : M.filter (fun x => ({x, x + 1} : Finset (ZMod n)) ⊆ {v, v + 1}) = {v} := by
    ext x
    simp only [mem_filter, mem_singleton, insert_subset_iff, singleton_subset_iff, mem_insert]
    refine ⟨fun ⟨_, hx, hx'⟩ => hx.resolve_right fun hv1 => ?_, ?_⟩
    · subst hv1
      rcases hx' with h | h
      · exact h2 (by linear_combination h)
      · exact one_ne_zero (by linear_combination h)
    · rintro rfl
      exact ⟨hv, Or.inl rfl, Or.inr rfl⟩
  rw [blockSource, hfilt, sum_singleton]

/-- The cut interval spanning the two positions `p`, `p + 1` is the pair
`{z + 1 + p, z + 1 + p + 1}`. -/
private theorem cutInterval_eq_pair (z : ZMod n) (p : ℕ) :
    cutInterval n z p (p + 2) = {z + 1 + (p : ZMod n), z + 1 + (p : ZMod n) + 1} := by
  rw [cutInterval, show Finset.Ico p (p + 2) = {p, p + 1} from by
    ext q; simp only [mem_Ico, mem_insert, mem_singleton]; omega,
    image_insert, image_singleton, Nat.cast_add, Nat.cast_one, ← add_assoc]

variable [NeZero n]

/-- **Second moment of the block source on an atom.** For an atom `B` of `𝔄_{M,z}`,
`𝔼[g_{M,B}²] ≤ 2α(1 - α)/(nm)`, `α = (m - 1)/(n - 1)`. -/
private theorem expectation_blockSource_sq_le_of_mem_cutAtoms (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hmn : m ≤ n) {z : ZMod n} {M : Finset (ZMod n)} {A : ℕ × ℕ} (hA : A ∈ cutAtoms n z M) :
    expectation (unif (TwoCopyState (ZMod n) m))
        (fun w => blockSource n m M (cutInterval n z A.1 A.2) w ^ 2) ≤
      2 * (((m : ℝ) - 1) / ((n : ℝ) - 1)) * (1 - ((m : ℝ) - 1) / ((n : ℝ) - 1)) /
        ((n : ℝ) * m) := by
  have : Fact (1 < n) := ⟨by omega⟩
  set α : ℝ := ((m : ℝ) - 1) / ((n : ℝ) - 1)
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hα0 : 0 ≤ α := div_nonneg (by linarith) hn1.le
  have hα1 : α ≤ 1 := (div_le_one hn1).2 (by linarith)
  rcases (mem_cutAtoms n).1 hA with ⟨-, hv, h2⟩ | ⟨-, -, -, h1⟩
  · set v := z + 1 + (A.1 : ZMod n)
    have hI : cutInterval n z A.1 A.2 = {v, v + 1} := by
      rw [h2]; exact cutInterval_eq_pair z A.1
    have hvv : v ≠ v + 1 := by simp
    have hpt : ∀ w : TwoCopyState (ZMod n) m,
        blockSource n m M (cutInterval n z A.1 A.2) w ^ 2 =
          (if w.x = v ∧ w.y = v then (1 : ℝ) else 0) *
              ((if v + 1 ∈ w.R then (1 : ℝ) else 0) - α) ^ 2 +
            (if w.x = v + 1 ∧ w.y = v + 1 then (1 : ℝ) else 0) *
              ((if v ∈ w.R then (1 : ℝ) else 0) - α) ^ 2 := by
      intro w
      rw [hI, blockSource_pair hn hv]
      by_cases h : w.x = v ∧ w.y = v
      · have h' : ¬(w.x = v + 1 ∧ w.y = v + 1) := fun h' => hvv (h.1.symm.trans h'.1)
        simp only [if_pos h, if_neg h']
        ring
      · simp only [if_neg h]
        split_ifs <;> ring
    have e1 := expectation_ite_diag_mul_sq_eq (V := ZMod n) (m := m) hm
      (by rwa [ZMod.card]) hvv
    have e2 := expectation_ite_diag_mul_sq_eq (V := ZMod n) (m := m) hm
      (by rwa [ZMod.card]) hvv.symm
    simp only [ZMod.card] at e1 e2
    rw [show (fun w => blockSource n m M (cutInterval n z A.1 A.2) w ^ 2) = _ from funext hpt,
      expectation_add, e1, e2]
    exact le_of_eq (by ring)
  · have hB : #(cutInterval n z A.1 A.2) < 2 :=
      (card_cutInterval_le z A.1 A.2).trans_lt (by omega)
    simp only [blockSource_eq_zero_of_card_lt (by omega) hB, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    rw [expectation_zero]
    have : 0 ≤ 1 - α := by linarith
    positivity

end Atoms

section Levels

variable {n : ℕ} [NeZero n] {m : ℕ} {z : ZMod n} {M : Finset (ZMod n)}

/-- Two blocks of `𝒫_ℓ` containing a common position `p` are equal. -/
private theorem eq_of_mem_levelPartition (hz : z ∉ M) {ℓ : ℕ} {B B' : ℕ × ℕ}
    (hB : B ∈ levelPartition n z M ℓ) (hB' : B' ∈ levelPartition n z M ℓ) {p q : ℕ}
    (hp : B.1 ≤ p ∧ p < B.2) (hq : B'.1 ≤ q ∧ q < B'.2)
    (h : z + 1 + (p : ZMod n) = z + 1 + (q : ZMod n)) : B = B' := by
  obtain ⟨-, huniq⟩ := levelPartition_structure (n := n) (z := z) (M := M) hz ℓ
  obtain ⟨C, -, hC⟩ := huniq (z + 1 + (p : ZMod n))
  exact (hC B ⟨hB, (mem_cutInterval n).2 ⟨p, hp.1, hp.2, rfl⟩⟩).trans
    (hC B' ⟨hB', (mem_cutInterval n).2 ⟨q, hq.1, hq.2, h.symm⟩⟩).symm

/-- The level partition `𝒫_ℓ` has at most `n` blocks. -/
private theorem card_levelPartition_le (hz : z ∉ M) (ℓ : ℕ) : #(levelPartition n z M ℓ) ≤ n := by
  obtain ⟨hstr, -⟩ := levelPartition_structure (n := n) (z := z) (M := M) hz ℓ
  calc #(levelPartition n z M ℓ) ≤ #(range n) := by
        refine card_le_card_of_injOn Prod.fst (fun B hB => ?_) (fun B hB B' hB' h => ?_)
        · have := hstr B hB
          simp only [coe_range, Set.mem_Iio]
          omega
        · exact eq_of_mem_levelPartition hz hB hB' ⟨le_rfl, (hstr B hB).1⟩
            ⟨le_rfl, (hstr B' hB').1⟩ (by rw [h])
    _ = n := card_range n

end Levels

/-- **Per-block dual bound for the residual.** There is an absolute constant `K > 0` such that
for `n ≥ 3`, `2 ≤ m ≤ n`, every atom `B` of `𝔄_{M,z}` spanning positions below `n` and every
`f`, `⟨f, g_{M,B} - F_B⟩²_{ϖ_{n,m}} ≤ K (2α(1 - α)/(nm)) 𝒟_B(f)` with `α = (m - 1)/(n - 1)`. -/
private theorem exists_innerP_blockSource_sub_blockMean_sq_le :
    ∃ K > 0, ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ m : ℕ, 2 ≤ m → m ≤ n →
      ∀ (z : ZMod n) (M : Finset (ZMod n)) (B : ℕ × ℕ), B.2 ≤ n → B ∈ cutAtoms n z M →
        ∀ f : TwoCopyState (ZMod n) m → ℝ,
          innerP (unif (TwoCopyState (ZMod n) m)) f (fun w =>
              blockSource n m M (cutInterval n z B.1 B.2) w -
                blockMean n m M (cutInterval n z B.1 B.2) w) ^ 2 ≤
            K * (2 * (((m : ℝ) - 1) / ((n : ℝ) - 1)) *
                (1 - ((m : ℝ) - 1) / ((n : ℝ) - 1)) / ((n : ℝ) * m)) *
              blockDirichlet n m z B.1 B.2 f := by
  obtain ⟨K₀, hK₀, hdual⟩ := exists_innerP_sq_le_blockDirichlet
  refine ⟨K₀ * 4, by positivity, fun n _ hn m hm hmn z M B hb hA f => ?_⟩
  set α : ℝ := ((m : ℝ) - 1) / ((n : ℝ) - 1)
  set c : ℝ := 2 * α * (1 - α) / ((n : ℝ) * m) with hc
  set U : TwoCopyState (ZMod n) m → ℝ := fun w =>
    blockSource n m M (cutInterval n z B.1 B.2) w -
      blockMean n m M (cutInterval n z B.1 B.2) w with hU
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hα0 : 0 ≤ α := div_nonneg (by linarith) hn1.le
  have hα1 : α ≤ 1 := (div_le_one hn1).2 (by linarith)
  have hc0 : 0 ≤ c := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hα0) (by linarith))
    (by positivity)
  refine (hdual n m z B.1 B.2 hb U
    (fun w hw => by
      simp only [hU, blockSource_eq_zero hw, blockMean_eq_zero hw, sub_zero])
    (condExp_blockSource_sub_blockMean (by omega) M _) f).trans ?_
  have hcard : (#(cutInterval n z B.1 B.2) : ℝ) ^ 2 ≤ 4 := by
    have h2 : #(cutInterval n z B.1 B.2) ≤ 2 := (card_cutInterval_le z B.1 B.2).trans <| by
      rcases (mem_cutAtoms n).1 hA with ⟨-, -, h⟩ | ⟨-, -, -, h⟩ <;> omega
    exact_mod_cast Nat.pow_le_pow_left h2 2
  have hE : expectation (unif (TwoCopyState (ZMod n) m)) (fun w => U w ^ 2) ≤ c :=
    (expectation_blockSource_sub_blockMean_sq_le (by omega) M _).trans
      (expectation_blockSource_sq_le_of_mem_cutAtoms hn hm hmn hA)
  have hD := (blockFamily n m z B.1 B.2).dirichletForm_nonneg f
  have hE0 : 0 ≤ expectation (unif (TwoCopyState (ZMod n) m)) (fun w => U w ^ 2) :=
    expectation_nonneg (fun w => (unif_pos w).le) fun w => sq_nonneg _
  gcongr

/-- For `3 ≤ a` and `b ≤ a`, the variance factor `β(1 - β)` with `β = (b - 1)/(a - 1)` is at
most `(3/2)(a - b)/a`. -/
private theorem div_mul_one_sub_div_le {a b : ℝ} (ha : 3 ≤ a) (hab : b ≤ a) :
    (b - 1) / (a - 1) * (1 - (b - 1) / (a - 1)) ≤ 3 / 2 * ((a - b) / a) := by
  have ha1 : (0 : ℝ) < a - 1 := by linarith
  have h1β : 1 - (b - 1) / (a - 1) = (a - b) / (a - 1) := by field_simp; ring
  have e : 3 / 2 * ((a - b) / a) - (a - b) / (a - 1) =
      (a - b) * (a - 3) / (2 * a * (a - 1)) := by field_simp; ring
  have h : 0 ≤ (a - b) * (a - 3) / (2 * a * (a - 1)) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  nlinarith [sq_nonneg (1 - (b - 1) / (a - 1))]

/-- **The dual bound at the leaves.** There is an absolute constant `K > 0` such that for
`n ≥ 3`, `2 ≤ m ≤ n - 1`, every set `M` of cycle edges and `z` with `e_z ∉ M`, every level `L`
all of whose blocks are atoms, and every `f`,
`⟨f, ∑_{B ∈ 𝒫_L} (g_{M,B} - F_B)⟩²_{ϖ_{n,m}} ≤ K (n - m)/(nm) 𝒟_{n,m}(f)`. -/
@[cycle_cutoff "lem_leaf_dual_bound"]
theorem exists_innerP_sum_leaf_sq_le :
    ∃ K > 0, ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ m : ℕ, 2 ≤ m → m < n →
      ∀ (z : ZMod n) (M : Finset (ZMod n)), z ∉ M →
        ∀ L : ℕ, (∀ B ∈ levelPartition n z M L, B ∈ cutAtoms n z M) →
        ∀ f : TwoCopyState (ZMod n) m → ℝ,
          innerP (unif (TwoCopyState (ZMod n) m)) f (fun w =>
              ∑ B ∈ levelPartition n z M L,
                (blockSource n m M (cutInterval n z B.1 B.2) w -
                  blockMean n m M (cutInterval n z B.1 B.2) w)) ^ 2 ≤
            K * (((n : ℝ) - m) / (n * m)) * (twoCopy n m).dirichletForm f := by
  obtain ⟨K₁, hK₁, hblock⟩ := exists_innerP_blockSource_sub_blockMean_sq_le
  refine ⟨3 * K₁, by positivity, fun n _ hn m hm hmn z M hz L hL f => ?_⟩
  set ν := unif (TwoCopyState (ZMod n) m)
  set P := levelPartition n z M L
  set α : ℝ := ((m : ℝ) - 1) / ((n : ℝ) - 1) with hα
  set c : ℝ := 2 * α * (1 - α) / ((n : ℝ) * m) with hc
  set U : ℕ × ℕ → TwoCopyState (ZMod n) m → ℝ := fun B w =>
    blockSource n m M (cutInterval n z B.1 B.2) w -
      blockMean n m M (cutInterval n z B.1 B.2) w
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn.le
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hα0 : 0 ≤ α := div_nonneg (by linarith) hn1.le
  have hα1 : α ≤ 1 := (div_le_one hn1).2 (by linarith)
  have hc0 : 0 ≤ c := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hα0) (by linarith))
    (by positivity)
  have hlin : innerP ν f (fun w => ∑ B ∈ P, U B w) = ∑ B ∈ P, innerP ν f (U B) := by
    simp only [innerP, expectation, mul_sum]
    exact sum_comm
  have hsum := sum_blockDirichlet_le_dirichletForm m hz (ℓ := L) (subset_refl _) f
  have hDB0 : 0 ≤ ∑ B ∈ P, blockDirichlet n m z B.1 B.2 f :=
    sum_nonneg fun B _ => (blockFamily n m z B.1 B.2).dirichletForm_nonneg f
  have hP : (#P : ℝ) ≤ n := by exact_mod_cast card_levelPartition_le hz L
  have hkey : α * (1 - α) ≤ 3 / 2 * (((n : ℝ) - m) / n) := by
    rw [hα]; exact div_mul_one_sub_div_le hn3 hmn'
  have hcoef : (n : ℝ) * (K₁ * c) ≤ 3 * K₁ * (((n : ℝ) - m) / (n * m)) := by
    calc (n : ℝ) * (K₁ * c) = 2 * K₁ * (α * (1 - α)) / m := by rw [hc]; field_simp
      _ ≤ 2 * K₁ * (3 / 2 * (((n : ℝ) - m) / n)) / m := by gcongr
      _ = 3 * K₁ * (((n : ℝ) - m) / (n * m)) := by field_simp
  rw [hlin]
  calc (∑ B ∈ P, innerP ν f (U B)) ^ 2 ≤ #P * ∑ B ∈ P, innerP ν f (U B) ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ n * ∑ B ∈ P, K₁ * c * blockDirichlet n m z B.1 B.2 f := by
        gcongr with B hB
        exact hblock n hn m hm hmn.le z M B ((levelPartition_structure hz L).1 B hB).2.1
          (hL B hB) f
    _ = n * (K₁ * c) * ∑ B ∈ P, blockDirichlet n m z B.1 B.2 f := by
        rw [← mul_sum]; ring
    _ ≤ n * (K₁ * c) * (twoCopy n m).dirichletForm f := by gcongr
    _ ≤ 3 * K₁ * (((n : ℝ) - m) / (n * m)) * (twoCopy n m).dirichletForm f :=
        mul_le_mul_of_nonneg_right hcoef (hDB0.trans hsum)

end CycleCutoff
