/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.TwoCopy.Defs
public import CycleCutoff.Generator.DirichletFormula
public import Mathlib.Data.List.MinMax

/-!
# The multiscale decomposition

For a set `M` of edges of the cycle `ℤ/nℤ` and a cut edge `e_z`, the atoms `𝔄_{M,z}` and the level
partitions `𝒫_ℓ` of the cut cycle into intervals `I^z[a, b)`, together with the block projection
`π_B`, the block source `g_{M,B}`, the block mean `F_B`, the level increment `U_B` and the block
Dirichlet form `𝒟_B` on the two-copy state space `Ω_{n,m}`.

## Main definitions

* `CycleCutoff.IsCycleMatching`: the edges `e_x = {x, x + 1}`, `x ∈ M`, are pairwise disjoint.
* `CycleCutoff.cutInterval`: the interval `I^z[a, b) = {z + 1 + p : a ≤ p < b}`.
* `CycleCutoff.cutAtoms`: the atoms `𝔄_{M,z}`, as pairs of positions.
* `CycleCutoff.IsAtomBoundary`: no atom meets both `I^z[a, p)` and `I^z[p, b)`.
* `CycleCutoff.splitPoint`: the least atom boundary `p ∈ (a, b)` minimising `|2p - (a + b)|`.
* `CycleCutoff.splitInterval`: the split `split(I^z[a, b))` of an interval into one or two
  intervals.
* `CycleCutoff.levelPartition`: the level partitions `𝒫_0 = {I^z[0, n)}`,
  `𝒫_{ℓ+1} = ⋃_{B ∈ 𝒫_ℓ} split(B)`.
* `CycleCutoff.blockProj`: the block projection `π_B(R, X, Y) = (R ∖ B, X^B, Y^B)`.
* `CycleCutoff.blockSource`: the block source `g_{M,B}`.
* `CycleCutoff.blockMean`: the block mean `F_B`.
* `CycleCutoff.levelIncrement`: the level increment `U_B = ∑_{B' ∈ split(B)} F_{B'} - F_B`.
* `CycleCutoff.blockEdge`: the path edges `e_{y_p}`, `y_p = z + 1 + p`, of `I^z[a, b)`.
* `CycleCutoff.blockFamily`: the two-copy involution family of the block edges on `Ω_{n,m}`.
* `CycleCutoff.blockDirichlet`: the block Dirichlet form `𝒟_B`.

## Main results

* `CycleCutoff.blockDirichlet_eq`: `𝒟_B(f)` as a sum over the path edges `e_{y_p}` of the three
  moves of `𝒯_{n,m}` attached to `y_p`.

## Implementation notes

* A set of edges is a `Finset (ZMod n)` of edge start points: `x ∈ M` stands for the edge
  `e_x = {x, x + 1}`, and `e_z ∉ M` is `z ∉ M`. Being a matching is the separate hypothesis
  `IsCycleMatching n M`.
* An interval `I^z[a, b)` is carried as the pair `(a, b) : ℕ × ℕ`, and `cutInterval n z a b` is its
  set. Atoms and blocks of level partitions are such pairs: an atom is `(p, p + 2)` with
  `e_{z+1+p} ∈ M`, or `(p, p + 1)` with `z + 1 + p` not an endpoint of an edge of `M`.
* In `blockProj`, the value `none` of an auxiliary coordinate stands for `⋆`.
* The block mean `F_B` is `0` unless `|B| ≥ 2` and `X, Y ∈ B`.
-/

@[expose] public section

open Finset

namespace CycleCutoff

variable (n : ℕ)

/-! ### Matchings and intervals -/

/-- `M` is a matching of the cycle: the edges `e_x = {x, x + 1}`, `x ∈ M`, are pairwise
disjoint. -/
def IsCycleMatching (M : Finset (ZMod n)) : Prop :=
  ∀ x ∈ M, ∀ y ∈ M, x ≠ y → Disjoint ({x, x + 1} : Finset (ZMod n)) {y, y + 1}

/-- The interval `I^z[a, b) = {z + 1 + p : a ≤ p < b}` of the cycle cut at the edge `e_z`. -/
@[cycle_cutoff "def_cut_interval"]
def cutInterval (z : ZMod n) (a b : ℕ) : Finset (ZMod n) :=
  (Finset.Ico a b).image fun p : ℕ => z + 1 + (p : ZMod n)

/-- Membership in `I^z[a, b)`: a point lies in it iff it is `z + 1 + p` for some `a ≤ p < b`. -/
theorem mem_cutInterval {z : ZMod n} {a b : ℕ} {v : ZMod n} :
    v ∈ cutInterval n z a b ↔ ∃ p, a ≤ p ∧ p < b ∧ z + 1 + (p : ZMod n) = v := by
  simp [cutInterval, and_assoc]

/-- The atoms `𝔄_{M,z}`: the pairs `(p, p + 2)` with `p ≤ n - 2` and `e_{z+1+p} ∈ M`, and the
pairs `(p, p + 1)` with `p < n` and `z + 1 + p` not an endpoint of an edge of `M`. -/
@[cycle_cutoff "def_atoms"]
def cutAtoms (z : ZMod n) (M : Finset (ZMod n)) : Finset (ℕ × ℕ) :=
  ((Finset.range (n - 1)).filter fun p : ℕ => z + 1 + (p : ZMod n) ∈ M).image
      (fun p => (p, p + 2)) ∪
    ((Finset.range n).filter fun p : ℕ =>
      z + 1 + (p : ZMod n) ∉ M ∧ z + 1 + (p : ZMod n) - 1 ∉ M).image (fun p => (p, p + 1))

/-- Membership in `𝔄_{M,z}`: a pair lies in it iff it is `(p, p + 2)` with `p < n - 1` and
`z + 1 + p ∈ M`, or `(p, p + 1)` with `p < n` and neither `z + 1 + p` nor `z + 1 + p - 1` in
`M`. -/
theorem mem_cutAtoms {z : ZMod n} {M : Finset (ZMod n)} {A : ℕ × ℕ} :
    A ∈ cutAtoms n z M ↔
      (A.1 < n - 1 ∧ z + 1 + (A.1 : ZMod n) ∈ M ∧ A.2 = A.1 + 2) ∨
      (A.1 < n ∧ z + 1 + (A.1 : ZMod n) ∉ M ∧ z + 1 + (A.1 : ZMod n) - 1 ∉ M ∧
        A.2 = A.1 + 1) := by
  obtain ⟨a, b⟩ := A
  simp only [cutAtoms, mem_union, mem_image, mem_filter, mem_range, Prod.mk.injEq]
  grind

section Cut

variable {n} {z : ZMod n}

/-- The points `z + 1 + p` of the cut cycle, `p < n`, are distinct. -/
theorem eq_of_add_natCast_eq {p q : ℕ} (hp : p < n) (hq : q < n)
    (h : z + 1 + (p : ZMod n) = z + 1 + (q : ZMod n)) : p = q := by
  simpa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq]
    using add_left_cancel h

/-- `|I^z[a, b)| ≤ b - a`. -/
theorem card_cutInterval_le (z : ZMod n) (a b : ℕ) : #(cutInterval n z a b) ≤ b - a :=
  card_image_le.trans (by simp)

/-- For `b ≤ n`, the interval `I^z[a, b)` has `b - a` elements. -/
theorem card_cutInterval {a b : ℕ} (hb : b ≤ n) : #(cutInterval n z a b) = b - a := by
  rw [cutInterval, card_image_of_injOn, Nat.card_Ico]
  intro p hp q hq h
  simp only [coe_Ico, Set.mem_Ico] at hp hq
  exact eq_of_add_natCast_eq (by omega) (by omega) h

/-- Every atom ends at a position `≤ n`. -/
theorem snd_le_of_mem_cutAtoms {M : Finset (ZMod n)} {A : ℕ × ℕ} (hA : A ∈ cutAtoms n z M) :
    A.2 ≤ n := by
  rcases (mem_cutAtoms n).1 hA with ⟨h, -, h'⟩ | ⟨h, -, -, h'⟩ <;> omega

end Cut

/-! ### Level partitions -/

/-- `p` is an atom boundary of `I^z[a, b)`: no atom meets both `I^z[a, p)` and `I^z[p, b)`. -/
@[cycle_cutoff "def_level_partitions"]
def IsAtomBoundary (z : ZMod n) (M : Finset (ZMod n)) (a b p : ℕ) : Prop :=
  ¬ ∃ A ∈ cutAtoms n z M, (cutInterval n z A.1 A.2 ∩ cutInterval n z a p).Nonempty ∧
    (cutInterval n z A.1 A.2 ∩ cutInterval n z p b).Nonempty

/-- Being an atom boundary is decidable. -/
instance (z : ZMod n) (M : Finset (ZMod n)) (a b p : ℕ) :
    Decidable (IsAtomBoundary n z M a b p) := by
  unfold IsAtomBoundary
  infer_instance

/-- The split point of `I^z[a, b)`: the least atom boundary `p` with `a < p < b` minimising
`|p - (a+b)/2|` (i.e. `|2p - (a+b)|`), or `none` if there is no atom boundary in `(a, b)`.
`List.argmin` returns the first minimiser of the increasing list `a+1, …, b-1`. -/
@[cycle_cutoff "def_level_partitions"]
def splitPoint (z : ZMod n) (M : Finset (ZMod n)) (a b : ℕ) : Option ℕ :=
  ((List.range' (a + 1) (b - a - 1)).filter fun p => decide (IsAtomBoundary n z M a b p)).argmin
    fun p => Int.natAbs (2 * (p : ℤ) - (a + b))

/-- `split(I^z[a, b))`: `{(a, b)}` if `(a, b)` is an atom or has no atom boundary in `(a, b)`,
otherwise `{(a, p), (p, b)}` with `p = splitPoint n z M a b`. -/
@[cycle_cutoff "def_level_partitions"]
def splitInterval (z : ZMod n) (M : Finset (ZMod n)) (a b : ℕ) : Finset (ℕ × ℕ) :=
  if (a, b) ∈ cutAtoms n z M then {(a, b)}
  else
    match splitPoint n z M a b with
    | none => {(a, b)}
    | some p => {(a, p), (p, b)}

/-- The level partitions `𝒫_0 = {I^z[0, n)}`, `𝒫_{ℓ+1} = ⋃_{B ∈ 𝒫_ℓ} split(B)`, as sets of
pairs `(a, b)`. -/
@[cycle_cutoff "def_level_partitions"]
def levelPartition (z : ZMod n) (M : Finset (ZMod n)) : ℕ → Finset (ℕ × ℕ)
  | 0 => {(0, n)}
  | ℓ + 1 => (levelPartition z M ℓ).biUnion fun B => splitInterval n z M B.1 B.2

/-- `𝒫_0 = {I^z[0, n)}`. -/
@[simp] theorem levelPartition_zero (z : ZMod n) (M : Finset (ZMod n)) :
    levelPartition n z M 0 = {(0, n)} := rfl

/-- `𝒫_{ℓ+1} = ⋃_{B ∈ 𝒫_ℓ} split(B)`. -/
theorem levelPartition_succ (z : ZMod n) (M : Finset (ZMod n)) (ℓ : ℕ) :
    levelPartition n z M (ℓ + 1) =
      (levelPartition n z M ℓ).biUnion fun B => splitInterval n z M B.1 B.2 := rfl

/-- An atom is not split: `split(I^z[a, b)) = {(a, b)}` when `(a, b) ∈ 𝔄_{M,z}`. -/
theorem splitInterval_of_mem_cutAtoms {z : ZMod n} {M : Finset (ZMod n)} {a b : ℕ}
    (h : (a, b) ∈ cutAtoms n z M) : splitInterval n z M a b = {(a, b)} := if_pos h

/-- A non-atom block with split point `p` splits in two: `split(I^z[a, b)) = {(a, p), (p, b)}`. -/
theorem splitInterval_of_splitPoint {z : ZMod n} {M : Finset (ZMod n)} {a b p : ℕ}
    (h : (a, b) ∉ cutAtoms n z M) (hp : splitPoint n z M a b = some p) :
    splitInterval n z M a b = {(a, p), (p, b)} := by
  rw [splitInterval, if_neg h, hp]

/-- A block with no atom boundary in `(a, b)` is not split: `split(I^z[a, b)) = {(a, b)}`. -/
theorem splitInterval_of_splitPoint_eq_none {z : ZMod n} {M : Finset (ZMod n)} {a b : ℕ}
    (hp : splitPoint n z M a b = none) : splitInterval n z M a b = {(a, b)} := by
  simp [splitInterval, hp]

/-! ### Block projection, block source, block mean, level increment -/

variable {n}

/-- The block projection `π_B(R, X, Y) = (R ∖ B, X^B, Y^B)`, with `X^B = none` (`⋆`) if
`X ∈ B` and `X^B = some X` otherwise (likewise `Y^B`). -/
@[cycle_cutoff "def_block_projection"]
def blockProj {m : ℕ} (B : Finset (ZMod n)) (w : TwoCopyState (ZMod n) m) :
    Finset (ZMod n) × Option (ZMod n) × Option (ZMod n) :=
  (w.R \ B, if w.x ∈ B then none else some w.x, if w.y ∈ B then none else some w.y)

variable (n) (m : ℕ)

/-- The block source
`g_{M,B} = ∑_{e_x ∈ M, e_x ⊆ B} [1[X=Y=x](1[x+1 ∈ R] - (m-1)/(n-1))
  + 1[X=Y=x+1](1[x ∈ R] - (m-1)/(n-1))]`. -/
@[cycle_cutoff "def_block_source"]
noncomputable def blockSource (M B : Finset (ZMod n)) (w : TwoCopyState (ZMod n) m) : ℝ :=
  ∑ x ∈ M with ({x, x + 1} : Finset (ZMod n)) ⊆ B,
    ((if w.x = x ∧ w.y = x then 1 else 0) *
        ((if x + 1 ∈ w.R then 1 else 0) - ((m : ℝ) - 1) / ((n : ℝ) - 1)) +
      (if w.x = x + 1 ∧ w.y = x + 1 then 1 else 0) *
        ((if x ∈ w.R then 1 else 0) - ((m : ℝ) - 1) / ((n : ℝ) - 1)))

/-- The block mean: for `s = |B| ≥ 2`, `c_B = 2 |{e ∈ M : e ⊆ B}|`, `K_B = |R ∩ B|`,
`F_B = 1[X ∈ B, Y ∈ B] (c_B / (s K_B)) ((K_B - 1)/(s - 1) - (m-1)/(n-1))`; `F_B = 0` if
`|B| ≤ 1`. -/
@[cycle_cutoff "def_block_mean"]
noncomputable def blockMean (M B : Finset (ZMod n)) (w : TwoCopyState (ZMod n) m) : ℝ :=
  if 2 ≤ #B ∧ w.x ∈ B ∧ w.y ∈ B then
    (2 * (#(M.filter fun x => ({x, x + 1} : Finset (ZMod n)) ⊆ B) : ℝ)) /
        ((#B : ℝ) * #(w.R ∩ B)) *
      (((#(w.R ∩ B) : ℝ) - 1) / ((#B : ℝ) - 1) - ((m : ℝ) - 1) / ((n : ℝ) - 1))
  else 0

/-- The level increment `U_B = ∑_{B' ∈ split(B)} F_{B'} - F_B` for `B = I^z[a, b)`; for a
block that is split, `split(B) = {B', B''}` and this is `F_{B'} + F_{B''} - F_B`. -/
@[cycle_cutoff "def_level_increment"]
noncomputable def levelIncrement (z : ZMod n) (M : Finset (ZMod n)) (a b : ℕ)
    (w : TwoCopyState (ZMod n) m) : ℝ :=
  ∑ B' ∈ splitInterval n z M a b, blockMean n m M (cutInterval n z B'.1 B'.2) w -
    blockMean n m M (cutInterval n z a b) w

/-! ### The block Dirichlet form -/

/-- The path edges `e_{y_p} = (y_p, y_p + 1)`, `y_p = z + 1 + p`, of the block `I^z[a, b)`,
for `a ≤ p`, `p + 1 < b`, indexed by `j : Fin (b - a - 1)` with `p = a + j`. -/
def blockEdge (z : ZMod n) (a b : ℕ) (j : Fin (b - a - 1)) : ZMod n × ZMod n :=
  cycleEdge n (z + 1 + ((a + j : ℕ) : ZMod n))

/-- The two-copy family of the block edges on `Ω_{n,m}`: the maps `T^sh_{y_p}`, `T^1_{y_p}`,
`T^2_{y_p}` of `𝒯_{n,m}` for the path edges `e_{y_p} ⊆ I^z[a, b)`. -/
def blockFamily (z : ZMod n) (a b : ℕ) :
    InvFamily (TwoCopyMove (Fin (b - a - 1))) (TwoCopyState (ZMod n) m) :=
  twoCopyFamily (blockEdge n z a b) m

/-- The block Dirichlet form
`𝒟_B(f) = ½ ∑_{a ≤ p, p+1 < b} ∑_{T ∈ {T^sh_{y_p}, T^1_{y_p}, T^2_{y_p}}} 𝔼_ϖ[(f ∘ T - f)²]`,
`B = I^z[a, b)`, as the Dirichlet form of `blockFamily` (see `blockDirichlet_eq`). -/
@[cycle_cutoff "def_block_dirichlet"]
noncomputable def blockDirichlet [NeZero n] (z : ZMod n) (a b : ℕ)
    (f : TwoCopyState (ZMod n) m → ℝ) : ℝ :=
  (blockFamily n m z a b).dirichletForm f

variable {n m}

/-- The `sh j` move of the block family is `T^sh_{y_p}` of `𝒯_{n,m}` at `y_p = z + 1 + (a + j)`. -/
@[simp] theorem blockFamily_T_sh (z : ZMod n) (a b : ℕ) (j : Fin (b - a - 1)) :
    (blockFamily n m z a b).T (.sh j) =
      (twoCopy n m).T (.sh (z + 1 + ((a + j : ℕ) : ZMod n))) :=
  rfl

/-- The `one j` move of the block family is `T^1_{y_p}` of `𝒯_{n,m}` at `y_p = z + 1 + (a + j)`. -/
@[simp] theorem blockFamily_T_one (z : ZMod n) (a b : ℕ) (j : Fin (b - a - 1)) :
    (blockFamily n m z a b).T (.one j) =
      (twoCopy n m).T (.one (z + 1 + ((a + j : ℕ) : ZMod n))) :=
  rfl

/-- The `two j` move of the block family is `T^2_{y_p}` of `𝒯_{n,m}` at `y_p = z + 1 + (a + j)`. -/
@[simp] theorem blockFamily_T_two (z : ZMod n) (a b : ℕ) (j : Fin (b - a - 1)) :
    (blockFamily n m z a b).T (.two j) =
      (twoCopy n m).T (.two (z + 1 + ((a + j : ℕ) : ZMod n))) :=
  rfl

/-- The block Dirichlet form is a sum over the path edges `e_{y_p}`, `a ≤ p`, `p + 1 < b`, of the
three moves of `𝒯_{n,m}` attached to `y_p`. -/
theorem blockDirichlet_eq [NeZero n] (z : ZMod n) (a b : ℕ) (f : TwoCopyState (ZMod n) m → ℝ) :
    blockDirichlet n m z a b f =
      (1 / 2) * ∑ p ∈ (Finset.Ico a b).filter (fun p => p + 1 < b),
        ((expectation (unif _) fun w =>
            (f ((twoCopy n m).T (.sh (z + 1 + (p : ZMod n))) w) - f w) ^ 2) +
          (expectation (unif _) fun w =>
            (f ((twoCopy n m).T (.one (z + 1 + (p : ZMod n))) w) - f w) ^ 2) +
          (expectation (unif _) fun w =>
            (f ((twoCopy n m).T (.two (z + 1 + (p : ZMod n))) w) - f w) ^ 2)) := by
  rw [blockDirichlet, InvFamily.dirichletForm_eq, TwoCopyMove.sum_eq, ← sum_add_distrib,
    ← sum_add_distrib]
  congr 1
  refine Finset.sum_bij (fun j _ => a + (j : ℕ)) ?_ ?_ ?_ fun j _ => rfl
  · intro j _
    simp only [mem_filter, mem_Ico]
    omega
  · intro j₁ _ j₂ _ h
    exact Fin.ext (by simpa using h)
  · intro p hp
    simp only [mem_filter, mem_Ico] at hp
    exact ⟨⟨p - a, by omega⟩, mem_univ _, by simp only; omega⟩

end CycleCutoff
