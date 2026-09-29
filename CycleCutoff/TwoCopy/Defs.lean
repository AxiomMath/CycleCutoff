/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Cycle.Defs
public import CycleCutoff.OneCard.Defs
public import CycleCutoff.Exposure.Defs
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.CardEmbedding

/-!
# The two-copy process and the black-labelled chains

For a vertex type `V` and edges `edge : ι → V × V`, the two-copy state space `TwoCopyState V m`
consists of the triples `(R, x, y)` with `|R| = m` and `x, y ∈ R`. Each edge `e`, with endpoint
transposition `τ_e`, gives three involutions: `T^sh_e` applies `τ_e` to all three coordinates
when `|e ∩ R| = 1`, and `T^1_e`, `T^2_e` apply `τ_e` to `x`, respectively `y`, when `e ⊆ R`. On
the cycle `ℤ/nℤ` with edges `{z, z + 1}` this is the two-copy process `𝒯_{n,m}`, which defines
the coincidence probability `C_{n,m}(t)` and the explicit error `ℰ_{n,m}(t)`. The black-labelled
chains on `Ξ'_A` and `Ξ_A` also record the positions of the black cards, as an embedding of
`ℤ/nℤ ∖ A` into `ℤ/nℤ`.

## Main definitions

* `TwoCopyMove`: The moves `sh e`, `one e`, `two e` on an edge `e`.
* `TwoCopyState`: The state space `{(R, x, y) : |R| = m, x, y ∈ R}`.
* `twoCopyFamily`: The two-copy involution family `T^sh_e`, `T^1_e`, `T^2_e` for edges `edge`.
* `twoCopy`: The cycle two-copy process `𝒯_{n,m}` on `Ω_{n,m} = TwoCopyState (ZMod n) m`.
* `coincidenceProb`: The coincidence probability `C_{n,m}(t)`.
* `paperError`: The explicit error `ℰ_{n,m}(t)`, the right side of Lemma 4.1 of the paper.
* `BlackConfig`: The black configurations `𝔅_A`, embeddings `ℤ/nℤ ∖ A ↪ ℤ/nℤ`.
* `blackRed`: The red positions `R(β)` of a black configuration `β`.
* `blackOneCopy`: The black-labelled one-copy chain `𝒰_A` on `Ξ'_A = BlackOneState n A`.
* `blackTwoCopy`: The black-labelled two-copy chain `𝒢_A` on `Ξ_A = BlackTwoState n A`.
* `BlackTwoState.proj`: The projection `(β, y₁, y₂) ↦ (R(β), y₁, y₂)` from `Ξ_A` to `Ω_{n,m}`.

## Main results

* `TwoCopyState.sum_eq`: A sum over `TwoCopyState V m` is a sum over `m`-sets `R` and `x, y ∈ R`.
* `TwoCopyState.card_eq`: `|TwoCopyState V m| = C(|V|, m) m²`.
* `card_blackRed`: `|R(β)| = |A|` for every `β ∈ 𝔅_A`.

## Implementation notes

* A permutation acts on a set by `Finset.map`, and `edgeSwap (cycleEdge n) z` is definitionally
  `Equiv.swap z (z + 1)`.
* `coincidenceProb` writes the paper's sum `∑_{A,i} ζ_m(A,i) ∑_{(R,x)} P_t((A,i,i),(R,x,x))` as a
  sum over the diagonal states `w = (A, i, i)` of `Ω_{n,m}`, weighted by
  `exposureWeight n m w.R w.x`; the pairs `(A, i)` left out are exactly those with
  `ζ_m(A, i) = 0`.
* `paperError` takes real-valued `n` and `m`, so no natural-number subtraction occurs.
-/

@[expose] public section

open Finset

namespace CycleCutoff

/-! ### The generic two-copy construction -/

/-- The three moves on an edge `e`: `sh e` (shared transposition, `T^sh_e`), `one e`
(first auxiliary coordinate, `T^1_e`), `two e` (second auxiliary coordinate, `T^2_e`). -/
inductive TwoCopyMove (ι : Type*)
  | sh (e : ι)
  | one (e : ι)
  | two (e : ι)
  deriving DecidableEq, Fintype

namespace TwoCopyMove

variable {ι κ : Type*}

/-- The equivalence `TwoCopyMove ι ≃ ι ⊕ ι ⊕ ι` sending `sh e`, `one e`, `two e` to the three
summands. -/
def equivSum : TwoCopyMove ι ≃ ι ⊕ ι ⊕ ι where
  toFun
    | .sh e => .inl e
    | .one e => .inr (.inl e)
    | .two e => .inr (.inr e)
  invFun
    | .inl e => .sh e
    | .inr (.inl e) => .one e
    | .inr (.inr e) => .two e
  left_inv := by rintro (e | e | e) <;> rfl
  right_inv := by rintro (e | e | e) <;> rfl

/-- A sum over the moves splits into the three kinds of move. -/
theorem sum_eq [Fintype ι] {M : Type*} [AddCommMonoid M] (f : TwoCopyMove ι → M) :
    ∑ θ, f θ = ∑ e, f (.sh e) + ∑ e, f (.one e) + ∑ e, f (.two e) := by
  rw [Fintype.sum_equiv equivSum f (fun p => f (equivSum.symm p))
    (fun θ => by rw [Equiv.symm_apply_apply]), Fintype.sum_sum_type, Fintype.sum_sum_type,
    add_assoc]
  rfl

/-- The move `map σ θ` is `θ` with its edge relabelled by `σ`. -/
def map (σ : ι → κ) : TwoCopyMove ι → TwoCopyMove κ
  | .sh e => .sh (σ e)
  | .one e => .one (σ e)
  | .two e => .two (σ e)

/-- Relabelling `sh e` by `σ` gives `sh (σ e)`. -/
@[simp] theorem map_sh (σ : ι → κ) (e : ι) : map σ (.sh e) = .sh (σ e) := rfl
/-- Relabelling `one e` by `σ` gives `one (σ e)`. -/
@[simp] theorem map_one (σ : ι → κ) (e : ι) : map σ (.one e) = .one (σ e) := rfl
/-- Relabelling `two e` by `σ` gives `two (σ e)`. -/
@[simp] theorem map_two (σ : ι → κ) (e : ι) : map σ (.two e) = .two (σ e) := rfl

end TwoCopyMove

variable (V : Type*)

/-- The two-copy state space `{(R, x, y) : |R| = m, x, y ∈ R}`. -/
abbrev TwoCopyState (m : ℕ) : Type _ :=
  {p : Finset V × V × V // p.1.card = m ∧ p.2.1 ∈ p.1 ∧ p.2.2 ∈ p.1}

variable {V}

namespace TwoCopyState

variable {m : ℕ} (w : TwoCopyState V m)

/-- The red set `R` of a two-copy state. -/
def R : Finset V := w.1.1

/-- The first auxiliary coordinate `x`. -/
def x : V := w.1.2.1

/-- The second auxiliary coordinate `y`. -/
def y : V := w.1.2.2

/-- The red set of a state in `TwoCopyState V m` has `m` elements. -/
theorem card_R : w.R.card = m := w.2.1

/-- The first auxiliary coordinate lies in the red set. -/
theorem x_mem : w.x ∈ w.R := w.2.2.1

/-- The second auxiliary coordinate lies in the red set. -/
theorem y_mem : w.y ∈ w.R := w.2.2.2

/-- The red set of `⟨p, h⟩` is `p.1`. -/
@[simp] theorem R_mk (p : Finset V × V × V) (h) :
    TwoCopyState.R (⟨p, h⟩ : TwoCopyState V m) = p.1 := rfl

/-- The first auxiliary coordinate of `⟨p, h⟩` is `p.2.1`. -/
@[simp] theorem x_mk (p : Finset V × V × V) (h) :
    TwoCopyState.x (⟨p, h⟩ : TwoCopyState V m) = p.2.1 := rfl

/-- The second auxiliary coordinate of `⟨p, h⟩` is `p.2.2`. -/
@[simp] theorem y_mk (p : Finset V × V × V) (h) :
    TwoCopyState.y (⟨p, h⟩ : TwoCopyState V m) = p.2.2 := rfl

/-- Two two-copy states are equal iff their red sets and both auxiliary coordinates agree. -/
theorem ext_iff' {w w' : TwoCopyState V m} : w = w' ↔ w.R = w'.R ∧ w.x = w'.x ∧ w.y = w'.y := by
  rw [Subtype.ext_iff, Prod.ext_iff, Prod.ext_iff]
  rfl

/-- The diagonal state `(R, x, x)` built from `(R, x, y)`. -/
def diag : TwoCopyState V m := ⟨(w.R, w.x, w.x), w.card_R, w.x_mem, w.x_mem⟩

/-- The red set of `w.diag` is that of `w`. -/
@[simp] theorem R_diag : w.diag.R = w.R := rfl
/-- The first auxiliary coordinate of `w.diag` is `w.x`. -/
@[simp] theorem x_diag : w.diag.x = w.x := rfl
/-- The second auxiliary coordinate of `w.diag` is `w.x`. -/
@[simp] theorem y_diag : w.diag.y = w.x := rfl

/-- A permutation `τ` of `V` acting on all three coordinates: `(τ R, τ x, τ y)`. -/
def permMap (τ : Equiv.Perm V) : TwoCopyState V m :=
  ⟨(w.R.map τ.toEmbedding, τ w.x, τ w.y), by rw [card_map, w.card_R],
    mem_map_of_mem _ w.x_mem, mem_map_of_mem _ w.y_mem⟩

/-- The red set of `w.permMap τ` is the image of `w.R` under `τ`. -/
@[simp] theorem R_permMap (τ : Equiv.Perm V) : (w.permMap τ).R = w.R.map τ.toEmbedding := rfl
/-- The first auxiliary coordinate of `w.permMap τ` is `τ w.x`. -/
@[simp] theorem x_permMap (τ : Equiv.Perm V) : (w.permMap τ).x = τ w.x := rfl
/-- The second auxiliary coordinate of `w.permMap τ` is `τ w.y`. -/
@[simp] theorem y_permMap (τ : Equiv.Perm V) : (w.permMap τ).y = τ w.y := rfl

/-- Acting by `τ` and then by `τ'` is acting by `τ' * τ`. -/
theorem permMap_permMap (τ τ' : Equiv.Perm V) :
    (w.permMap τ).permMap τ' = w.permMap (τ' * τ) :=
  ext_iff'.2 ⟨map_map _ _ _, rfl, rfl⟩

/-- Acting twice by a transposition is the identity. -/
theorem permMap_swap_swap [DecidableEq V] (a b : V) :
    (w.permMap (Equiv.swap a b)).permMap (Equiv.swap a b) = w := by
  rw [permMap_permMap, Equiv.swap_mul_self]
  exact ext_iff'.2 ⟨map_refl, rfl, rfl⟩

/-- Transport of two-copy states along a bijection of the vertex types. -/
def congr {V' : Type*} (e : V ≃ V') : TwoCopyState V m ≃ TwoCopyState V' m where
  toFun w := ⟨(w.R.map e.toEmbedding, e w.x, e w.y), by rw [card_map, w.card_R],
    mem_map_of_mem _ w.x_mem, mem_map_of_mem _ w.y_mem⟩
  invFun w := ⟨(w.R.map e.symm.toEmbedding, e.symm w.x, e.symm w.y), by rw [card_map, w.card_R],
    mem_map_of_mem _ w.x_mem, mem_map_of_mem _ w.y_mem⟩
  left_inv w := ext_iff'.2 ⟨by simp [map_map], by simp, by simp⟩
  right_inv w := ext_iff'.2 ⟨by simp [map_map], by simp, by simp⟩

/-- The red set of `congr e w` is the image of `w.R` under `e`. -/
@[simp] theorem R_congr {V' : Type*} (e : V ≃ V') :
    (congr e w).R = w.R.map e.toEmbedding := rfl
/-- The first auxiliary coordinate of `congr e w` is `e w.x`. -/
@[simp] theorem x_congr {V' : Type*} (e : V ≃ V') : (congr e w).x = e w.x := rfl
/-- The second auxiliary coordinate of `congr e w` is `e w.y`. -/
@[simp] theorem y_congr {V' : Type*} (e : V ≃ V') : (congr e w).y = e w.y := rfl

section Counting

variable [Fintype V] [DecidableEq V] {M : Type*} [AddCommMonoid M]

/-- A sum over the two-copy states `(R, x, y)` is a sum over the `m`-subsets `R` and then over
`x ∈ R` and `y ∈ R`. -/
theorem sum_eq (g : Finset V → V → V → M) :
    ∑ w : TwoCopyState V m, g w.R w.x w.y =
      ∑ R ∈ univ.powersetCard m, ∑ x ∈ R, ∑ y ∈ R, g R x y := by
  have h : ∑ p ∈ univ.filter
        (fun p : Finset V × V × V => p.1.card = m ∧ p.2.1 ∈ p.1 ∧ p.2.2 ∈ p.1),
        g p.1 p.2.1 p.2.2 = ∑ w : TwoCopyState V m, g w.R w.x w.y :=
    Finset.sum_subtype _ (fun _ => by simp) _
  rw [← h, sum_filter, Fintype.sum_prod_type, ← univ_filter_card_eq, sum_filter]
  refine sum_congr rfl fun R _ => ?_
  by_cases hR : R.card = m
  · simp only [hR, true_and, if_true, Fintype.sum_prod_type]
    calc _ = ∑ x, if x ∈ R then ∑ y ∈ R, g R x y else 0 := by
          refine sum_congr rfl fun x _ => ?_
          by_cases hx : x ∈ R <;> simp [hx, Finset.sum_ite_mem]
      _ = _ := by simp [Finset.sum_ite_mem]
  · simp [hR]

/-- `|Ω| = C(|V|, m) m²`: an `m`-set `R` and two points of `R`. -/
theorem card_eq : Fintype.card (TwoCopyState V m) = (Fintype.card V).choose m * m * m := by
  have h := sum_eq (V := V) (m := m) (M := ℕ) (fun _ _ _ => 1)
  simp only [sum_const, card_univ, smul_eq_mul, mul_one] at h
  rw [h, sum_congr rfl fun R hR => by rw [(mem_powersetCard_univ.1 hR)], sum_const,
    card_powersetCard, card_univ, smul_eq_mul, mul_assoc]

/-- A sum over the two-copy states `(R, x, y)` is a sum over the `m`-subsets `R` of a sum over
`(x, y) ∈ R × R`. -/
theorem sum_eq_sum_product (f : Finset V × V × V → M) :
    ∑ w : TwoCopyState V m, f w.1 =
      ∑ R ∈ (univ : Finset V).powersetCard m, ∑ q ∈ R ×ˢ R, f (R, q) := by
  rw [← Finset.sum_subtype (univ.filter fun p : Finset V × V × V =>
    p.1.card = m ∧ p.2.1 ∈ p.1 ∧ p.2.2 ∈ p.1) (by simp) f]
  refine Finset.sum_finset_product _ _ _ ?_
  rintro ⟨R, x, y⟩
  simp [mem_powersetCard]

end Counting

end TwoCopyState

section Generic

variable [DecidableEq V] {ι : Type*} (edge : ι → V × V)

/-- The transposition `τ_e` exchanging the two endpoints of edge `e`. -/
def edgeSwap (e : ι) : Equiv.Perm V := Equiv.swap (edge e).1 (edge e).2

/-- The vertex set `{a, b}` of edge `e`. -/
def edgeSet (e : ι) : Finset V := {(edge e).1, (edge e).2}

/-- A vertex lies on edge `e` iff it is one of the two endpoints of `e`. -/
theorem mem_edgeSet {e : ι} {v : V} : v ∈ edgeSet edge e ↔ v = (edge e).1 ∨ v = (edge e).2 := by
  simp [edgeSet]

/-- The transposition `τ_e` is an involution. -/
theorem edgeSwap_edgeSwap (e : ι) (v : V) : edgeSwap edge e (edgeSwap edge e v) = v :=
  Equiv.swap_apply_self _ _ _

/-- The transposition `τ_e` maps the vertex set of `e` onto itself. -/
theorem map_edgeSwap_edgeSet (e : ι) :
    (edgeSet edge e).map (edgeSwap edge e).toEmbedding = edgeSet edge e := by
  simp [edgeSet, edgeSwap, pair_comm]

/-- `τ_e v ∈ R` whenever `v ∈ R` and both endpoints of `e` lie in `R`. -/
theorem edgeSwap_mem_of_subset {e : ι} {R : Finset V} (he : edgeSet edge e ⊆ R) {v : V}
    (hv : v ∈ R) : edgeSwap edge e v ∈ R := by
  rw [edgeSet, insert_subset_iff, singleton_subset_iff] at he
  rw [edgeSwap, Equiv.swap_apply_def]
  split_ifs <;> simp [he, hv]

/-- `τ_e R ∩ e = τ_e (R ∩ e)`. -/
theorem inter_edgeSet_map (e : ι) (R : Finset V) :
    R.map (edgeSwap edge e).toEmbedding ∩ edgeSet edge e =
      (R ∩ edgeSet edge e).map (edgeSwap edge e).toEmbedding := by
  rw [map_inter, map_edgeSwap_edgeSet]

/-- `e ⊆ τ_e R` iff `e ⊆ R`. -/
theorem edgeSet_subset_map_iff (e : ι) (R : Finset V) :
    edgeSet edge e ⊆ R.map (edgeSwap edge e).toEmbedding ↔ edgeSet edge e ⊆ R := by
  conv_lhs => rw [← map_edgeSwap_edgeSet edge e]
  exact map_subset_map

variable (m : ℕ)

/-- `T^sh_e(R, x, y) = (τ_e R, τ_e x, τ_e y)` if `|e ∩ R| = 1`, else the identity. -/
def shMove (e : ι) (w : TwoCopyState V m) : TwoCopyState V m :=
  if (w.R ∩ edgeSet edge e).card = 1 then w.permMap (edgeSwap edge e) else w

/-- `T^1_e(R, x, y) = (R, τ_e x, y)` if `e ⊆ R`, else the identity. -/
def oneMove (e : ι) (w : TwoCopyState V m) : TwoCopyState V m :=
  if h : edgeSet edge e ⊆ w.R then
    ⟨(w.R, edgeSwap edge e w.x, w.y), w.card_R, edgeSwap_mem_of_subset edge h w.x_mem, w.y_mem⟩
  else w

/-- `T^2_e(R, x, y) = (R, x, τ_e y)` if `e ⊆ R`, else the identity. -/
def twoMove (e : ι) (w : TwoCopyState V m) : TwoCopyState V m :=
  if h : edgeSet edge e ⊆ w.R then
    ⟨(w.R, w.x, edgeSwap edge e w.y), w.card_R, w.x_mem, edgeSwap_mem_of_subset edge h w.y_mem⟩
  else w

/-- `T^sh_e` is an involution. -/
theorem shMove_involutive (e : ι) : Function.Involutive (shMove edge m e) := by
  intro w
  by_cases h : (w.R ∩ edgeSet edge e).card = 1
  · have h' : ((w.permMap (edgeSwap edge e)).R ∩ edgeSet edge e).card = 1 := by
      rw [TwoCopyState.R_permMap, inter_edgeSet_map, card_map, h]
    simp only [shMove, h, h', if_true]
    exact w.permMap_swap_swap _ _
  · simp [shMove, h]

/-- `T^1_e` is an involution. -/
theorem oneMove_involutive (e : ι) : Function.Involutive (oneMove edge m e) := by
  intro w
  by_cases h : edgeSet edge e ⊆ w.R <;> simp [oneMove, h, TwoCopyState.ext_iff', edgeSwap_edgeSwap]

/-- `T^2_e` is an involution. -/
theorem twoMove_involutive (e : ι) : Function.Involutive (twoMove edge m e) := by
  intro w
  by_cases h : edgeSet edge e ⊆ w.R <;> simp [twoMove, h, TwoCopyState.ext_iff', edgeSwap_edgeSwap]

/-- The generic two-copy involution family on `TwoCopyState V m`, for the graph with edges
`edge : ι → V × V`: the maps `T^sh_e`, `T^1_e`, `T^2_e` (`e ∈ ι`). -/
def twoCopyFamily : InvFamily (TwoCopyMove ι) (TwoCopyState V m) where
  T
    | .sh e => shMove edge m e
    | .one e => oneMove edge m e
    | .two e => twoMove edge m e
  involutive
    | .sh e => shMove_involutive edge m e
    | .one e => oneMove_involutive edge m e
    | .two e => twoMove_involutive edge m e

/-- The map of `twoCopyFamily` indexed by `sh e` is `T^sh_e`. -/
@[simp] theorem twoCopyFamily_T_sh (e : ι) :
    (twoCopyFamily edge m).T (.sh e) = shMove edge m e := rfl
/-- The map of `twoCopyFamily` indexed by `one e` is `T^1_e`. -/
@[simp] theorem twoCopyFamily_T_one (e : ι) :
    (twoCopyFamily edge m).T (.one e) = oneMove edge m e := rfl
/-- The map of `twoCopyFamily` indexed by `two e` is `T^2_e`. -/
@[simp] theorem twoCopyFamily_T_two (e : ι) :
    (twoCopyFamily edge m).T (.two e) = twoMove edge m e := rfl

end Generic

/-! ### The cycle two-copy process `𝒯_{n,m}` -/

section Cycle

variable (n : ℕ)

/-- The cycle edges `e_z = {z, z + 1}`, `z ∈ ℤ/nℤ`. -/
def cycleEdge (z : ZMod n) : ZMod n × ZMod n := (z, z + 1)

/-- The transposition of the cycle edge `e_z` is `τ_z = (z z+1)`. -/
@[simp] theorem edgeSwap_cycleEdge (z : ZMod n) :
    edgeSwap (cycleEdge n) z = Equiv.swap z (z + 1) := rfl

/-- The vertex set of the cycle edge `e_z` is `{z, z + 1}`. -/
@[simp] theorem edgeSet_cycleEdge (z : ZMod n) : edgeSet (cycleEdge n) z = {z, z + 1} := rfl

/-- The two-copy process `𝒯_{n,m}` on `Ω_{n,m} = TwoCopyState (ZMod n) m`: for each `z ∈ ℤ/nℤ` the
maps `T^sh_z`, `T^1_z`, `T^2_z`. -/
@[cycle_cutoff "def_two_copy"]
def twoCopy (m : ℕ) : InvFamily (TwoCopyMove (ZMod n)) (TwoCopyState (ZMod n) m) :=
  twoCopyFamily (cycleEdge n) m

/-- The coincidence probability
`C_{n,m}(t) = ∑_{A,i} ζ_m(A,i) ∑_{(R,x)} P^{𝒯_{n,m}}_t((A,i,i),(R,x,x))`, summed over the diagonal
states `(A, i, i)` and `(R, x, x)` of `Ω_{n,m}`. -/
@[cycle_cutoff "def_Cnm"]
noncomputable def coincidenceProb [NeZero n] (m : ℕ) (t : ℝ) : ℝ :=
  ∑ w : TwoCopyState (ZMod n) m with w.x = w.y, exposureWeight n m w.R w.x *
    ∑ w' : TwoCopyState (ZMod n) m with w'.x = w'.y, (twoCopy n m).semigroup t w w'

/-- The explicit error
`ℰ_{n,m}(t) = C_{n,m}(t) - (n/m) S₂(t) + (n/m)² ((n-m)/(n-1)) (S₃(t) - S₂(t)/n)`. -/
@[cycle_cutoff "def_paper_error"]
noncomputable def paperError [NeZero n] (m : ℕ) (t : ℝ) : ℝ :=
  coincidenceProb n m t - (n : ℝ) / m * S2 n t +
    ((n : ℝ) / m) ^ 2 * (((n : ℝ) - m) / ((n : ℝ) - 1)) * (S3 n t - S2 n t / n)

end Cycle

/-! ### Black configurations and the black-labelled chains -/

section Black

variable (n : ℕ) [NeZero n]

/-- The black configurations `𝔅_A`: injective maps `ℤ/nℤ ∖ A → ℤ/nℤ` (the positions of the black
cards). -/
@[cycle_cutoff "def_black_configurations"]
abbrev BlackConfig (A : Finset (ZMod n)) : Type :=
  {z : ZMod n // z ∉ A} ↪ ZMod n

variable {n} {A : Finset (ZMod n)}

/-- The red positions `R(β) = ℤ/nℤ ∖ β(ℤ/nℤ ∖ A)`. -/
@[cycle_cutoff "def_black_configurations"]
def blackRed (β : BlackConfig n A) : Finset (ZMod n) :=
  (univ.map β)ᶜ

/-- `v ∈ R(β)` iff `v` is not in the image of `β`. -/
theorem mem_blackRed {β : BlackConfig n A} {v : ZMod n} :
    v ∈ blackRed β ↔ ∀ a, β a ≠ v := by
  simp [blackRed]

variable (A) in
/-- The inclusion `ι_A : ℤ/nℤ ∖ A ↪ ℤ/nℤ`. -/
@[cycle_cutoff "def_black_configurations"]
def blackIncl : BlackConfig n A := Function.Embedding.subtype _

omit [NeZero n] in
/-- `ι_A a = a`. -/
@[simp] theorem blackIncl_apply (a : {z : ZMod n // z ∉ A}) : blackIncl A a = a := rfl

/-- `R(ι_A) = A`. -/
@[simp] theorem blackRed_incl : blackRed (blackIncl A) = A := by
  ext v
  rw [mem_blackRed]
  exact ⟨fun h => by_contra fun hv => h ⟨v, hv⟩ rfl,
    fun hv a hav => a.2 (by rwa [← hav] at hv)⟩

/-- `|R(β)| = |A|`. -/
theorem card_blackRed (β : BlackConfig n A) : (blackRed β).card = A.card := by
  rw [blackRed, card_compl, card_map, card_univ, ZMod.card, Fintype.card_subtype_compl,
    Fintype.card_coe, ZMod.card]
  exact Nat.sub_sub_self (by simpa [ZMod.card] using A.card_le_univ)

/-- `R(τ ∘ β) = τ R(β)`. -/
theorem blackRed_trans (β : BlackConfig n A) (τ : Equiv.Perm (ZMod n)) :
    blackRed (β.trans τ.toEmbedding) = (blackRed β).map τ.toEmbedding := by
  ext v
  simp only [mem_map_equiv, mem_blackRed, Function.Embedding.trans_apply,
    Equiv.coe_toEmbedding]
  exact forall_congr' fun a => by rw [ne_eq, ne_eq, Equiv.eq_symm_apply]

omit [NeZero n] in
/-- Composing a black configuration twice with a transposition gives it back. -/
theorem trans_swap_trans_swap (β : BlackConfig n A) (a b : ZMod n) :
    (β.trans (Equiv.swap a b).toEmbedding).trans (Equiv.swap a b).toEmbedding = β := by
  ext v
  simp

variable (A) in
/-- The restriction `σ|_{A^c}` of a permutation to the complement of `A`, as a black
configuration. -/
def permRestrict (σ : Equiv.Perm (ZMod n)) : BlackConfig n A :=
  (blackIncl A).trans σ.toEmbedding

omit [NeZero n] in
/-- `σ|_{A^c} a = σ a`. -/
@[simp] theorem permRestrict_apply (σ : Equiv.Perm (ZMod n)) (a : {z : ZMod n // z ∉ A}) :
    permRestrict A σ a = σ a := rfl

variable (n A) in
/-- The state space `Ξ'_A = {(β, y) : β ∈ 𝔅_A, y ∈ R(β)}`. -/
@[cycle_cutoff "def_black_one_copy"]
abbrev BlackOneState : Type :=
  {p : BlackConfig n A × ZMod n // p.2 ∈ blackRed p.1}

variable (n A) in
/-- The black-labelled one-copy chain `𝒰_A = (U_z)_z`, `U_z(β, y) = (τ_z ∘ β, τ_z y)`. -/
@[cycle_cutoff "def_black_one_copy"]
def blackOneCopy : InvFamily (ZMod n) (BlackOneState n A) where
  T z w := ⟨(w.1.1.trans (Equiv.swap z (z + 1)).toEmbedding, Equiv.swap z (z + 1) w.1.2), by
    rw [blackRed_trans]; exact mem_map_of_mem _ w.2⟩
  involutive z w := Subtype.ext <| by simp [trans_swap_trans_swap]

/-- `U_z(β, y) = (τ_z ∘ β, τ_z y)`. -/
@[simp] theorem blackOneCopy_T_val (z : ZMod n) (w : BlackOneState n A) :
    ((blackOneCopy n A).T z w).1 =
      (w.1.1.trans (Equiv.swap z (z + 1)).toEmbedding, Equiv.swap z (z + 1) w.1.2) := rfl

/-- The start state `(ι_A, i) ∈ Ξ'_A`, for `i ∈ A`. -/
def blackOneInit {i : ZMod n} (hi : i ∈ A) : BlackOneState n A :=
  ⟨(blackIncl A, i), by rwa [blackRed_incl]⟩

variable (n A) in
/-- The state space `Ξ_A = {(β, y₁, y₂) : β ∈ 𝔅_A, y₁, y₂ ∈ R(β)}`. -/
@[cycle_cutoff "def_black_two_copy"]
abbrev BlackTwoState : Type :=
  {p : BlackConfig n A × ZMod n × ZMod n // p.2.1 ∈ blackRed p.1 ∧ p.2.2 ∈ blackRed p.1}

/-- `S_z(β, y₁, y₂) = (τ_z ∘ β, τ_z y₁, τ_z y₂)` if `e_z ⊄ R(β)`, else the identity. -/
def blackS (z : ZMod n) (w : BlackTwoState n A) : BlackTwoState n A :=
  if ({z, z + 1} : Finset (ZMod n)) ⊆ blackRed w.1.1 then w
  else ⟨(w.1.1.trans (Equiv.swap z (z + 1)).toEmbedding, Equiv.swap z (z + 1) w.1.2.1,
      Equiv.swap z (z + 1) w.1.2.2), by
    rw [blackRed_trans]; exact ⟨mem_map_of_mem _ w.2.1, mem_map_of_mem _ w.2.2⟩⟩

/-- `X_z(β, y₁, y₂) = (β, τ_z y₁, y₂)` if `e_z ⊆ R(β)`, else the identity. -/
def blackX (z : ZMod n) (w : BlackTwoState n A) : BlackTwoState n A :=
  if h : ({z, z + 1} : Finset (ZMod n)) ⊆ blackRed w.1.1 then
    ⟨(w.1.1, Equiv.swap z (z + 1) w.1.2.1, w.1.2.2),
      edgeSwap_mem_of_subset (cycleEdge n) (e := z) h w.2.1, w.2.2⟩
  else w

/-- `Y_z(β, y₁, y₂) = (β, y₁, τ_z y₂)` if `e_z ⊆ R(β)`, else the identity. -/
def blackY (z : ZMod n) (w : BlackTwoState n A) : BlackTwoState n A :=
  if h : ({z, z + 1} : Finset (ZMod n)) ⊆ blackRed w.1.1 then
    ⟨(w.1.1, w.1.2.1, Equiv.swap z (z + 1) w.1.2.2),
      w.2.1, edgeSwap_mem_of_subset (cycleEdge n) (e := z) h w.2.2⟩
  else w

/-- `S_z` is an involution. -/
theorem blackS_involutive (z : ZMod n) : Function.Involutive (blackS (A := A) z) := by
  intro w
  by_cases h : ({z, z + 1} : Finset (ZMod n)) ⊆ blackRed w.1.1
  · simp [blackS, h]
  · have h' : ¬ ({z, z + 1} : Finset (ZMod n)) ⊆
        blackRed (w.1.1.trans (Equiv.swap z (z + 1)).toEmbedding) := by
      rw [blackRed_trans]
      exact fun h'' => h ((edgeSet_subset_map_iff (cycleEdge n) z _).1 h'')
    simp [blackS, h, h', trans_swap_trans_swap]

/-- `X_z` is an involution. -/
theorem blackX_involutive (z : ZMod n) : Function.Involutive (blackX (A := A) z) := by
  intro w
  by_cases h : ({z, z + 1} : Finset (ZMod n)) ⊆ blackRed w.1.1 <;> simp [blackX, h]

/-- `Y_z` is an involution. -/
theorem blackY_involutive (z : ZMod n) : Function.Involutive (blackY (A := A) z) := by
  intro w
  by_cases h : ({z, z + 1} : Finset (ZMod n)) ⊆ blackRed w.1.1 <;> simp [blackY, h]

variable (n A) in
/-- The black-labelled two-copy chain `𝒢_A`: for each `z`, the maps `S_z` (index `sh z`), `X_z`
(index `one z`) and `Y_z` (index `two z`). -/
@[cycle_cutoff "def_black_two_copy"]
def blackTwoCopy : InvFamily (TwoCopyMove (ZMod n)) (BlackTwoState n A) where
  T
    | .sh z => blackS z
    | .one z => blackX z
    | .two z => blackY z
  involutive
    | .sh z => blackS_involutive z
    | .one z => blackX_involutive z
    | .two z => blackY_involutive z

/-- The map of `𝒢_A` indexed by `sh z` is `S_z`. -/
@[simp] theorem blackTwoCopy_T_sh (z : ZMod n) : (blackTwoCopy n A).T (.sh z) = blackS z := rfl
/-- The map of `𝒢_A` indexed by `one z` is `X_z`. -/
@[simp] theorem blackTwoCopy_T_one (z : ZMod n) : (blackTwoCopy n A).T (.one z) = blackX z := rfl
/-- The map of `𝒢_A` indexed by `two z` is `Y_z`. -/
@[simp] theorem blackTwoCopy_T_two (z : ZMod n) : (blackTwoCopy n A).T (.two z) = blackY z := rfl

/-- The start state `(ι_A, i, i) ∈ Ξ_A`, for `i ∈ A`. -/
def blackTwoInit {i : ZMod n} (hi : i ∈ A) : BlackTwoState n A :=
  ⟨(blackIncl A, i, i), by rw [blackRed_incl]; exact ⟨hi, hi⟩⟩

/-- The projection `(β, y₁, y₂) ↦ (R(β), y₁, y₂)` from `Ξ_A` to `Ω_{n,m}`, for `|A| = m`. -/
def BlackTwoState.proj {m : ℕ} (hA : A.card = m) (w : BlackTwoState n A) :
    TwoCopyState (ZMod n) m :=
  ⟨(blackRed w.1.1, w.1.2.1, w.1.2.2), by rw [card_blackRed, hA], w.2.1, w.2.2⟩

/-- The red set of `w.proj hA` is `R(β)`. -/
@[simp] theorem BlackTwoState.proj_R {m : ℕ} (hA : A.card = m) (w : BlackTwoState n A) :
    (w.proj hA).R = blackRed w.1.1 := rfl
/-- The first auxiliary coordinate of `w.proj hA` is `y₁`. -/
@[simp] theorem BlackTwoState.proj_x {m : ℕ} (hA : A.card = m) (w : BlackTwoState n A) :
    (w.proj hA).x = w.1.2.1 := rfl
/-- The second auxiliary coordinate of `w.proj hA` is `y₂`. -/
@[simp] theorem BlackTwoState.proj_y {m : ℕ} (hA : A.card = m) (w : BlackTwoState n A) :
    (w.proj hA).y = w.1.2.2 := rfl

end Black

end CycleCutoff
