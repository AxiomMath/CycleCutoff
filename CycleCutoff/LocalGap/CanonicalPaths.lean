/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.LocalGap.Defs

/-!
# Canonical paths for the path two-copy process

Each state `(R, x, y) ∈ Ω^p_{s,k}` with `x ≠ y` is joined to `(R, x, x)` by a word in the path
two-copy process `𝒯^p_{s,k}` of length at most `2s`, and each pair of a move and a state occurs
along these words at most `2s` times.

The words are explicit. Say `x < y` (the case `x > y` is symmetric). The path runs along the edges
`y - 1, …, x + 1`, then `x`, then `x + 1, …, y - 1`, and on each edge `q` it uses `T^2_q` if both
endpoints of `e_q` lie in the current red set and `T^sh_q` otherwise.

## Main results

* `CycleCutoff.exists_pathTwoCopy_canonical_paths`: the canonical paths, of length `≤ 2s`, with
  congestion `≤ 2s`.

## Implementation notes

* Positions are `Fin s` and edges `Fin (s - 1)`, 0-indexed; edge `j` joins `j` and `j + 1`.
* The pairs `((R, x, y), r)` with `1 ≤ r ≤ L` are counted by their 0-indexed positions `r - 1 < L`.
* No hypothesis on `s` or `k` is assumed.
-/

public section

open Finset

namespace CycleCutoff

variable {s k : ℕ}

private theorem mem_edgeSet_pathEdge {q : Fin (s - 1)} {v : Fin s} :
    v ∈ edgeSet (pathEdge s) q ↔ (v : ℕ) = q ∨ (v : ℕ) = q + 1 := by
  simp [mem_edgeSet, pathEdge, Fin.ext_iff]

private theorem adjSwap_val (q : Fin (s - 1)) (v : Fin s) :
    (adjSwap s q v : ℕ) =
      if (v : ℕ) = q then (q : ℕ) + 1 else if (v : ℕ) = (q : ℕ) + 1 then (q : ℕ) else (v : ℕ) := by
  rw [adjSwap, Equiv.swap_apply_def]
  split_ifs <;> simp_all [Fin.ext_iff]

private theorem adjSwap_apply_of_notMem {q : Fin (s - 1)} {v : Fin s}
    (h : v ∉ edgeSet (pathEdge s) q) : adjSwap s q v = v := by
  rw [mem_edgeSet_pathEdge] at h
  ext
  rw [adjSwap_val]
  split_ifs <;> lia

private theorem map_adjSwap_eq_self {q : Fin (s - 1)} {R : Finset (Fin s)}
    (h : (∀ v ∈ edgeSet (pathEdge s) q, v ∈ R) ∨ ∀ v ∈ edgeSet (pathEdge s) q, v ∉ R) :
    R.map (adjSwap s q).toEmbedding = R := by
  ext v
  rw [mem_map_equiv, show (adjSwap s q).symm = adjSwap s q from Equiv.symm_swap _ _]
  by_cases hv : v ∈ edgeSet (pathEdge s) q
  · have hv' : adjSwap s q v ∈ edgeSet (pathEdge s) q := by
      rw [mem_edgeSet_pathEdge] at hv ⊢
      rw [adjSwap_val]
      split_ifs <;> lia
    rcases h with h | h
    · exact iff_of_true (h _ hv') (h _ hv)
    · exact iff_of_false (h _ hv') (h _ hv)
  · rw [adjSwap_apply_of_notMem hv]

private theorem permMap_one {m : ℕ} (u : TwoCopyState (Fin s) m) : u.permMap 1 = u :=
  TwoCopyState.ext_iff'.2 ⟨by ext; simp [mem_map_equiv, ← Equiv.Perm.inv_def], rfl, rfl⟩

/-! ### One step along an edge -/

/-- The move used on edge `q` at state `u`: `T^2_q` if the edge is red–red, else `T^sh_q`. -/
private def pathMove (q : Fin (s - 1)) (u : TwoCopyState (Fin s) k) :
    TwoCopyMove (Fin (s - 1)) :=
  if edgeSet (pathEdge s) q ⊆ u.R then .two q else .sh q

/-- The state reached from `u` by the move `pathMove q u`. -/
private def pathStep (q : Fin (s - 1)) (u : TwoCopyState (Fin s) k) : TwoCopyState (Fin s) k :=
  (pathTwoCopy s k).T (pathMove q u) u

private theorem subset_R_pathStep_iff (q : Fin (s - 1)) (u : TwoCopyState (Fin s) k) :
    edgeSet (pathEdge s) q ⊆ (pathStep q u).R ↔ edgeSet (pathEdge s) q ⊆ u.R := by
  unfold pathStep pathMove
  split_ifs with h
  · simp only [pathTwoCopy, twoCopyFamily_T_two, twoMove, dif_pos h, TwoCopyState.R_mk]
  · simp only [pathTwoCopy, twoCopyFamily_T_sh, shMove]
    split_ifs
    · rw [TwoCopyState.R_permMap, edgeSwap_pathEdge]
      exact edgeSet_subset_map_iff (pathEdge s) q u.R
    · rfl

private theorem pathStep_injective (q : Fin (s - 1)) :
    Function.Injective (pathStep (k := k) q) := by
  intro u u' h
  have hm : pathMove q u = pathMove q u' := by
    simp only [pathMove, (subset_R_pathStep_iff q u).symm.trans (h ▸ subset_R_pathStep_iff q u')]
  simp only [pathStep, hm] at h
  exact ((pathTwoCopy s k).involutive _).injective h

/-- Off the first coordinate, a step is the shared transposition `S_q`. -/
private theorem pathStep_eq_permMap {q : Fin (s - 1)} {u : TwoCopyState (Fin s) k}
    (hx : u.x ∉ edgeSet (pathEdge s) q) : pathStep q u = u.permMap (adjSwap s q) := by
  unfold pathStep pathMove
  split_ifs with h
  · simp only [pathTwoCopy, twoCopyFamily_T_two, twoMove, dif_pos h]
    exact TwoCopyState.ext_iff'.2 ⟨(map_adjSwap_eq_self (Or.inl fun v hv => h hv)).symm,
      (adjSwap_apply_of_notMem hx).symm, rfl⟩
  · simp only [pathTwoCopy, twoCopyFamily_T_sh, shMove, edgeSwap_pathEdge]
    split_ifs with hc
    · rfl
    have hnone : ∀ v ∈ edgeSet (pathEdge s) q, v ∉ u.R := by
      intro v hv hvR
      have h₂ : #(edgeSet (pathEdge s) q) = 2 := by
        rw [edgeSet, card_pair (by simp [pathEdge, Fin.ext_iff])]
      have h₁ := card_pos.2 ⟨v, mem_inter.2 ⟨hvR, hv⟩⟩
      have hle := card_le_card (inter_subset_right (s₁ := u.R) (s₂ := edgeSet (pathEdge s) q))
      exact h (inter_eq_right.1 (eq_of_subset_of_card_le inter_subset_right (by lia)))
    exact TwoCopyState.ext_iff'.2 ⟨(map_adjSwap_eq_self (Or.inr hnone)).symm,
      (adjSwap_apply_of_notMem hx).symm,
      (adjSwap_apply_of_notMem fun hy => hnone _ hy u.y_mem).symm⟩

/-- On a red–red edge through the first coordinate, a step moves only the second one. -/
private theorem pathStep_of_subset {q : Fin (s - 1)} {u : TwoCopyState (Fin s) k}
    (h : edgeSet (pathEdge s) q ⊆ u.R) :
    (pathStep q u).R = u.R ∧ (pathStep q u).x = u.x ∧ (pathStep q u).y = adjSwap s q u.y := by
  simp [pathStep, pathMove, h, pathTwoCopy, twoMove]

/-! ### Walking along a list of edges -/

/-- The state reached from `u` by stepping along the edges of `l` in order. -/
private def runPath (l : List (Fin (s - 1))) (u : TwoCopyState (Fin s) k) :
    TwoCopyState (Fin s) k :=
  l.foldl (fun u q => pathStep q u) u

/-- The moves used when stepping along the edges of `l` from `u`. -/
private def pathMoves : List (Fin (s - 1)) → TwoCopyState (Fin s) k →
    List (TwoCopyMove (Fin (s - 1)))
  | [], _ => []
  | q :: l, u => pathMove q u :: pathMoves l (pathStep q u)

/-- The edge of a move. -/
private def moveEdge {ι : Type*} : TwoCopyMove ι → ι
  | .sh e => e
  | .one e => e
  | .two e => e

private theorem runPath_cons (q : Fin (s - 1)) (l : List (Fin (s - 1)))
    (u : TwoCopyState (Fin s) k) : runPath (q :: l) u = runPath l (pathStep q u) := rfl

private theorem runPath_append (l l' : List (Fin (s - 1))) (u : TwoCopyState (Fin s) k) :
    runPath (l ++ l') u = runPath l' (runPath l u) := by
  simp [runPath, List.foldl_append]

private theorem runPath_injective (l : List (Fin (s - 1))) :
    Function.Injective (runPath (k := k) l) := by
  induction l with
  | nil => exact fun _ _ h => h
  | cons q l ih => exact fun u u' h => pathStep_injective q (ih h)

private theorem foldl_pathMoves (l : List (Fin (s - 1))) (u : TwoCopyState (Fin s) k)
    (g : TwoCopyState (Fin s) k → TwoCopyState (Fin s) k) (v : TwoCopyState (Fin s) k)
    (hg : g v = u) :
    (pathMoves l u).foldl (fun g e => (pathTwoCopy s k).T e ∘ g) g v = runPath l u := by
  induction l generalizing u g with
  | nil => exact hg
  | cons q l ih =>
    exact ih (pathStep q u) _ (by simp only [Function.comp_apply, hg]; rfl)

private theorem length_pathMoves (l : List (Fin (s - 1))) (u : TwoCopyState (Fin s) k) :
    (pathMoves l u).length = l.length := by
  induction l generalizing u with
  | nil => rfl
  | cons q l ih => simp [pathMoves, ih]

private theorem take_pathMoves (l : List (Fin (s - 1))) (u : TwoCopyState (Fin s) k) (r : ℕ) :
    (pathMoves l u).take r = pathMoves (l.take r) u := by
  induction l generalizing u r with
  | nil => simp [pathMoves]
  | cons q l ih =>
    cases r with
    | zero => simp [pathMoves]
    | succ r => simp [pathMoves, ih]

private theorem getElem?_pathMoves (l : List (Fin (s - 1))) (u : TwoCopyState (Fin s) k)
    (r : ℕ) : (pathMoves l u)[r]?.map moveEdge = l[r]? := by
  induction l generalizing u r with
  | nil => simp [pathMoves]
  | cons q l ih =>
    cases r with
    | zero =>
      simp only [pathMoves, pathMove, List.getElem?_cons_zero, Option.map_some]
      split_ifs <;> rfl
    | succ r => simp [pathMoves, ih]

/-! ### Products of adjacent transpositions -/

/-- The product `τ_{q_n} ⋯ τ_{q_1}` of the transpositions along `l = [q_1, …, q_n]`. -/
private def pathPerm (l : List (Fin (s - 1))) : Equiv.Perm (Fin s) :=
  (l.map (adjSwap s)).reverse.prod

private theorem pathPerm_nil : pathPerm (s := s) [] = 1 := rfl

private theorem pathPerm_cons (q : Fin (s - 1)) (l : List (Fin (s - 1))) :
    pathPerm (q :: l) = pathPerm l * adjSwap s q := by
  simp [pathPerm, List.prod_append]

private theorem pathPerm_append_singleton (q : Fin (s - 1)) (l : List (Fin (s - 1))) :
    pathPerm (l ++ [q]) = adjSwap s q * pathPerm l := by
  simp [pathPerm]

private theorem pathPerm_reverse_apply (l : List (Fin (s - 1))) (v : Fin s) :
    pathPerm l.reverse (pathPerm l v) = v := by
  induction l generalizing v with
  | nil => rfl
  | cons q l ih =>
    rw [List.reverse_cons, pathPerm_append_singleton, pathPerm_cons, Equiv.Perm.mul_apply,
      Equiv.Perm.mul_apply, ih, adjSwap_adjSwap]

private theorem pathPerm_apply_of_forall_notMem {l : List (Fin (s - 1))} {v : Fin s}
    (h : ∀ q ∈ l, v ∉ edgeSet (pathEdge s) q) : pathPerm l v = v := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    rw [pathPerm_cons, Equiv.Perm.mul_apply, adjSwap_apply_of_notMem (h q (by simp)),
      ih fun q' hq' => h q' (by simp [hq'])]

/-- Along edges avoiding the first coordinate, every step is a shared transposition. -/
private theorem runPath_eq_permMap {l : List (Fin (s - 1))} {u : TwoCopyState (Fin s) k}
    (h : ∀ q ∈ l, u.x ∉ edgeSet (pathEdge s) q) : runPath l u = u.permMap (pathPerm l) := by
  induction l generalizing u with
  | nil => exact (permMap_one u).symm
  | cons q l ih =>
    rw [runPath_cons, pathStep_eq_permMap (h q (by simp)), ih, TwoCopyState.permMap_permMap,
      pathPerm_cons]
    intro q' hq'
    rw [TwoCopyState.x_permMap, adjSwap_apply_of_notMem (h q (by simp))]
    exact h q' (by simp [hq'])

private theorem runPath_x_of_forall_notMem {l : List (Fin (s - 1))} {u : TwoCopyState (Fin s) k}
    (h : ∀ q ∈ l, u.x ∉ edgeSet (pathEdge s) q) : (runPath l u).x = u.x := by
  rw [runPath_eq_permMap h, TwoCopyState.x_permMap, pathPerm_apply_of_forall_notMem h]

/-! ### Canonical edge sequences -/

/-- `E` is a canonical edge sequence from `a` to `b`: `E = F ++ m :: F.reverse`, where the edges of
`F` avoid `a` and are distinct, `m` is an edge at `a`, and `τ_F` carries `b` to the other endpoint
of `m`. -/
private def IsCanonical (a b : Fin s) (E : List (Fin (s - 1))) : Prop :=
  ∃ (F : List (Fin (s - 1))) (m : Fin (s - 1)), E = F ++ m :: F.reverse ∧ F.Nodup ∧
    (∀ q ∈ F, a ∉ edgeSet (pathEdge s) q) ∧ a ∈ edgeSet (pathEdge s) m ∧
    pathPerm F b = adjSwap s m a ∧ F.length < s

/-- The state after the forward phase and the middle step. -/
private theorem pathStep_runPath_forward {F : List (Fin (s - 1))} {m : Fin (s - 1)} {a b : Fin s}
    (hFa : ∀ q ∈ F, a ∉ edgeSet (pathEdge s) q) (hma : a ∈ edgeSet (pathEdge s) m)
    (hFb : pathPerm F b = adjSwap s m a) {u : TwoCopyState (Fin s) k} (hux : u.x = a)
    (huy : u.y = a) (hb : b ∈ u.R) :
    (pathStep m (runPath F u)).R = u.R.map (pathPerm F).toEmbedding ∧
      (pathStep m (runPath F u)).x = a ∧ (pathStep m (runPath F u)).y = pathPerm F b := by
  have hrun : runPath F u = u.permMap (pathPerm F) := runPath_eq_permMap (hux ▸ hFa)
  have hPa : pathPerm F a = a := pathPerm_apply_of_forall_notMem hFa
  have hsub : edgeSet (pathEdge s) m ⊆ (runPath F u).R := by
    intro v hv
    have hends : v = a ∨ v = adjSwap s m a := by
      rw [mem_edgeSet_pathEdge] at hv hma
      rw [Fin.ext_iff, Fin.ext_iff, adjSwap_val]
      split_ifs <;> lia
    rw [hrun, TwoCopyState.R_permMap]
    rcases hends with h | h <;> rw [h]
    · exact mem_map.2 ⟨a, hux ▸ u.x_mem, hPa⟩
    · exact mem_map.2 ⟨b, hb, hFb⟩
  obtain ⟨h1, h2, h3⟩ := pathStep_of_subset hsub
  rw [h1, h2, h3, hrun, TwoCopyState.R_permMap, TwoCopyState.x_permMap, TwoCopyState.y_permMap,
    hux, huy, hPa, hFb]
  exact ⟨rfl, rfl, rfl⟩

/-- A canonical edge sequence from `a` to `b` leads from `(R, a, a)` to `(R, a, b)`. -/
private theorem IsCanonical.endpoint {a b : Fin s} {E : List (Fin (s - 1))}
    (hE : IsCanonical a b E) {u : TwoCopyState (Fin s) k} (hux : u.x = a) (huy : u.y = a)
    (hb : b ∈ u.R) : (runPath E u).R = u.R ∧ (runPath E u).x = a ∧ (runPath E u).y = b := by
  obtain ⟨F, m, rfl, -, hFa, hma, hFb, -⟩ := hE
  obtain ⟨h1, h2, h3⟩ := pathStep_runPath_forward hFa hma hFb hux huy hb
  rw [runPath_append, runPath_cons]
  have hrev : ∀ q ∈ F.reverse, (pathStep m (runPath F u)).x ∉ edgeSet (pathEdge s) q :=
    fun q hq => h2 ▸ hFa q (List.mem_reverse.1 hq)
  rw [runPath_eq_permMap hrev, TwoCopyState.R_permMap, TwoCopyState.x_permMap,
    TwoCopyState.y_permMap, h1, h2, h3, pathPerm_reverse_apply]
  refine ⟨?_, ?_, rfl⟩
  · have : (pathPerm F).toEmbedding.trans (pathPerm F.reverse).toEmbedding =
        Function.Embedding.refl _ := by
      ext v
      simp [pathPerm_reverse_apply]
    rw [map_map, this, map_refl]
  · exact pathPerm_apply_of_forall_notMem fun q hq => hFa q (List.mem_reverse.1 hq)

/-- Along a canonical edge sequence from `a`, the first coordinate stays at `a`. -/
private theorem IsCanonical.runPath_take_x {a b : Fin s} {E : List (Fin (s - 1))}
    (hE : IsCanonical a b E) {u : TwoCopyState (Fin s) k} (hux : u.x = a) (huy : u.y = a)
    (hb : b ∈ u.R) (r : ℕ) : (runPath (E.take r) u).x = a := by
  obtain ⟨F, m, rfl, -, hFa, hma, hFb, -⟩ := hE
  rw [List.take_append]
  by_cases hr : r ≤ F.length
  · rw [Nat.sub_eq_zero_of_le hr, List.take_zero, List.append_nil, ← hux]
    exact runPath_x_of_forall_notMem fun q hq => hux ▸ hFa q (List.mem_of_mem_take hq)
  · obtain ⟨j, hj⟩ : ∃ j, r - F.length = j + 1 := ⟨r - F.length - 1, by lia⟩
    rw [List.take_of_length_le (by lia), hj, List.take_succ_cons, runPath_append,
      runPath_cons]
    obtain ⟨-, h2, -⟩ := pathStep_runPath_forward hFa hma hFb hux huy hb
    rw [← h2]
    refine runPath_x_of_forall_notMem fun q hq => ?_
    rw [h2]
    exact hFa q (List.mem_reverse.1 (List.mem_of_mem_take hq))

private theorem IsCanonical.length_le {a b : Fin s} {E : List (Fin (s - 1))}
    (hE : IsCanonical a b E) : E.length ≤ 2 * s := by
  obtain ⟨F, m, rfl, -, -, -, -, hF⟩ := hE
  grind

/-- Each edge occurs at most twice in a canonical edge sequence. -/
private theorem IsCanonical.card_filter_le_two {a b : Fin s} {E : List (Fin (s - 1))}
    (hE : IsCanonical a b E) (S : Finset ℕ) (q : Fin (s - 1)) :
    (S.filter fun r => E[r]? = some q).card ≤ 2 := by
  obtain ⟨F, m, rfl, hF, hFa, hma, -, -⟩ := hE
  have hmF : m ∉ F := fun h => hFa m h hma
  have hidx : ∀ i j : ℕ, F[i]? = some q → F[j]? = some q → i = j := fun i j hi hj => by
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hi
    obtain ⟨hj, h⟩ := List.getElem?_eq_some_iff.1 hj
    exact hF.getElem_inj_iff.1 h.symm
  have hback : ∀ r, F.length < r → (F ++ m :: F.reverse)[r]? = some q →
      F[2 * F.length - r]? = some q := by
    intro r h hr
    obtain ⟨j, hj⟩ : ∃ j, r - F.length = j + 1 := ⟨r - F.length - 1, by lia⟩
    rw [List.getElem?_append_right h.le, hj, List.getElem?_cons_succ] at hr
    have hjlt : j < F.length := by
      simpa using (List.getElem?_eq_some_iff.1 hr).1
    rw [List.getElem?_reverse hjlt] at hr
    rwa [show 2 * F.length - r = F.length - 1 - j by lia]
  by_cases hq : q ∈ F
  · obtain ⟨i, hi⟩ := List.getElem?_of_mem hq
    have hilt : i < F.length := (List.getElem?_eq_some_iff.1 hi).1
    refine (card_le_card fun r hr => ?_).trans (card_le_two (a := i) (b := 2 * F.length - i))
    obtain ⟨-, hr⟩ := mem_filter.1 hr
    rw [mem_insert, mem_singleton]
    rcases lt_trichotomy r F.length with h | rfl | h
    · rw [List.getElem?_append_left h] at hr
      exact .inl (hidx _ _ hr hi)
    · rw [List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero,
        Option.some_inj] at hr
      exact (hmF (hr ▸ hq)).elim
    · have := hidx _ _ (hback r h hr) hi
      have := (List.getElem?_eq_some_iff.1 hr).1
      grind
  · refine (card_le_card (t := {F.length}) fun r hr => ?_).trans (by simp)
    obtain ⟨-, hr⟩ := mem_filter.1 hr
    rcases lt_trichotomy r F.length with h | h | h
    · rw [List.getElem?_append_left h] at hr
      exact absurd (List.mem_of_getElem? hr) hq
    · exact mem_singleton.2 h
    · exact absurd (List.mem_of_getElem? (hback r h hr)) hq

private theorem exists_forward_lt : ∀ (n : ℕ) (a b : Fin s), (b : ℕ) = a + 1 + n →
    ∃ F : List (Fin (s - 1)), F.Nodup ∧ (∀ q ∈ F, (a : ℕ) < q ∧ (q : ℕ) < b) ∧
      F.length = n ∧ (pathPerm F b : ℕ) = a + 1
  | 0, a, b, h => ⟨[], List.nodup_nil, by simp, rfl, h⟩
  | n + 1, a, b, h => by
    obtain ⟨F, hF, hFq, hFl, hFb⟩ := exists_forward_lt n a ⟨b - 1, by lia⟩ (by grind)
    have hb : adjSwap s ⟨b - 1, by lia⟩ b = ⟨b - 1, by lia⟩ := by
      ext
      rw [adjSwap_val]
      grind
    refine ⟨⟨b - 1, by lia⟩ :: F, List.nodup_cons.2 ⟨fun hm => lt_irrefl _ (hFq _ hm).2, hF⟩,
      by grind, by simp [hFl], by rw [pathPerm_cons, Equiv.Perm.mul_apply, hb, hFb]⟩

private theorem exists_forward_gt : ∀ (n : ℕ) (a b : Fin s), (a : ℕ) = b + 1 + n →
    ∃ F : List (Fin (s - 1)), F.Nodup ∧ (∀ q ∈ F, (b : ℕ) ≤ q ∧ (q : ℕ) + 1 < a) ∧
      F.length = n ∧ (pathPerm F b : ℕ) = a - 1
  | 0, a, b, h =>
    ⟨[], List.nodup_nil, by simp, rfl, by rw [pathPerm_nil, Equiv.Perm.one_apply]; lia⟩
  | n + 1, a, b, h => by
    obtain ⟨F, hF, hFq, hFl, hFb⟩ := exists_forward_gt n a ⟨b + 1, by lia⟩ (by grind)
    have hb : adjSwap s ⟨b, by lia⟩ b = ⟨b + 1, by lia⟩ := by
      ext
      rw [adjSwap_val]
      simp
    refine ⟨⟨b, by lia⟩ :: F, List.nodup_cons.2 ⟨fun hm => by grind, hF⟩, by grind,
      by simp [hFl], by rw [pathPerm_cons, Equiv.Perm.mul_apply, hb, hFb]⟩

private theorem exists_isCanonical {a b : Fin s} (hab : a ≠ b) : ∃ E, IsCanonical a b E := by
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
  · obtain ⟨F, hF, hFq, hFl, hFb⟩ := exists_forward_lt (b - a - 1) a b (by lia)
    refine ⟨_, F, ⟨a, by lia⟩, rfl, hF, fun q hq => ?_, by simp [mem_edgeSet_pathEdge], ?_,
      by lia⟩
    · rw [mem_edgeSet_pathEdge]
      grind
    · ext
      rw [hFb, adjSwap_val]
      simp
  · obtain ⟨F, hF, hFq, hFl, hFb⟩ := exists_forward_gt (a - b - 1) a b (by lia)
    refine ⟨_, F, ⟨a - 1, by lia⟩, rfl, hF, fun q hq => ?_, ?_, ?_, by lia⟩
    · rw [mem_edgeSet_pathEdge]
      grind
    · rw [mem_edgeSet_pathEdge]
      grind
    · ext
      rw [hFb, adjSwap_val]
      grind

/-! ### The canonical paths -/

/-- **Canonical paths between sectors.** Each `(R, x, y) ∈ Ω^p_{s,k}` with `x ≠ y` is joined to
`(R, x, x)` by a word `θ_1, …, θ_L` in `𝒯^p_{s,k}` of length `L ≤ 2s`, such that each pair `(θ, z)`
of a move and a state occurs as `(θ_r, θ_{r-1} ∘ ⋯ ∘ θ_1 (R, x, x))` for at most `2s` pairs
`((R, x, y), r)`. -/
@[cycle_cutoff "lem_canonical_paths"]
theorem exists_pathTwoCopy_canonical_paths (s k : ℕ) :
    ∃ γ : TwoCopyState (Fin s) k → List (TwoCopyMove (Fin (s - 1))),
      (∀ w : TwoCopyState (Fin s) k, w.x ≠ w.y → (γ w).length ≤ 2 * s ∧
        (γ w).foldl (fun g e => (pathTwoCopy s k).T e ∘ g) id w.diag = w) ∧
      ∀ (θ : TwoCopyMove (Fin (s - 1))) (z : TwoCopyState (Fin s) k),
        ∑ w : TwoCopyState (Fin s) k with w.x ≠ w.y,
          ((range (γ w).length).filter fun r => (γ w)[r]? = some θ ∧
            ((γ w).take r).foldl (fun g e => (pathTwoCopy s k).T e ∘ g) id w.diag = z).card ≤
          2 * s := by
  have key : ∀ a b : Fin s, ∃ E : List (Fin (s - 1)), a ≠ b → IsCanonical a b E := fun a b =>
    if h : a = b then ⟨[], (absurd h ·)⟩ else (exists_isCanonical h).imp fun _ hE _ => hE
  choose E hE using key
  refine ⟨fun w => pathMoves (E w.x w.y) w.diag, fun w hw => ?_, fun θ z => ?_⟩
  · rw [length_pathMoves, foldl_pathMoves _ w.diag id w.diag rfl]
    exact ⟨(hE _ _ hw).length_le,
      TwoCopyState.ext_iff'.2 ((hE _ _ hw).endpoint (u := w.diag) rfl rfl w.y_mem)⟩
  set P := ((univ : Finset (TwoCopyState (Fin s) k)).filter fun w => w.x ≠ w.y).sigma
    fun w => (range (pathMoves (E w.x w.y) w.diag).length).filter fun r =>
      (pathMoves (E w.x w.y) w.diag)[r]? = some θ ∧
        ((pathMoves (E w.x w.y) w.diag).take r).foldl
          (fun g e => (pathTwoCopy s k).T e ∘ g) id w.diag = z with hP
  have hmem : ∀ p ∈ P, p.1.x ≠ p.1.y ∧ p.2 < (E p.1.x p.1.y).length ∧
      (E p.1.x p.1.y)[p.2]? = some (moveEdge θ) ∧
      runPath ((E p.1.x p.1.y).take p.2) p.1.diag = z ∧ p.1.x = z.x := by
    intro p hp
    rw [hP, mem_sigma, mem_filter, mem_filter, mem_range, length_pathMoves, take_pathMoves,
      foldl_pathMoves _ p.1.diag id p.1.diag rfl] at hp
    obtain ⟨⟨-, hxy⟩, hlt, hθ, hz⟩ := hp
    refine ⟨hxy, hlt, by rw [← getElem?_pathMoves _ p.1.diag, hθ]; rfl, hz, ?_⟩
    rw [← hz]
    exact ((hE _ _ hxy).runPath_take_x (u := p.1.diag) rfl rfl p.1.y_mem _).symm
  calc ∑ w : TwoCopyState (Fin s) k with w.x ≠ w.y, _ = P.card := (card_sigma _ _).symm
    _ ≤ (((univ : Finset (Fin s)).filter (· ≠ z.x)).sigma fun y =>
          (range (E z.x y).length).filter fun r => (E z.x y)[r]? = some (moveEdge θ)).card := by
      refine card_le_card_of_injOn (fun p => ⟨p.1.y, p.2⟩) (fun p hp => ?_) ?_
      · obtain ⟨hxy, hlt, hθ, -, hx⟩ := hmem p hp
        rw [hx] at hxy hlt hθ
        simp only [coe_sigma, Set.mem_sigma_iff, coe_filter, mem_univ, true_and, mem_range]
        exact ⟨Ne.symm hxy, hlt, hθ⟩
      · intro p hp p' hp' hpp
        obtain ⟨-, -, -, hz, hx⟩ := hmem p hp
        obtain ⟨-, -, -, hz', hx'⟩ := hmem p' hp'
        obtain ⟨hy, hr⟩ := Sigma.mk.inj_iff.1 hpp
        have hxx := hx.trans hx'.symm
        rw [hxx, hy, eq_of_heq hr] at hz
        have hR := congrArg TwoCopyState.R (runPath_injective _ (hz.trans hz'.symm))
        exact Sigma.ext (TwoCopyState.ext_iff'.2 ⟨hR, hxx, hy⟩) hr
    _ = ∑ y ∈ (univ : Finset (Fin s)).filter (· ≠ z.x),
          ((range (E z.x y).length).filter fun r => (E z.x y)[r]? = some (moveEdge θ)).card :=
      card_sigma _ _
    _ ≤ ∑ _y ∈ (univ : Finset (Fin s)).filter (· ≠ z.x), 2 :=
      sum_le_sum fun y hy => (hE _ _ (mem_filter.1 hy).2.symm).card_filter_le_two _ _
    _ ≤ 2 * s := by
      rw [sum_const, smul_eq_mul, mul_comm]
      exact Nat.mul_le_mul_left 2 ((card_filter_le _ _).trans (by simp))

end CycleCutoff
