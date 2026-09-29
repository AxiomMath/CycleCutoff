/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.PathShuffle.Defs
public import CycleCutoff.Generator.CanonicalPath

/-!
# Comparison of transpositions with adjacent transpositions

For `f : 𝔖_N → ℝ`, the total uniform mean-square change of `f` under all transpositions
`σ ↦ τ_{i,j} ∘ σ` is at most `4 N³` times the total change under the adjacent transpositions
`σ ↦ τ_j ∘ σ`:
`∑_{i<j} 𝔼_u[(f(τ_{i,j} σ) - f σ)²] ≤ 4 N³ ∑_j 𝔼_u[(f(τ_j σ) - f σ)²]`.
Indices are `0`-based: `τ_{i,j}` is `Equiv.swap i j` for `i < j` in `Fin N`, and `τ_j` is
`adjSwap N j` for `j : Fin (N - 1)`.

## Main results

* `CycleCutoff.sum_expectation_swap_sq_le`: the comparison above.
-/

public section

open Finset

namespace CycleCutoff

/-- A left fold of compositions started at `h` is the fold started at `id`, composed with `h`. -/
private theorem foldl_comp_eq_foldl_id_comp {ι Ω : Type*} (F : ι → Ω → Ω) (l : List ι)
    (h : Ω → Ω) :
    l.foldl (fun g e => F e ∘ g) h = l.foldl (fun g e => F e ∘ g) id ∘ h := by
  induction l generalizing h with
  | nil => rfl
  | cons e l ih =>
    simp only [List.foldl_cons]
    rw [ih, ih (F e ∘ id)]
    rfl

/-- The transposition `τ_{i,j}` with `j = i + d + 1` is the palindromic path of at most
`2d + 1` adjacent transpositions, each `τ_l` occurring at most twice and only for `i ≤ l`. -/
private theorem exists_adjSwap_path (N : ℕ) (E : Fin (N - 1) → ℝ) (hE : ∀ l, 0 ≤ E l) :
    ∀ (d : ℕ) (i j : Fin N), (j : ℕ) = i + d + 1 →
      ∃ es : List (Fin (N - 1)), es.length ≤ 2 * d + 1 ∧
        (∀ σ, es.foldl (fun g e => (pathShuffle N).T e ∘ g) id σ = Equiv.swap i j * σ) ∧
        (es.map E).sum ≤ 2 * ∑ l ∈ univ.filter (fun l : Fin (N - 1) => (i : ℕ) ≤ l), E l := by
  intro d
  induction d with
  | zero =>
    intro i j hij
    have hi : (i : ℕ) < N - 1 := by omega
    refine ⟨[⟨i, hi⟩], by simp, fun σ => ?_, ?_⟩
    · have hj : (⟨i + 1, by omega⟩ : Fin N) = j := Fin.ext (by simp [hij])
      simp only [List.foldl_cons, List.foldl_nil, Function.comp_apply, id, pathShuffle_T]
      rw [← hj]
      rfl
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have h1 : E ⟨i, hi⟩ ≤ ∑ l ∈ univ.filter (fun l : Fin (N - 1) => (i : ℕ) ≤ l), E l :=
        single_le_sum (f := E) (fun l _ => hE l) (by simp)
      linarith [hE ⟨i, hi⟩]
  | succ d ih =>
    intro i j hij
    have hi : (i : ℕ) < N - 1 := by omega
    set i' : Fin N := ⟨i + 1, by omega⟩
    obtain ⟨es, hlen, hfold, hsum⟩ := ih i' j (by simp [i']; omega)
    refine ⟨⟨i, hi⟩ :: es ++ [⟨i, hi⟩], by simp; omega, fun σ => ?_, ?_⟩
    · rw [List.cons_append, List.foldl_cons, List.foldl_append, foldl_comp_eq_foldl_id_comp _ es]
      simp only [List.foldl_cons, List.foldl_nil, Function.comp_apply, id, hfold, pathShuffle_T]
      have hs : adjSwap N ⟨i, hi⟩ = Equiv.swap i i' := rfl
      have hji : j ≠ i := fun h => by rw [h] at hij; omega
      have hji' : j ≠ i' := fun h => by rw [h] at hij; simp [i'] at hij
      have key := Equiv.swap_apply_apply (Equiv.swap i i') i' j
      rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hji hji', Equiv.swap_inv] at key
      rw [hs, key]
      simp only [mul_assoc]
    · have hsplit : (univ.filter fun l : Fin (N - 1) => (i : ℕ) ≤ l) =
          insert ⟨i, hi⟩ (univ.filter fun l : Fin (N - 1) => (i' : ℕ) ≤ l) := by
        ext l
        simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff, i']
        omega
      rw [hsplit, sum_insert (by simp [i'])]
      simp only [List.map_cons, List.map_append, List.map_nil, List.sum_cons, List.sum_append,
        List.sum_nil, add_zero]
      linarith

/-- **Comparison of transpositions.** For `f : 𝔖_N → ℝ`,
`∑_{i<j} 𝔼_u[(f(τ_{i,j} σ) - f σ)²] ≤ 4 N³ ∑_j 𝔼_u[(f(τ_j σ) - f σ)²]`. -/
@[cycle_cutoff "lem_transposition_comparison"]
theorem sum_expectation_swap_sq_le (N : ℕ) (f : Equiv.Perm (Fin N) → ℝ) :
    ∑ i : Fin N, ∑ j : Fin N with i < j,
        expectation (unif (Equiv.Perm (Fin N))) (fun σ => (f (Equiv.swap i j * σ) - f σ) ^ 2) ≤
      4 * (N : ℝ) ^ 3 * ∑ j : Fin (N - 1),
        expectation (unif (Equiv.Perm (Fin N)))
          (fun σ => (f ((pathShuffle N).T j σ) - f σ) ^ 2) := by
  set E : Fin (N - 1) → ℝ := fun l => expectation (unif (Equiv.Perm (Fin N)))
    (fun σ => (f ((pathShuffle N).T l σ) - f σ) ^ 2)
  have hu : ∀ σ, 0 ≤ unif (Equiv.Perm (Fin N)) σ := fun σ => by simp [unif_apply]
  have hE : ∀ l, 0 ≤ E l := fun l => expectation_nonneg hu fun σ => sq_nonneg _
  have hS : 0 ≤ ∑ l, E l := sum_nonneg fun l _ => hE l
  have key : ∀ i j : Fin N, i < j →
      expectation (unif (Equiv.Perm (Fin N))) (fun σ => (f (Equiv.swap i j * σ) - f σ) ^ 2) ≤
        4 * N * ∑ l, E l := by
    intro i j hij
    have hij' := Fin.lt_def.1 hij
    obtain ⟨es, hlen, hfold, hsum⟩ := exists_adjSwap_path N E hE (j - i - 1) i j (by omega)
    have h1 := (pathShuffle N).expectation_sq_foldl_sub_le es f
    simp only [hfold] at h1
    have h2 : (es.map E).sum ≤ 2 * ∑ l, E l :=
      hsum.trans <| mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun l _ _ => hE l) (by norm_num)
    have h3 : (es.length : ℝ) ≤ 2 * N := by exact_mod_cast hlen.trans (by omega)
    have h4 : 0 ≤ (es.map E).sum := List.sum_nonneg (by simpa using fun l _ => hE l)
    exact h1.trans ((mul_le_mul h3 h2 h4 (by positivity)).trans_eq (by ring))
  calc ∑ i : Fin N, ∑ j : Fin N with i < j,
        expectation (unif (Equiv.Perm (Fin N))) (fun σ => (f (Equiv.swap i j * σ) - f σ) ^ 2)
      ≤ ∑ _i : Fin N, ∑ _j : Fin N, 4 * N * ∑ l, E l := by
        gcongr with i
        calc _ ≤ ∑ j : Fin N with i < j, 4 * N * ∑ l, E l :=
              sum_le_sum fun j hj => key i j (mem_filter.1 hj).2
          _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
              fun _ _ _ => by positivity
    _ = 4 * (N : ℝ) ^ 3 * ∑ l, E l := by simp; ring

end CycleCutoff
