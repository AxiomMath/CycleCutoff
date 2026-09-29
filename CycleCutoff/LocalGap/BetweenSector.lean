/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.LocalGap.CanonicalPaths
public import CycleCutoff.Generator.DirichletFormula
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Between-sector variance

Let `D : Ω^p_{s,k} → Bool` record whether a state `(R, x, y)` lies on the diagonal `x = y`. The
conditional expectation `𝔼_ν[f ∣ D]` is constant on the diagonal sector and on the off-diagonal
sector, and its variance is bounded by the Dirichlet form of the two-copy path chain:
`Var_ν(𝔼_ν[f ∣ D]) ≤ 8 s² 𝒟^p_{s,k}(f)`.

## Main results

* `CycleCutoff.InvFamily.sq_foldl_sub_le`: the telescoping bound along a path.
* `CycleCutoff.TwoCopyState.sum_offDiag_diag`: each diagonal state is the diagonal of `m - 1`
  off-diagonal states.
* `CycleCutoff.variance_condExp_diag_le`: `Var_ν(𝔼_ν[f ∣ D]) ≤ 8 s² 𝒟^p_{s,k}(f)`.

## Implementation notes

* `D` is `fun w => decide (w.x = w.y)`, valued in `Bool`.
* No hypothesis on `s` or `k` is assumed: for `k > s` the state space is empty and both sides
  vanish.
-/

public section

open Finset

namespace CycleCutoff

/-! ### Telescoping along a path -/

namespace InvFamily

variable {ι Ω : Type*} (𝒯 : InvFamily ι Ω)

/-- Appending one step to a path: the state after `r + 1` steps is `T_{e_r}` of the state after `r`
steps. -/
theorem foldl_take_add_one (es : List ι) (z₀ : Ω) {r : ℕ} (hr : r < es.length) :
    (es.take (r + 1)).foldl (fun g e => 𝒯.T e ∘ g) id z₀ =
      𝒯.T es[r] ((es.take r).foldl (fun g e => 𝒯.T e ∘ g) id z₀) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hr, List.foldl_append]
  rfl

/-- Telescoping bound along a path: moving from `z₀` along `T_{e_L} ∘ ⋯ ∘ T_{e₁}` changes `f` by at
most `L` times the sum of the squared single-step changes,
`(f(z_L) - f(z₀))² ≤ L ∑_{r < L} (f(z_{r+1}) - f(z_r))²`, with `z_r` the state after `r` steps. -/
theorem sq_foldl_sub_le (es : List ι) (z₀ : Ω) (f : Ω → ℝ) :
    (f (es.foldl (fun g e => 𝒯.T e ∘ g) id z₀) - f z₀) ^ 2 ≤
      es.length * ∑ r ∈ range es.length,
        (f ((es.take (r + 1)).foldl (fun g e => 𝒯.T e ∘ g) id z₀) -
          f ((es.take r).foldl (fun g e => 𝒯.T e ∘ g) id z₀)) ^ 2 := by
  have h := sum_range_sub (fun r => f ((es.take r).foldl (fun g e => 𝒯.T e ∘ g) id z₀))
    es.length
  simp only [List.take_length, List.take_zero, List.foldl_nil, id_eq] at h
  rw [← h]
  simpa using sq_sum_le_card_mul_sum_sq (s := range es.length)
    (f := fun r => f ((es.take (r + 1)).foldl (fun g e => 𝒯.T e ∘ g) id z₀) -
      f ((es.take r).foldl (fun g e => 𝒯.T e ∘ g) id z₀))

end InvFamily

/-! ### Diagonal states and their off-diagonal partners -/

namespace TwoCopyState

variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

/-- A diagonal state `u = (R, x, x)` is the diagonal of exactly `m - 1` off-diagonal states, the
`(R, x, y)` with `y ∈ R \ {x}`. -/
theorem card_filter_diag_eq {u : TwoCopyState V m} (hu : u.x = u.y) :
    #{w ∈ univ.filter (fun w : TwoCopyState V m => w.x ≠ w.y) | w.diag = u} = m - 1 := by
  have hc : #(u.R.erase u.x) = m - 1 := by rw [card_erase_of_mem u.x_mem, u.card_R]
  rw [← hc]
  refine card_bij (fun w _ => w.y) (fun w hw => ?_) (fun w hw w' hw' h => ?_) (fun y hy => ?_)
  · simp only [mem_filter, mem_univ, true_and] at hw
    obtain ⟨hxy, rfl⟩ := hw
    exact mem_erase.2 ⟨Ne.symm hxy, w.y_mem⟩
  · simp only [mem_filter, mem_univ, true_and] at hw hw'
    obtain ⟨-, rfl⟩ := hw
    rw [TwoCopyState.ext_iff'] at hw' ⊢
    exact ⟨hw'.2.1.symm, hw'.2.2.1.symm, h⟩
  · refine ⟨⟨(u.R, u.x, y), u.card_R, u.x_mem, mem_of_mem_erase hy⟩, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and, TwoCopyState.ext_iff']
    exact ⟨(ne_of_mem_erase hy).symm, rfl, rfl, hu⟩

/-- Summing a function of the diagonal `w.diag` over the off-diagonal states `w` counts each
diagonal state `m - 1` times. -/
theorem sum_offDiag_diag {M : Type*} [AddCommMonoid M] (F : TwoCopyState V m → M) :
    ∑ w : TwoCopyState V m with w.x ≠ w.y, F w.diag =
      (m - 1) • ∑ u : TwoCopyState V m with u.x = u.y, F u := by
  rw [← sum_fiberwise_of_maps_to (g := TwoCopyState.diag)
    (t := univ.filter fun u : TwoCopyState V m => u.x = u.y) (fun w _ => by simp), smul_sum]
  refine sum_congr rfl fun u hu => ?_
  rw [sum_congr rfl (g := fun _ => F u) (fun w hw => by rw [(mem_filter.1 hw).2]), sum_const,
    card_filter_diag_eq (mem_filter.1 hu).2]

end TwoCopyState

/-! ### The between-sector bound -/

/-- **Between-sector variance.** With `D(R, x, y) = 1[x = y]`,
`Var_ν(𝔼_ν[f ∣ D]) ≤ 8 s² 𝒟^p_{s,k}(f)`. -/
@[cycle_cutoff "lem_between_sector"]
theorem variance_condExp_diag_le (s k : ℕ) (f : TwoCopyState (Fin s) k → ℝ) :
    variance (unif (TwoCopyState (Fin s) k))
        (condExp (unif (TwoCopyState (Fin s) k)) (fun w => decide (w.x = w.y)) f) ≤
      8 * (s : ℝ) ^ 2 * (pathTwoCopy s k).dirichletForm f := by
  set 𝒯 := pathTwoCopy s k
  set n : ℝ := (Fintype.card (TwoCopyState (Fin s) k) : ℝ) with hn_def
  set H : TwoCopyMove (Fin (s - 1)) → TwoCopyState (Fin s) k → ℝ :=
    fun θ z => (f (𝒯.T θ z) - f z) ^ 2 with hH_def
  have hH : ∀ θ z, 0 ≤ H θ z := fun θ z => sq_nonneg _
  set M := ∑ θ, ∑ z, H θ z with hM_def
  have hD : 𝒯.dirichletForm f = M / (2 * n) := by
    rw [InvFamily.dirichletForm_eq]
    simp only [expectation_unif, ← mul_sum, hM_def, hH_def]
    rw [← hn_def]
    ring
  set Q := ∑ w : TwoCopyState (Fin s) k with w.x ≠ w.y, (f w.diag - f w) ^ 2
  have hQ : Q ≤ 4 * (s : ℝ) ^ 2 * M := by
    obtain ⟨γ, hγ, hcong⟩ := exists_pathTwoCopy_canonical_paths s k
    have hstep : ∀ w : TwoCopyState (Fin s) k, ∀ r ∈ range (γ w).length,
        (f (((γ w).take (r + 1)).foldl (fun g e => 𝒯.T e ∘ g) id w.diag) -
          f (((γ w).take r).foldl (fun g e => 𝒯.T e ∘ g) id w.diag)) ^ 2 =
        ∑ θ, ∑ z, if (γ w)[r]? = some θ ∧
          ((γ w).take r).foldl (fun g e => 𝒯.T e ∘ g) id w.diag = z then H θ z else 0 := by
      intro w r hr
      rw [𝒯.foldl_take_add_one _ _ (mem_range.1 hr), List.getElem?_eq_getElem (mem_range.1 hr)]
      simp [ite_and, hH_def]
    have hpt : ∀ w : TwoCopyState (Fin s) k, w.x ≠ w.y → (f w.diag - f w) ^ 2 ≤
        2 * s * ∑ θ, ∑ z, H θ z * (((range (γ w).length).filter fun r => (γ w)[r]? = some θ ∧
          ((γ w).take r).foldl (fun g e => 𝒯.T e ∘ g) id w.diag = z).card : ℝ) := by
      intro w hw
      obtain ⟨hlen, hend⟩ := hγ w hw
      have h1 := 𝒯.sq_foldl_sub_le (γ w) w.diag f
      rw [hend, sum_congr rfl (hstep w)] at h1
      have h2 : ∑ θ, ∑ z, H θ z * (((range (γ w).length).filter fun r => (γ w)[r]? = some θ ∧
          ((γ w).take r).foldl (fun g e => 𝒯.T e ∘ g) id w.diag = z).card : ℝ) =
          ∑ r ∈ range (γ w).length, ∑ θ, ∑ z, if (γ w)[r]? = some θ ∧
            ((γ w).take r).foldl (fun g e => 𝒯.T e ∘ g) id w.diag = z then H θ z else 0 := by
        simp only [natCast_card_filter, mul_sum, mul_ite, mul_one, mul_zero]
        exact (sum_comm.trans (sum_congr rfl fun _ _ => sum_comm)).symm
      rw [h2, ← neg_sub, neg_sq]
      exact h1.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) (sum_nonneg
        fun r _ => sum_nonneg fun θ _ => sum_nonneg fun z _ => ite_nonneg (hH θ z) le_rfl))
    calc Q ≤ ∑ w : TwoCopyState (Fin s) k with w.x ≠ w.y, 2 * (s : ℝ) * ∑ θ, ∑ z, H θ z *
          (((range (γ w).length).filter fun r => (γ w)[r]? = some θ ∧
            ((γ w).take r).foldl (fun g e => 𝒯.T e ∘ g) id w.diag = z).card : ℝ) :=
          sum_le_sum fun w hw => hpt w (mem_filter.1 hw).2
      _ = 2 * (s : ℝ) * ∑ θ, ∑ z, H θ z *
          ((∑ w : TwoCopyState (Fin s) k with w.x ≠ w.y,
            ((range (γ w).length).filter fun r => (γ w)[r]? = some θ ∧
              ((γ w).take r).foldl (fun g e => 𝒯.T e ∘ g) id w.diag = z).card : ℕ) : ℝ) := by
          simp only [Nat.cast_sum, mul_sum]
          exact sum_comm.trans (sum_congr rfl fun _ _ => sum_comm)
      _ ≤ 2 * (s : ℝ) * ∑ θ, ∑ z, H θ z * (2 * s) := by
          gcongr with θ _ z _
          exact_mod_cast hcong θ z
      _ = 4 * (s : ℝ) ^ 2 * M := by
          simp only [hM_def, ← sum_mul]
          ring
  have hQ0 : 0 ≤ Q := sum_nonneg fun w _ => sq_nonneg _
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  rcases hn0.eq_or_lt with h0 | hpos
  · rw [hD, ← h0]
    simp [variance, expectation_def, unif_apply, ← hn_def, ← h0]
  set A := univ.filter fun w : TwoCopyState (Fin s) k => w.x = w.y with hA
  set B := univ.filter fun w : TwoCopyState (Fin s) k => w.x ≠ w.y with hB
  set nA : ℝ := (#A : ℝ) with hnA
  set nB : ℝ := (#B : ℝ) with hnB
  set a₁ := (∑ w ∈ A, f w) / nA with ha₁
  set a₀ := (∑ w ∈ B, f w) / nB with ha₀
  have hnAB : nA + nB = n := by
    rw [hnA, hnB, hn_def, hA, hB]
    exact_mod_cast (card_filter_add_card_filter_not _).trans card_univ
  have hnA0 : 0 ≤ nA := Nat.cast_nonneg _
  have hnB0 : 0 ≤ nB := Nat.cast_nonneg _
  have hg : ∀ z, condExp (unif (TwoCopyState (Fin s) k)) (fun w => decide (w.x = w.y)) f z =
      if z.x = z.y then a₁ else a₀ := by
    intro z
    have hn : n⁻¹ ≠ 0 := inv_ne_zero hpos.ne'
    rw [condExp_apply]
    by_cases hz : z.x = z.y
    · have hfib : fiber (fun w : TwoCopyState (Fin s) k => decide (w.x = w.y)) z = A := by
        ext
        simp [mem_fiber, hA, hz]
      simp only [if_pos hz, hfib, mass, unif_apply, ← hn_def, ← mul_sum, sum_const, nsmul_eq_mul]
      rw [mul_comm (#A : ℝ), mul_div_mul_left _ _ hn]
    · have hfib : fiber (fun w : TwoCopyState (Fin s) k => decide (w.x = w.y)) z = B := by
        ext
        simp [mem_fiber, hB, hz]
      simp only [if_neg hz, hfib, mass, unif_apply, ← hn_def, ← mul_sum, sum_const, nsmul_eq_mul]
      rw [mul_comm (#B : ℝ), mul_div_mul_left _ _ hn]
  have hsplit : ∀ F : ℝ → ℝ, ∑ z : TwoCopyState (Fin s) k, F (if z.x = z.y then a₁ else a₀) =
      nA * F a₁ + nB * F a₀ := fun F => by
    simp only [apply_ite F, sum_ite, sum_const, nsmul_eq_mul]
    rfl
  have hvar : n * variance (unif (TwoCopyState (Fin s) k))
      (condExp (unif (TwoCopyState (Fin s) k)) (fun w => decide (w.x = w.y)) f) =
      nA * nB * (a₁ - a₀) ^ 2 / n := by
    simp only [variance, expectation_unif, hg, ← hn_def, hsplit fun x => x,
      hsplit fun x => (x - n⁻¹ * (nA * a₁ + nB * a₀)) ^ 2]
    rw [← hnAB] at hpos ⊢
    field_simp
    ring
  have hcount : nB = ((k - 1 : ℕ) : ℝ) * nA := by
    have := TwoCopyState.sum_offDiag_diag (V := Fin s) (m := k) (M := ℕ) fun _ => 1
    simp only [sum_const, smul_eq_mul, mul_one] at this
    rw [hnB, hnA, hB, this]
    push_cast
    rfl
  have hdiag := TwoCopyState.sum_offDiag_diag (V := Fin s) (m := k) f
  rw [nsmul_eq_mul] at hdiag
  have hkey : nB * (a₁ - a₀) ^ 2 ≤ Q := by
    rcases hnB0.eq_or_lt with hB0 | hBpos
    · simpa [← hB0] using hQ0
    have hJ : (∑ w ∈ B, (f w.diag - f w)) ^ 2 ≤ nB * Q := sq_sum_le_card_mul_sum_sq
    rw [hcount] at hBpos
    have hApos : 0 < nA := pos_of_mul_pos_right hBpos (Nat.cast_nonneg _)
    have hc : ((k - 1 : ℕ) : ℝ) ≠ 0 := (pos_of_mul_pos_left hBpos hnA0).ne'
    have hsum : ∑ w ∈ B, (f w.diag - f w) = nB * (a₁ - a₀) := by
      rw [sum_sub_distrib, hB, hdiag, ← hB, ← hA, ha₁, ha₀, hcount]
      field_simp
    rw [hsum] at hJ
    nlinarith
  have hVQ : variance (unif (TwoCopyState (Fin s) k))
      (condExp (unif (TwoCopyState (Fin s) k)) (fun w => decide (w.x = w.y)) f) ≤ Q / n := by
    rw [le_div_iff₀ hpos, mul_comm, hvar, div_le_iff₀ hpos]
    have : nA * nB * (a₁ - a₀) ^ 2 ≤ n * (nB * (a₁ - a₀) ^ 2) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hnB0 (sq_nonneg _))
    nlinarith
  rw [hD]
  calc _ ≤ Q / n := hVQ
    _ ≤ 4 * (s : ℝ) ^ 2 * M / n := div_le_div_of_nonneg_right hQ hpos.le
    _ = 8 * (s : ℝ) ^ 2 * (M / (2 * n)) := by
      field_simp
      ring

end CycleCutoff
