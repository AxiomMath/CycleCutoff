/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Generator.Defs

/-!
# Symmetry of the semigroup of an involution family

For an involution family `𝒯` and every `t`, `P^𝒯_t(z, w) = P^𝒯_t(w, z)`: the rate matrix `Q_𝒯` is
symmetric, and so is every `P^𝒯_t = exp(t Q_𝒯)`.

## Main results

* `CycleCutoff.semigroup_transpose`: `(P^Q_t)ᵀ = P^{Qᵀ}_t` for any real square matrix `Q`.
* `Matrix.IsSymm.semigroup`: the semigroup of a symmetric matrix is symmetric.
* `CycleCutoff.InvFamily.isSymm_rateMatrix`, `CycleCutoff.InvFamily.rateMatrix_transpose`:
  `Q_𝒯ᵀ = Q_𝒯`.
* `CycleCutoff.InvFamily.semigroup_apply_comm`: `P^𝒯_t(z, w) = P^𝒯_t(w, z)`.
-/

public section

open Matrix

namespace CycleCutoff

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Transposition commutes with the semigroup: `(P^Q_t)ᵀ = P^{Qᵀ}_t`. -/
theorem semigroup_transpose (Q : Matrix Ω Ω ℝ) (t : ℝ) :
    (semigroup Q t)ᵀ = semigroup Qᵀ t := by
  rw [semigroup, semigroup, ← Matrix.exp_transpose, transpose_smul]

/-- The semigroup of a symmetric matrix is symmetric. -/
theorem _root_.Matrix.IsSymm.semigroup {Q : Matrix Ω Ω ℝ} (hQ : Q.IsSymm) (t : ℝ) :
    (semigroup Q t).IsSymm := by
  rw [IsSymm, semigroup_transpose, hQ.eq]

namespace InvFamily

variable {ι : Type*} [Fintype ι] (𝒯 : InvFamily ι Ω)

omit [Fintype Ω] in
/-- The rate matrix of an involution family is symmetric. -/
theorem isSymm_rateMatrix : 𝒯.rateMatrix.IsSymm := by
  ext z w
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [𝒯.T_eq_iff e w z, eq_comm (a := w) (b := z)]

omit [Fintype Ω] in
/-- The rate matrix of an involution family equals its transpose. -/
theorem rateMatrix_transpose : 𝒯.rateMatrixᵀ = 𝒯.rateMatrix :=
  𝒯.isSymm_rateMatrix.eq

/-- The semigroup of an involution family is symmetric. -/
theorem isSymm_semigroup (t : ℝ) : (𝒯.semigroup t).IsSymm :=
  𝒯.isSymm_rateMatrix.semigroup t

/-- **Symmetry of the semigroup**: `P^𝒯_t(z, w) = P^𝒯_t(w, z)`. -/
@[cycle_cutoff "lem_semigroup_symmetric"]
theorem semigroup_apply_comm (t : ℝ) (z w : Ω) :
    𝒯.semigroup t z w = 𝒯.semigroup t w z :=
  (𝒯.isSymm_semigroup t).apply w z

end InvFamily

end CycleCutoff
