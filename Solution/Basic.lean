/-
Copyright (c) 2026 Colin Defant. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import CycleCutoff.Cutoff.Main

/-! # Satisfying the formal challenge -/

@[expose] public section

namespace CycleCutoff.Challenge

/-- **`thm_main` — cutoff for the adjacent transposition shuffle on the cycle.** There is an
absolute constant `C > 0` such that for every `ε ∈ (0, 1)` there is `C_ε > 0` with
`t_n - C_ε n² ≤ t_mix^{(n)}(ε) ≤ t_n + C n² log log n + C_ε n²` for all sufficiently large
`n`. -/
theorem thm_main :
    ∃ C > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ Cε > (0 : ℝ), ∃ N₀ : ℕ,
      ∀ (n : ℕ) [NeZero n], N₀ ≤ n →
        tn n - Cε * (n : ℝ) ^ 2 ≤ tmix n ε ∧
        tmix n ε ≤ tn n + C * (n : ℝ) ^ 2 * Real.log (Real.log n) + Cε * (n : ℝ) ^ 2 :=
  cutoff

end CycleCutoff.Challenge
