[![](logo.svg)](https://axiommath.ai/)

# Cutoff for the Adjacent Transposition Shuffle on a Cycle

This is a Lean formalization of total-variation cutoff for the adjacent transposition shuffle
on the cycle of length `n`, at time `n² log n / (8π²)` with a window of order `n² log log n`.

## Main Results

* There is an absolute constant `C > 0` such that for every `ε ∈ (0, 1)` there is `C_ε > 0` with
  `t_n - C_ε n² ≤ t_mix(ε) ≤ t_n + C n² log log n + C_ε n²` for all sufficiently large `n`,
  where `t_n = log n / (2(2 - 2 cos(2π/n)))`.

See [§Formal Challenge](#formal-challenge) for a formal certificate.

## Dependencies

This depends on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Formal Challenge

A formal challenge file certifying that this repository does formalize the results
claimed above is located at [Challenge/Basic.lean](Challenge/Basic.lean). This file only
depends on the dependency above. It contains formal statements of
[§Main Results](#main-results) with `sorry` as proof.

This repository can be verified against the formal challenge with the Lean
comparator on a Linux machine. First, follow the instructions in
https://github.com/leanprover/comparator to install `comparator`. Then, run the following command:

```
lake env comparator Comparator/comparator.json
```

This repository has been verified with the comparator.
