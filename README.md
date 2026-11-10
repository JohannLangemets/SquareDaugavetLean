# SquareDaugavet

Lean 4 / Mathlib formalization of J. Langemets, *Characterizing the Daugavet property by
squares of rank-one operators*.

## Status

| Result | Lean name | Status |
|---|---|---|
| Theorem 2.6 (negative square point ⇔ Daugavet point) | `SquareDaugavet.isNegativeSquarePoint_iff_isDaugavetPoint` | proved |
| Proposition 3.2 (∇-point ⇒ positive square point) | `SquareDaugavet.isPositiveSquarePoint_of_isNablaPoint` | proved |

## Building

```
lake exe cache get
lake build
```
