# SquareDaugavet

Lean 4 / Mathlib formalization of J. Langemets, *Characterizing the Daugavet property by
squares of rank-one operators*
([doi:10.48550/arXiv.2609.27693](https://doi.org/10.48550/arXiv.2609.27693)).

## Status

The paper works with Banach spaces; every result here is proved for real normed spaces, since
no proof uses completeness.

| Result | Lean name | Status |
|---|---|---|
| Proposition 2.1 (KMM2007: σ-square Daugavet property ⇔ rank-one equation for σf(x) ≥ 0 ⇔ good pairs) | `SquareDaugavet.kmm_signed` | proved |
| KSSW2000, Lemma 2.2 (Daugavet property ⇔ every normalized pair is good) | `SquareDaugavet.hasDaugavetProperty_iff_forall_isGood` | proved |
| Theorem 2.2 (dim X > 1: positive square Daugavet property ⇔ Daugavet property) | `SquareDaugavet.hasSquareDaugavetProperty_one_iff_hasDaugavetProperty` | proved |
| Theorem 2.2, core (dim X > 1, every point of S_X a positive square point ⇒ every point a Daugavet point) | `SquareDaugavet.isDaugavetPoint_of_forall_isPositiveSquarePoint` | proved |
| Remark 2.3 (ℝ is extremely non-complex, has the positive square Daugavet property, not the Daugavet property) | `SquareDaugavet.real_isExtremelyNonComplex_not_hasDaugavetProperty` | proved |
| Corollary 2.4 (extremely non-complex, dim X > 1 ⇒ Daugavet property) | `SquareDaugavet.hasDaugavetProperty_of_isExtremelyNonComplex` | proved |
| Theorem 2.6 (negative square point ⇔ Daugavet point) | `SquareDaugavet.isNegativeSquarePoint_iff_isDaugavetPoint` | proved |
| Corollary 2.7 (negative square Daugavet property ⇔ Daugavet property) | `SquareDaugavet.hasSquareDaugavetProperty_neg_one_iff_hasDaugavetProperty` | proved |
| Proposition 3.2 (∇-point ⇒ positive square point) | `SquareDaugavet.isPositiveSquarePoint_of_isNablaPoint` | proved |
| Remark 3.3 (dim X > 1, every point of S_X a ∇-point ⇒ Daugavet property; new proof of HLPV Thm 1.6) | `SquareDaugavet.hasDaugavetProperty_of_forall_isNablaPoint` | proved |
| Example 3.4 (in ℓ∞², `(1, 0)` is a positive square point, neither ∇- nor Δ-point) | `SquareDaugavet.ex_linfty` | proved |
| Example 3.5 (in c ⊕₂ ℝ, `(𝟏, 0)` is a Δ-point but not a positive square point) | `SquareDaugavet.ex_c_sum_real` | proved |

## Building

```
lake exe cache get
lake build
```
