import Mathlib

/-!
# Basic definitions

Definitions from J. Langemets, *Characterizing the Daugavet property by squares of
rank-one operators*, Section 2.

We work in a real normed space `X` (completeness is never needed for these definitions).
The dual space `X*` is `StrongDual ℝ X`, i.e. continuous linear maps `X →L[ℝ] ℝ`
with the operator norm.
-/

namespace SquareDaugavet

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The pair `(x, f)` is *good* (condition (G) of the paper): for every `ε > 0` there is
`y ∈ S_X` with `f y > 1 - ε` and `‖x + y‖ > 2 - ε`.

The paper only uses this for `x ∈ S_X`, `f ∈ S_{X*}`; those norm conditions are imposed
where the notion is used. -/
def IsGood (x : X) (f : StrongDual ℝ X) : Prop :=
  ∀ ε > 0, ∃ y : X, ‖y‖ = 1 ∧ 1 - ε < f y ∧ 2 - ε < ‖x + y‖

/-- `x ∈ S_X` is a *Daugavet point* if `(x, f)` is good for every `f ∈ S_{X*}`. -/
def IsDaugavetPoint (x : X) : Prop :=
  ‖x‖ = 1 ∧ ∀ f : StrongDual ℝ X, ‖f‖ = 1 → IsGood x f

/-- Definition 2.5: `x ∈ S_X` is a *negative square point* if `(x, f)` is good for every
`f ∈ S_{X*}` with `f x ≤ 0`. -/
def IsNegativeSquarePoint (x : X) : Prop :=
  ‖x‖ = 1 ∧ ∀ f : StrongDual ℝ X, ‖f‖ = 1 → f x ≤ 0 → IsGood x f

/-- A functional evaluated at a unit vector is bounded by its norm: `|φ v| ≤ ‖φ‖`. -/
lemma abs_apply_le_norm (φ : StrongDual ℝ X) {v : X} (hv : ‖v‖ = 1) : |φ v| ≤ ‖φ‖ := by
  simpa [Real.norm_eq_abs, hv] using φ.le_opNorm v

end SquareDaugavet
