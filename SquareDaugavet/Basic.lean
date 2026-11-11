import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.TFAE
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Set

/-!
# Basic definitions

Definitions from J. Langemets, *Characterizing the Daugavet property by squares of
rank-one operators*, Section 2.

We work in a real normed space `X` (completeness is never needed for these definitions).
The dual space `X*` is `StrongDual ℝ X`, i.e. continuous linear maps `X →L[ℝ] ℝ`
with the operator norm.

We import only the Mathlib modules we need, not all of `Mathlib`: builds are much faster.
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

/-- Definition 2.5: `x ∈ S_X` is a *positive square point* if `(x, f)` is good for every
`f ∈ S_{X*}` with `f x ≥ 0`. -/
def IsPositiveSquarePoint (x : X) : Prop :=
  ‖x‖ = 1 ∧ ∀ f : StrongDual ℝ X, ‖f‖ = 1 → 0 ≤ f x → IsGood x f

/-- Definition 2.5: `x ∈ S_X` is a *negative square point* if `(x, f)` is good for every
`f ∈ S_{X*}` with `f x ≤ 0`. -/
def IsNegativeSquarePoint (x : X) : Prop :=
  ‖x‖ = 1 ∧ ∀ f : StrongDual ℝ X, ‖f‖ = 1 → f x ≤ 0 → IsGood x f

/-- The slice `S(f, α) = {y ∈ B_X : f y > 1 - α}` of the closed unit ball (Section 3).
The paper uses it for `f ∈ S_{X*}` and `α > 0`; those conditions are imposed where it is used. -/
def slice (f : StrongDual ℝ X) (α : ℝ) : Set X :=
  {y | ‖y‖ ≤ 1 ∧ 1 - α < f y}

lemma mem_slice {f : StrongDual ℝ X} {α : ℝ} {y : X} :
    y ∈ slice f α ↔ ‖y‖ ≤ 1 ∧ 1 - α < f y :=
  Iff.rfl

/-- Definition 3.1 (from [AHLP2020]): `x ∈ S_X` is a *Δ-point* if
`sup_{y ∈ S} ‖x - y‖ = 2` for every slice `S = S(f, α)` of `B_X` containing `x`. -/
def IsDeltaPoint (x : X) : Prop :=
  ‖x‖ = 1 ∧ ∀ f : StrongDual ℝ X, ‖f‖ = 1 → ∀ α > 0, x ∈ slice f α →
    sSup ((fun y => ‖x - y‖) '' slice f α) = 2

/-- Definition 3.1 (from [HLPV2024]): `x ∈ S_X` is a *∇-point* if
`sup_{y ∈ S} ‖x - y‖ = 2` for every slice `S = S(f, α)` of `B_X` not containing `x`.

`sSup` on `ℝ` returns `0` for empty or unbounded sets; neither happens here, since slices with
`‖f‖ = 1`, `α > 0` are nonempty and `‖x - y‖ ≤ 2` on `B_X`. -/
def IsNablaPoint (x : X) : Prop :=
  ‖x‖ = 1 ∧ ∀ f : StrongDual ℝ X, ‖f‖ = 1 → ∀ α > 0, x ∉ slice f α →
    sSup ((fun y => ‖x - y‖) '' slice f α) = 2

/-- A functional evaluated at a unit vector is bounded by its norm: `|φ v| ≤ ‖φ‖`. -/
lemma abs_apply_le_norm (φ : StrongDual ℝ X) {v : X} (hv : ‖v‖ = 1) : |φ v| ≤ ‖φ‖ := by
  simpa [Real.norm_eq_abs, hv] using φ.le_opNorm v

end SquareDaugavet
