import SquareDaugavet.Basic

/-!
# Proposition 2.1 (KMM2007, Prop. 4.8/4.9) and KSSW2000, Lemma 2.2

We define the Daugavet property and the `σ`-square Daugavet properties literally, via rank-one
operators, and prove the equivalences with good pairs that the paper quotes.

Notation: `f.smulRight x` is the operator `f ⊗ x : z ↦ f(z) x`; `1 : X →L[ℝ] X` is `Id`, and
`T ^ 2 = T ∘ T`.

The proof of (i) ⇔ (ii) in Proposition 2.1 follows Kadets–Martín–Merí:
* (i) ⇒ (ii): if `σ f(x) > 0`, then `S = (σ f(x))^{-1/2} (f ⊗ x)` satisfies `σ S² = f ⊗ x`;
  if `σ f(x) = 0`, approximate `f ⊗ x` in norm by `g ⊗ x` with `σ g(x) > 0` and use that the
  set of operators satisfying the Daugavet equation is closed.
* (ii) ⇒ (i): `T = f ⊗ x` gives `T² = f(x) T`, so `σ T² = (σ f(x) f) ⊗ x`.

(ii) ⇔ (iii) uses the standard argument of KSSW2000 (Lemma 2.1 there): for `x ∈ S_X`,
`f ∈ S_{X*}`, `‖Id + f ⊗ x‖ = 2` iff `(x, f)` is good, and the Daugavet equation for `T`
implies it for every `t T`, `t ≥ 0`.
-/

namespace SquareDaugavet

open Module

/-- `X` has the *Daugavet property*: `‖Id + T‖ = 1 + ‖T‖` for every rank-one operator `T`. -/
def HasDaugavetProperty (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ T : X →L[ℝ] X, finrank ℝ (LinearMap.range (T : X →ₗ[ℝ] X)) = 1 → ‖1 + T‖ = 1 + ‖T‖

/-- `X` has the *`σ`-square Daugavet property*: `‖Id + σT²‖ = 1 + ‖T²‖` for every rank-one
operator `T`. (The paper takes `σ ∈ {-1, 1}`; that is imposed where it is used.) -/
def HasSquareDaugavetProperty (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (σ : ℝ) :
    Prop :=
  ∀ T : X →L[ℝ] X, finrank ℝ (LinearMap.range (T : X →ₗ[ℝ] X)) = 1 →
    ‖1 + σ • T ^ 2‖ = 1 + ‖T ^ 2‖

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ### Preliminaries on `Id` and rank-one operators -/

/-- Normalizing a nonzero vector gives a unit vector (in any real normed space). -/
lemma norm_inv_norm_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {v : E}
    (hv : v ≠ 0) : ‖‖v‖⁻¹ • v‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_pos_iff.mpr hv).ne']

/-- `‖Id‖ ≤ 1`. -/
lemma norm_one_le : ‖(1 : X →L[ℝ] X)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by simp

/-- `(Id + f ⊗ x)(y) = y + f(y) x`. -/
lemma one_add_smulRight_apply (f : StrongDual ℝ X) (x y : X) :
    (1 + f.smulRight x) y = y + f y • x := by
  simp

/-- `(f ⊗ x)² = f(x) (f ⊗ x)`. -/
lemma smulRight_sq (f : StrongDual ℝ X) (x : X) :
    (f.smulRight x) ^ 2 = f x • f.smulRight x := by
  ext z
  simp [pow_two, smul_smul, mul_comm]

/-- `(a f) ⊗ x = a (f ⊗ x)`. -/
lemma smul_smulRight (a : ℝ) (f : StrongDual ℝ X) (x : X) :
    (a • f).smulRight x = a • f.smulRight x := by
  ext z
  simp [smul_smul]

/-- `f ⊗ x` has rank one when `f ≠ 0` and `x ≠ 0`: its range is `span {x}`. -/
lemma finrank_range_smulRight {f : StrongDual ℝ X} {x : X} (hf : f ≠ 0) (hx : x ≠ 0) :
    finrank ℝ (LinearMap.range (f.smulRight x : X →ₗ[ℝ] X)) = 1 := by
  obtain ⟨z₀, hz₀⟩ : ∃ z, f z ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (ContinuousLinearMap.ext h)
  have hrange : LinearMap.range (f.smulRight x : X →ₗ[ℝ] X) = ℝ ∙ x := by
    ext v
    rw [LinearMap.mem_range, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨f z, rfl⟩
    · rintro ⟨a, rfl⟩
      refine ⟨(a / f z₀) • z₀, ?_⟩
      simp only [ContinuousLinearMap.coe_smulRight, map_smul, LinearMap.coe_smulRight,
        ContinuousLinearMap.coe_coe]
      rw [smul_smul, div_mul_cancel₀ a hz₀]
  rw [hrange]
  exact finrank_span_singleton hx

/-- Every rank-one operator has the form `f ⊗ x` with `f ≠ 0`, `x ≠ 0`. -/
lemma exists_eq_smulRight_of_finrank_range_eq_one {T : X →L[ℝ] X}
    (hT : finrank ℝ (LinearMap.range (T : X →ₗ[ℝ] X)) = 1) :
    ∃ (f : StrongDual ℝ X) (x : X), f ≠ 0 ∧ x ≠ 0 ∧ T = f.smulRight x := by
  -- The range is spanned by a single nonzero vector `x`.
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hT
  have hx : (v : X) ≠ 0 := by
    intro h
    exact hv0 (Subtype.ext h)
  -- So `T z = c(z) x` for every `z`.
  have hTz : ∀ z, ∃ c : ℝ, T z = c • (v : X) := fun z => by
    obtain ⟨c, hc⟩ := hv ⟨T z, LinearMap.mem_range_self (T : X →ₗ[ℝ] X) z⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  -- Choose `g ∈ X*` with `g(x) = ‖x‖`; then `f = ‖x‖⁻¹ (g ∘ T)` satisfies `T = f ⊗ x`.
  obtain ⟨g, -, hgx⟩ := exists_dual_vector ℝ (v : X) (norm_ne_zero_iff.mpr hx)
  rw [RCLike.ofReal_real_eq_id, id_eq] at hgx
  have hnx : 0 < ‖(v : X)‖ := norm_pos_iff.mpr hx
  have hTeq : T = (‖(v : X)‖⁻¹ • g.comp T).smulRight (v : X) := by
    ext z
    obtain ⟨c, hc⟩ := hTz z
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply, ContinuousLinearMap.comp_apply,
      smul_eq_mul, hc, map_smul, hgx]
    rw [show ‖(v : X)‖⁻¹ * (c * ‖(v : X)‖) = c by field_simp]
  refine ⟨_, _, ?_, hx, hTeq⟩
  -- `f ≠ 0`, since otherwise `T = 0`, but `x = T z₀` for some `z₀`.
  intro hf0
  obtain ⟨z₀, hz₀⟩ := LinearMap.mem_range.mp v.2
  apply hx
  rw [← hz₀, ContinuousLinearMap.coe_coe, hTeq, hf0]
  simp

/-- If `f = 0` or `x = 0`, then `f ⊗ x = 0` satisfies the Daugavet equation (`X ≠ {0}`). -/
lemma norm_one_add_smulRight_of_eq_zero [Nontrivial X] {f : StrongDual ℝ X} {x : X}
    (h : f = 0 ∨ x = 0) : ‖1 + f.smulRight x‖ = 1 + ‖f.smulRight x‖ := by
  have : f.smulRight x = 0 := by
    rcases h with rfl | rfl <;> ext <;> simp
  rw [this, add_zero, norm_zero, add_zero, norm_one]

/-! ### The Daugavet equation and good pairs (KSSW2000) -/

/-- If `T` satisfies the Daugavet equation, so does `t T` for every `t ≥ 0`. -/
lemma norm_one_add_smul_of_norm_one_add {T : X →L[ℝ] X} (hT : ‖1 + T‖ = 1 + ‖T‖) {t : ℝ}
    (ht : 0 ≤ t) : ‖1 + t • T‖ = 1 + t * ‖T‖ := by
  have h1 := norm_one_le (X := X)
  refine le_antisymm ?_ ?_
  · calc ‖1 + t • T‖ ≤ ‖(1 : X →L[ℝ] X)‖ + ‖t • T‖ := norm_add_le _ _
      _ ≤ 1 + t * ‖T‖ := by rw [norm_smul, Real.norm_of_nonneg ht]; linarith
  rcases le_total t 1 with ht1 | ht1
  · -- `Id + T = (Id + tT) + (1 - t)T`.
    have h := norm_add_le (1 + t • T) ((1 - t) • T)
    rw [show (1 + t • T) + (1 - t) • T = 1 + T by rw [sub_smul, one_smul]; abel, hT,
      norm_smul, Real.norm_of_nonneg (by linarith)] at h
    nlinarith
  · -- `t (Id + T) = (Id + tT) + (t - 1) Id`.
    have h := norm_add_le (1 + t • T) ((t - 1) • (1 : X →L[ℝ] X))
    rw [show (1 + t • T) + (t - 1) • (1 : X →L[ℝ] X) = t • (1 + T) by
        rw [sub_smul, one_smul, smul_add]; abel,
      norm_smul, norm_smul, hT, Real.norm_of_nonneg ht, Real.norm_of_nonneg (by linarith)] at h
    nlinarith

/-- For `x ∈ S_X`, `f ∈ S_{X*}`: if `(x, f)` is good, then `‖Id + f ⊗ x‖ = 2`. -/
lemma norm_one_add_smulRight_eq_two_of_isGood {f : StrongDual ℝ X} {x : X} (hf : ‖f‖ = 1)
    (hx : ‖x‖ = 1) (hg : IsGood x f) : ‖1 + f.smulRight x‖ = 2 := by
  refine le_antisymm ?_ (le_of_forall_pos_lt_add fun ε hε => ?_)
  · calc ‖1 + f.smulRight x‖ ≤ ‖(1 : X →L[ℝ] X)‖ + ‖f.smulRight x‖ := norm_add_le _ _
      _ ≤ 2 := by
        rw [ContinuousLinearMap.norm_smulRight_apply, hf, hx]
        linarith [norm_one_le (X := X)]
  -- Take `y ∈ S_X` with `f(y) > 1 - ε/2` and `‖x + y‖ > 2 - ε/2`.
  obtain ⟨y, hy1, hfy, hxy⟩ := hg (ε / 2) (by linarith)
  have hfy1 := (abs_le.mp (abs_apply_le_norm f hy1)).2
  rw [hf] at hfy1
  -- `‖(Id + f ⊗ x) y‖ ≤ ‖Id + f ⊗ x‖`.
  have h1 := (1 + f.smulRight x).le_opNorm y
  rw [one_add_smulRight_apply, hy1, mul_one] at h1
  -- `x + y = (y + f(y) x) + (1 - f(y)) x`.
  have h2 : ‖x + y‖ ≤ ‖y + f y • x‖ + (1 - f y) := by
    calc ‖x + y‖ = ‖(y + f y • x) + (1 - f y) • x‖ := by
          rw [sub_smul, one_smul]; congr 1; abel
      _ ≤ ‖y + f y • x‖ + ‖(1 - f y) • x‖ := norm_add_le _ _
      _ = ‖y + f y • x‖ + (1 - f y) := by
          rw [norm_smul, hx, mul_one, Real.norm_of_nonneg (by linarith)]
  linarith

/-- For `x ∈ S_X`, `f ∈ S_{X*}`: if `‖Id + f ⊗ x‖ = 2`, then `(x, f)` is good. -/
lemma isGood_of_norm_one_add_smulRight_eq_two {f : StrongDual ℝ X} {x : X} (hf : ‖f‖ = 1)
    (hx : ‖x‖ = 1) (h : ‖1 + f.smulRight x‖ = 2) : IsGood x f := by
  intro ε hε
  obtain ⟨η, hη0, hηε, hη1⟩ : ∃ η : ℝ, 0 < η ∧ 3 * η ≤ ε ∧ η ≤ 1 / 2 :=
    ⟨min ε 1 / 6, div_pos (lt_min hε one_pos) (by norm_num),
      by linarith [min_le_left ε 1], by linarith [min_le_right ε 1]⟩
  -- There is `y₀` with `‖y₀‖ < 1` and `‖y₀ + f(y₀) x‖ > 2 - η`.
  obtain ⟨y₀, hy₀1, hy₀⟩ :=
    (1 + f.smulRight x).exists_lt_apply_of_lt_opNorm (r := 2 - η) (by rw [h]; linarith)
  rw [one_add_smulRight_apply] at hy₀
  -- Replacing `y₀` by `-y₀` if needed, we may assume `f(y₁) = |f(y₀)| ≥ 0`.
  obtain ⟨y₁, hy₁n, hfy₁, hy₁⟩ : ∃ y₁ : X, ‖y₁‖ = ‖y₀‖ ∧ f y₁ = |f y₀| ∧
      ‖y₁ + f y₁ • x‖ = ‖y₀ + f y₀ • x‖ := by
    rcases le_total 0 (f y₀) with h0 | h0
    · exact ⟨y₀, rfl, (abs_of_nonneg h0).symm, rfl⟩
    · refine ⟨-y₀, norm_neg _, by rw [map_neg, abs_of_nonpos h0], ?_⟩
      rw [map_neg, neg_smul, ← neg_add, norm_neg]
  rw [← hy₁] at hy₀
  rw [← hy₁n] at hy₀1
  -- `|f(y₁)| ≤ ‖y₁‖` and `‖y₁ + f(y₁) x‖ ≤ ‖y₁‖ + f(y₁)`, so `f(y₁), ‖y₁‖ > 1 - η`.
  have hfle : f y₁ ≤ ‖y₁‖ := by
    have := f.le_opNorm y₁
    rw [hf, one_mul, Real.norm_eq_abs] at this
    exact (abs_le.mp this).2
  have hfnn : 0 ≤ f y₁ := by rw [hfy₁]; exact abs_nonneg _
  have htri : ‖y₁ + f y₁ • x‖ ≤ ‖y₁‖ + f y₁ := by
    calc ‖y₁ + f y₁ • x‖ ≤ ‖y₁‖ + ‖f y₁ • x‖ := norm_add_le _ _
      _ = ‖y₁‖ + f y₁ := by rw [norm_smul, hx, mul_one, Real.norm_of_nonneg hfnn]
  have hfy₁' : 1 - η < f y₁ := by linarith
  have hny₁ : 1 - η < ‖y₁‖ := by linarith
  have hnpos : 0 < ‖y₁‖ := by linarith
  -- `‖x + y₁‖ ≥ ‖y₁ + f(y₁) x‖ - (1 - f(y₁)) > 2 - 2η`.
  have hxy₁ : 2 - 2 * η < ‖x + y₁‖ := by
    have : ‖y₁ + f y₁ • x‖ ≤ ‖x + y₁‖ + (1 - f y₁) := by
      calc ‖y₁ + f y₁ • x‖ = ‖(x + y₁) + (f y₁ - 1) • x‖ := by
            rw [sub_smul, one_smul]; congr 1; abel
        _ ≤ ‖x + y₁‖ + ‖(f y₁ - 1) • x‖ := norm_add_le _ _
        _ = ‖x + y₁‖ + (1 - f y₁) := by
            rw [norm_smul, hx, mul_one, Real.norm_eq_abs, abs_sub_comm,
              abs_of_nonneg (by linarith)]
    linarith
  -- Normalize: `y = y₁ / ‖y₁‖ ∈ S_X`.
  have hy₁0 : y₁ ≠ 0 := norm_pos_iff.mp hnpos
  refine ⟨‖y₁‖⁻¹ • y₁, norm_inv_norm_smul hy₁0, ?_, ?_⟩
  · -- `f(y) = f(y₁) / ‖y₁‖ ≥ f(y₁) > 1 - η ≥ 1 - ε`.
    have hfy : f (‖y₁‖⁻¹ • y₁) * ‖y₁‖ = f y₁ := by
      rw [map_smul, smul_eq_mul, mul_comm, ← mul_assoc, mul_inv_cancel₀ hnpos.ne', one_mul]
    have hfypos : 0 ≤ f (‖y₁‖⁻¹ • y₁) := by
      rw [map_smul, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.mpr hnpos.le) hfnn
    nlinarith
  · -- `‖y - y₁‖ = 1 - ‖y₁‖ < η`, so `‖x + y‖ > 2 - 3η ≥ 2 - ε`.
    have hdist : ‖‖y₁‖⁻¹ • y₁ - y₁‖ = 1 - ‖y₁‖ := by
      rw [show ‖y₁‖⁻¹ • y₁ - y₁ = (‖y₁‖⁻¹ - 1) • y₁ by rw [sub_smul, one_smul], norm_smul,
        Real.norm_of_nonneg (sub_nonneg.mpr ((one_le_inv₀ hnpos).mpr hy₀1.le)), sub_mul,
        inv_mul_cancel₀ hnpos.ne', one_mul]
    have : ‖x + y₁‖ ≤ ‖x + ‖y₁‖⁻¹ • y₁‖ + ‖‖y₁‖⁻¹ • y₁ - y₁‖ := by
      calc ‖x + y₁‖ = ‖(x + ‖y₁‖⁻¹ • y₁) - (‖y₁‖⁻¹ • y₁ - y₁)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith

/-- If the normalized pair `(x / ‖x‖, f / ‖f‖)` is good, then `f ⊗ x` satisfies the Daugavet
equation. -/
lemma norm_one_add_smulRight_of_isGood {f : StrongDual ℝ X} {x : X} (hf : f ≠ 0) (hx : x ≠ 0)
    (hg : IsGood (‖x‖⁻¹ • x) (‖f‖⁻¹ • f)) :
    ‖1 + f.smulRight x‖ = 1 + ‖f.smulRight x‖ := by
  have hnf : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h2 := norm_one_add_smulRight_eq_two_of_isGood (norm_inv_norm_smul hf)
    (norm_inv_norm_smul hx) hg
  have hT1 : ‖(‖f‖⁻¹ • f).smulRight (‖x‖⁻¹ • x)‖ = 1 := by
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_inv_norm_smul hf,
      norm_inv_norm_smul hx, one_mul]
  -- `f ⊗ x = (‖f‖ ‖x‖) (f / ‖f‖ ⊗ x / ‖x‖)`.
  have heq : f.smulRight x = (‖f‖ * ‖x‖) • (‖f‖⁻¹ • f).smulRight (‖x‖⁻¹ • x) := by
    ext z
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul, smul_smul]
    congr 1
    field_simp
  rw [heq, norm_one_add_smul_of_norm_one_add (by rw [h2, hT1]; norm_num) (by positivity),
    norm_smul, Real.norm_of_nonneg (by positivity), hT1, mul_one]

/-- **KSSW2000, Lemma 2.2.** `X` has the Daugavet property iff every pair
`(x, f) ∈ S_X × S_{X*}` is good. -/
theorem hasDaugavetProperty_iff_forall_isGood :
    HasDaugavetProperty X ↔
      ∀ x : X, ‖x‖ = 1 → ∀ f : StrongDual ℝ X, ‖f‖ = 1 → IsGood x f := by
  constructor
  · intro hD x hx f hf
    have hf0 : f ≠ 0 := by rintro rfl; rw [norm_zero] at hf; exact zero_ne_one hf
    have hx0 : x ≠ 0 := by rintro rfl; rw [norm_zero] at hx; exact zero_ne_one hx
    have h := hD _ (finrank_range_smulRight hf0 hx0)
    rw [ContinuousLinearMap.norm_smulRight_apply, hf, hx] at h
    exact isGood_of_norm_one_add_smulRight_eq_two hf hx (by rw [h]; norm_num)
  · intro hG T hT
    obtain ⟨f, x, hf, hx, rfl⟩ := exists_eq_smulRight_of_finrank_range_eq_one hT
    exact norm_one_add_smulRight_of_isGood hf hx
      (hG _ (norm_inv_norm_smul hx) _ (norm_inv_norm_smul hf))

/-! ### Proposition 2.1 -/

/-- (i) ⇒ (ii) of Proposition 2.1, case `σ f(x) > 0` (KMM): `S = (σ f(x))^{-1/2} (f ⊗ x)` is
rank-one with `σ S² = f ⊗ x`, so `1 + ‖f ⊗ x‖ = 1 + ‖S²‖ = ‖Id + σ S²‖ = ‖Id + f ⊗ x‖`. -/
lemma norm_one_add_smulRight_of_square_of_pos {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hsq : HasSquareDaugavetProperty X σ) {f : StrongDual ℝ X} {x : X} (hpos : 0 < σ * f x) :
    ‖1 + f.smulRight x‖ = 1 + ‖f.smulRight x‖ := by
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσn : ‖σ‖ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hfx : f x ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  have hf : f ≠ 0 := by
    rintro rfl
    exact hfx rfl
  have hx : x ≠ 0 := by
    rintro rfl
    exact hfx (map_zero f)
  -- `c = (σ f(x))^{-1/2}`, so `c² = (σ f(x))⁻¹`.
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, c ≠ 0 ∧ c * c = (σ * f x)⁻¹ :=
    ⟨(Real.sqrt (σ * f x))⁻¹, inv_ne_zero (Real.sqrt_pos.mpr hpos).ne',
      by rw [← mul_inv, Real.mul_self_sqrt hpos.le]⟩
  -- `S = (c f) ⊗ x = c (f ⊗ x)`; then `σ S² = f ⊗ x`.
  have hS : σ • ((c • f).smulRight x) ^ 2 = f.smulRight x := by
    rw [smulRight_sq, smul_smulRight, smul_smul, smul_smul, smul_apply, smul_eq_mul,
      show σ * (c * f x) * c = (c * c) * (σ * f x) by ring, hc, inv_mul_cancel₀ hpos.ne',
      one_smul]
  have h := hsq _ (finrank_range_smulRight (smul_ne_zero hc0 hf) hx)
  rw [hS] at h
  rw [h, ← hS, norm_smul, hσn, one_mul]

/-- (i) ⇒ (ii) of Proposition 2.1, case `σ f(x) = 0` (KMM): `f ⊗ x` is a norm limit of operators
`g ⊗ x` with `σ g(x) > 0`, and the Daugavet equation is a closed condition. -/
lemma norm_one_add_smulRight_of_square_of_eq_zero [Nontrivial X] {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hsq : HasSquareDaugavetProperty X σ) {f : StrongDual ℝ X} {x : X}
    (hzero : σ * f x = 0) : ‖1 + f.smulRight x‖ = 1 + ‖f.smulRight x‖ := by
  by_cases hx : x = 0
  · exact norm_one_add_smulRight_of_eq_zero (Or.inr hx)
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  -- The set `D` of operators satisfying the Daugavet equation is closed.
  have hD : IsClosed {T : X →L[ℝ] X | ‖1 + T‖ = 1 + ‖T‖} :=
    isClosed_eq (continuous_const.add continuous_id).norm (continuous_const.add continuous_norm)
  -- `g ∈ S_{X*}` with `g(x) = ‖x‖`; approximants `A δ = (f + δσ g) ⊗ x`, `δ > 0`.
  obtain ⟨g, -, hgx⟩ := exists_dual_vector ℝ x (norm_ne_zero_iff.mpr hx)
  rw [RCLike.ofReal_real_eq_id, id_eq] at hgx
  have hA : ∀ δ : ℝ, (f + (δ * σ) • g).smulRight x =
      f.smulRight x + δ • (σ • g).smulRight x := fun δ => by
    ext z
    simp [add_smul, smul_smul, mul_assoc]
  -- `A δ → f ⊗ x` as `δ → 0`.
  have hlim : Filter.Tendsto (fun δ : ℝ => (f + (δ * σ) • g).smulRight x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f.smulRight x)) := by
    simp_rw [hA]
    have hc : Continuous fun δ : ℝ => f.smulRight x + δ • (σ • g).smulRight x :=
      continuous_const.add (continuous_id.smul continuous_const)
    have := hc.tendsto 0
    rw [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  -- For `δ > 0`, `σ (f + δσ g)(x) = δ ‖x‖ > 0`, so `A δ ∈ D` by the first case.
  refine hD.mem_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ => ?_)
  apply norm_one_add_smulRight_of_square_of_pos hσ hsq
  rw [add_apply, smul_apply, smul_eq_mul, hgx,
    show σ * (f x + δ * σ * ‖x‖) = σ * f x + (σ * σ) * (δ * ‖x‖) by ring, hzero, hσσ]
  have : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have : (0 : ℝ) < δ := hδ
  positivity

/-- **Proposition 2.1** (KMM2007, Prop. 4.9). Let `X` be a nonzero real normed space and
`σ ∈ {-1, 1}`. (The paper assumes `X` Banach; completeness is not needed.)
The following are equivalent:
(i) `X` has the `σ`-square Daugavet property;
(ii) `‖Id + f ⊗ x‖ = 1 + ‖f ⊗ x‖` for all `f ∈ X*`, `x ∈ X` with `σ f(x) ≥ 0`;
(iii) `(x, f)` is good for all `x ∈ S_X`, `f ∈ S_{X*}` with `σ f(x) ≥ 0`. -/
theorem kmm_signed [Nontrivial X] {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    List.TFAE
      [HasSquareDaugavetProperty X σ,
       ∀ (f : StrongDual ℝ X) (x : X), 0 ≤ σ * f x →
         ‖1 + f.smulRight x‖ = 1 + ‖f.smulRight x‖,
       ∀ x : X, ‖x‖ = 1 → ∀ f : StrongDual ℝ X, ‖f‖ = 1 → 0 ≤ σ * f x → IsGood x f] := by
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσn : ‖σ‖ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  tfae_have 1 → 2 := by
    intro hsq f x hfx
    rcases hfx.lt_or_eq with hpos | hzero
    · exact norm_one_add_smulRight_of_square_of_pos hσ hsq hpos
    · exact norm_one_add_smulRight_of_square_of_eq_zero hσ hsq hzero.symm
  tfae_have 2 → 1 := by
    -- `T = f ⊗ x`, so `σ T² = (σ f(x) f) ⊗ x` with `σ (σ f(x) f)(x) = f(x)² ≥ 0`.
    intro h2 T hT
    obtain ⟨f, x, -, -, rfl⟩ := exists_eq_smulRight_of_finrank_range_eq_one hT
    have hsq : σ • (f.smulRight x) ^ 2 = ((σ * f x) • f).smulRight x := by
      rw [smulRight_sq, smul_smul, smul_smulRight]
    have h := h2 ((σ * f x) • f) x (by
      rw [smul_apply, smul_eq_mul, show σ * (σ * f x * f x) = (σ * σ) * (f x * f x) by ring,
        hσσ, one_mul]
      exact mul_self_nonneg _)
    -- `h` now reads `‖Id + σT²‖ = 1 + ‖σT²‖ = 1 + ‖T²‖`.
    rwa [← hsq, norm_smul, hσn, one_mul] at h
  tfae_have 2 → 3 := by
    intro h2 x hx f hf hfx
    have h := h2 f x hfx
    rw [ContinuousLinearMap.norm_smulRight_apply, hf, hx] at h
    exact isGood_of_norm_one_add_smulRight_eq_two hf hx (by rw [h]; norm_num)
  tfae_have 3 → 2 := by
    intro h3 f x hfx
    by_cases h0 : f = 0 ∨ x = 0
    · exact norm_one_add_smulRight_of_eq_zero h0
    push Not at h0
    obtain ⟨hf, hx⟩ := h0
    refine norm_one_add_smulRight_of_isGood hf hx
      (h3 _ (norm_inv_norm_smul hx) _ (norm_inv_norm_smul hf) ?_)
    rw [smul_apply, map_smul, smul_eq_mul, smul_eq_mul,
      show σ * (‖f‖⁻¹ * (‖x‖⁻¹ * f x)) = (‖f‖⁻¹ * ‖x‖⁻¹) * (σ * f x) by ring]
    exact mul_nonneg (by positivity) hfx
  tfae_finish

end SquareDaugavet
