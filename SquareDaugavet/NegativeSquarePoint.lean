import SquareDaugavet.KMM

/-!
# Negative square points are Daugavet points (Theorem 2.6)
-/

namespace SquareDaugavet

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Theorem 2.6.** Let `X` be a real normed space. An element `x ∈ S_X` is a negative square
point if and only if it is a Daugavet point. (The paper assumes `X` Banach; completeness is not
needed.) -/
theorem isNegativeSquarePoint_iff_isDaugavetPoint (x : X) :
    IsNegativeSquarePoint x ↔ IsDaugavetPoint x := by
  constructor
  swap
  · -- "Clearly, every Daugavet point is a negative square point."
    rintro ⟨hx, hgood⟩
    exact ⟨hx, fun f hf _ => hgood f hf⟩
  rintro ⟨hx, hneg⟩
  refine ⟨hx, fun f hf => ?_⟩
  -- "There is nothing to prove if `f(x) ≤ 0`."
  rcases le_or_gt (f x) 0 with hfx | hfx
  · exact hneg f hf hfx
  intro ε hε
  -- The paper takes `0 < ε < 1` and `δ = ε/8`; taking `δ = min ε 1 / 8` covers every `ε > 0`.
  obtain ⟨δ, hδ0, hδε, hδ1⟩ : ∃ δ : ℝ, 0 < δ ∧ 8 * δ ≤ ε ∧ 8 * δ ≤ 1 :=
    ⟨min ε 1 / 8, div_pos (lt_min hε one_pos) (by norm_num),
      by linarith [min_le_left ε 1], by linarith [min_le_right ε 1]⟩
  -- Apply the negative square condition to `-f` and negate the resulting witness.
  obtain ⟨y', hy'1, hfy', hxy'⟩ :=
    hneg (-f) (by rw [norm_neg, hf]) (by rw [neg_apply]; linarith) δ hδ0
  set y := -y' with hy_def
  have hy1 : ‖y‖ = 1 := by rw [hy_def, norm_neg, hy'1]
  have hfy : 1 - δ < f y := by
    rw [neg_apply] at hfy'
    rw [hy_def, map_neg]
    exact hfy'
  have hyx : 2 - δ < ‖y - x‖ := by
    have : y - x = -(x + y') := by rw [hy_def]; abel
    rw [this, norm_neg]
    exact hxy'
  -- Choose `g ∈ S_{X*}` with `g(y - x) = ‖y - x‖` (Hahn–Banach).
  obtain ⟨g, hg1, hgyx⟩ := exists_dual_vector ℝ (y - x) (by linarith : (0 : ℝ) < ‖y - x‖).ne'
  -- `exists_dual_vector` is stated over `ℝ` or `ℂ`, so it writes `↑‖y - x‖` (a cast `ℝ → 𝕜`);
  -- for `𝕜 = ℝ` the cast is the identity, which `RCLike.ofReal_real_eq_id` says.
  rw [map_sub, RCLike.ofReal_real_eq_id, id_eq] at hgyx
  have hgy := abs_le.mp (abs_apply_le_norm g hy1)
  have hgx := abs_le.mp (abs_apply_le_norm g hx)
  rw [hg1] at hgy hgx
  have hgy' : 1 - δ < g y := by linarith [hgx.1]
  have hgx' : g x < -1 + δ := by linarith [hgy.2]
  -- `F = f + 2g`.
  set F : StrongDual ℝ X := f + (2 : ℝ) • g with hF_def
  have hF : ∀ v, F v = f v + 2 * g v := fun v => by
    rw [hF_def, add_apply, smul_apply, smul_eq_mul]
  have hfx1 := (abs_le.mp (abs_apply_le_norm f hx)).2
  rw [hf] at hfx1
  have hFx : F x < 0 := by rw [hF]; linarith
  have hFnorm : 3 * (1 - δ) < ‖F‖ := by
    have := (abs_le.mp (abs_apply_le_norm F hy1)).2
    rw [hF] at this
    linarith
  have hFpos : 0 < ‖F‖ := by linarith
  -- Apply the negative square condition to `F / ‖F‖`.
  obtain ⟨w, hw1, hhw, hxw⟩ := hneg (‖F‖⁻¹ • F)
    (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hFpos.ne'])
    (by
      rw [smul_apply, smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hFpos.le) hFx.le)
    δ hδ0
  rw [smul_apply, smul_eq_mul] at hhw
  -- `F(w) > (1 - δ) ‖F‖ > 3 (1 - δ)²`.
  have hFw : ‖F‖ * (1 - δ) < F w := by
    have := mul_lt_mul_of_pos_left hhw hFpos
    rwa [← mul_assoc, mul_inv_cancel₀ hFpos.ne', one_mul] at this
  have hkey : (1 - δ) * (3 * (1 - δ)) < (1 - δ) * ‖F‖ :=
    mul_lt_mul_of_pos_left hFnorm (by linarith)
  have hgw := (abs_le.mp (abs_apply_le_norm g hw1)).2
  rw [hg1] at hgw
  rw [hF] at hFw
  -- `f(w) = F(w) - 2g(w) > 3(1 - δ)² - 2 > 1 - 6δ > 1 - ε`, and `‖x + w‖ > 2 - δ > 2 - ε`.
  refine ⟨w, hw1, ?_, by linarith⟩
  nlinarith [sq_nonneg δ]

/-- **Corollary 2.7.** A real normed space has the negative square Daugavet property if and
only if it has the Daugavet property. (The paper assumes `X` Banach; completeness is not needed.
Nor is `X ≠ {0}`: for `X = {0}` there are no rank-one operators and both sides hold vacuously.) -/
theorem hasSquareDaugavetProperty_neg_one_iff_hasDaugavetProperty :
    HasSquareDaugavetProperty X (-1) ↔ HasDaugavetProperty X := by
  rcases subsingleton_or_nontrivial X with hX | hX
  · -- `X = {0}`: no operator has rank one, so both properties hold vacuously.
    have hno : ∀ T : X →L[ℝ] X, Module.finrank ℝ (LinearMap.range (T : X →ₗ[ℝ] X)) ≠ 1 := by
      intro T hT
      rw [Module.finrank_zero_of_subsingleton] at hT
      exact zero_ne_one hT
    exact ⟨fun _ T hT => absurd hT (hno T), fun _ T hT => absurd hT (hno T)⟩
  -- Proposition 2.1 with `σ = -1`; `hK.out 1 3` is its equivalence (i) ⇔ (iii).
  have hK := kmm_signed (X := X) (σ := -1) (Or.inr rfl)
  -- KSSW Lemma 2.2: the Daugavet property means that every normalized pair is good.
  rw [hasDaugavetProperty_iff_forall_isGood]
  constructor
  · -- By Proposition 2.1, every point of `S_X` is a negative square point; by Theorem 2.6,
    -- every point of `S_X` is a Daugavet point.
    intro hsq x hx f hf
    have h3 := (hK.out 1 3).mp hsq
    have hneg : IsNegativeSquarePoint x :=
      ⟨hx, fun g hg hgx => h3 x hx g hg (by linarith)⟩
    exact ((isNegativeSquarePoint_iff_isDaugavetPoint x).mp hneg).2 f hf
  · -- "Clearly": if every normalized pair is good, so is every pair with `f(x) ≤ 0`.
    intro hgood
    exact (hK.out 1 3).mpr fun x hx f hf _ => hgood x hx f hf

end SquareDaugavet
