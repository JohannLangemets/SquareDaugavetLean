import SquareDaugavet.PositiveGlobal

/-!
# ∇-points are positive square points (Proposition 3.2)
-/

namespace SquareDaugavet

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Proposition 3.2.** Let `X` be a real normed space. If `x` is a ∇-point, then `x` is a
positive square point. (The paper assumes `X` Banach; completeness is not needed.) -/
theorem isPositiveSquarePoint_of_isNablaPoint {x : X}
    (hx : IsNablaPoint x) : IsPositiveSquarePoint x := by
  obtain ⟨hx1, hnabla⟩ := hx
  refine ⟨hx1, fun f hf hfx => ?_⟩
  intro ε hε
  -- The paper takes `0 < ε < 1` and `δ = ε/2`; taking `δ = min ε 1 / 2` covers every `ε > 0`.
  obtain ⟨δ, hδ0, hδε, hδ1⟩ : ∃ δ : ℝ, 0 < δ ∧ 2 * δ ≤ ε ∧ 2 * δ ≤ 1 :=
    ⟨min ε 1 / 2, div_pos (lt_min hε one_pos) (by norm_num),
      by linarith [min_le_left ε 1], by linarith [min_le_right ε 1]⟩
  -- "Since `(-f)(x) ≤ 0 < 1 - δ`, the slice `S(-f, δ)` does not contain `x`."
  have hnot : x ∉ slice (-f) δ := by
    rintro ⟨-, h⟩
    rw [neg_apply] at h
    linarith
  have hsup := hnabla (-f) (by rw [norm_neg, hf]) δ hδ0 hnot
  set A := (fun z => ‖x - z‖) '' slice (-f) δ with hA
  -- `A` is nonempty: otherwise its `sSup` would be `sSup ∅ = 0`, not `2`.
  have hne : A.Nonempty := by
    rcases Set.eq_empty_or_nonempty A with h | h
    · rw [h, Real.sSup_empty] at hsup
      norm_num at hsup
    · exact h
  -- "There is therefore `z ∈ S(-f, δ)` with `‖x - z‖ > 2 - δ`."
  obtain ⟨_, ⟨z, hz, rfl⟩, hxz⟩ :=
    exists_lt_of_lt_csSup hne (show 2 - δ < sSup A by rw [hsup]; linarith)
  have hz' : ‖z‖ ≤ 1 ∧ 1 - δ < (-f) z := hz
  have hxz' : 2 - δ < ‖x - z‖ := hxz
  -- "Set `y = -z`. Then `f(y) > 1 - δ` and `‖x + y‖ > 2 - δ`."
  set y := -z with hy_def
  have hy1 : ‖y‖ ≤ 1 := by rw [hy_def, norm_neg]; exact hz'.1
  have hfy : 1 - δ < f y := by
    have := hz'.2
    rw [neg_apply] at this
    rw [hy_def, map_neg]
    exact this
  have hxy : 2 - δ < ‖x + y‖ := by rw [hy_def, ← sub_eq_add_neg]; exact hxz'
  -- "Therefore, we have `1 - δ < ‖y‖ ≤ 1`."
  have hy0 : 1 - δ < ‖y‖ := by linarith [norm_add_le x y]
  have hypos : 0 < ‖y‖ := by linarith
  -- "For `w = y / ‖y‖ ∈ S_X` ..."
  set w := ‖y‖⁻¹ • y with hw_def
  have hw1 : ‖w‖ = 1 := by
    rw [hw_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hypos.ne']
  refine ⟨w, hw1, ?_, ?_⟩
  · -- "`f(w) ≥ f(y) > 1 - δ > 1 - ε`": from `f(y) = ‖y‖ f(w)` with `0 < ‖y‖ ≤ 1`.
    have hfw : f y = ‖y‖ * f w := by
      rw [hw_def, map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hypos.ne', one_mul]
    have hfw0 : 0 ≤ f w := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hy1 hfw0]
  · -- "`‖x + w‖ ≥ ‖x + y‖ - ‖w - y‖ > 2 - δ - (1 - ‖y‖) > 2 - ε`".
    have hwy : ‖w - y‖ = 1 - ‖y‖ := by
      have : w - y = (‖y‖⁻¹ - 1) • y := by rw [hw_def, sub_smul, one_smul]
      have hinv : 0 ≤ ‖y‖⁻¹ - 1 := by
        rw [sub_nonneg]
        exact (one_le_inv₀ hypos).mpr hy1
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv, sub_mul,
        inv_mul_cancel₀ hypos.ne', one_mul]
    have htri : ‖x + y‖ ≤ ‖x + w‖ + ‖w - y‖ :=
      calc ‖x + y‖ = ‖(x + w) - (w - y)‖ := by congr 1; abel
        _ ≤ ‖x + w‖ + ‖w - y‖ := norm_sub_le _ _
    linarith

/-- **Remark 3.3** (new proof of HLPV2024, Theorem 1.6). If `dim X > 1` and every point of `S_X`
is a ∇-point, then `X` has the Daugavet property. (The paper assumes `X` Banach; completeness is
not needed.) -/
theorem hasDaugavetProperty_of_forall_isNablaPoint (hdim : 1 < Module.rank ℝ X)
    (h : ∀ x : X, ‖x‖ = 1 → IsNablaPoint x) : HasDaugavetProperty X := by
  -- `dim X > 1` gives `X ≠ {0}`, which Proposition 2.1 needs.
  have : Nontrivial X := rank_pos_iff_nontrivial.mp (zero_lt_one.trans hdim)
  -- By Proposition 3.2, every point of `S_X` is a positive square point.
  have hpos : ∀ x : X, ‖x‖ = 1 → IsPositiveSquarePoint x := fun x hx =>
    isPositiveSquarePoint_of_isNablaPoint (h x hx)
  -- So `X` has the positive square Daugavet property by Proposition 2.1, (iii) ⇒ (i).
  have hsq : HasSquareDaugavetProperty X 1 :=
    ((kmm_signed (X := X) (σ := 1) (Or.inl rfl)).out 1 3).mpr fun x hx f hf hfx =>
      (hpos x hx).2 f hf (by linarith)
  -- Theorem 2.2 now shows that `X` has the Daugavet property.
  exact (hasSquareDaugavetProperty_one_iff_hasDaugavetProperty hdim).mp hsq

end SquareDaugavet
