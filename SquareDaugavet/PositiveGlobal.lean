import SquareDaugavet.KMM

/-!
# The positive square property forces the Daugavet property (core of Theorem 2.2)

Theorem 2.2 of the paper says: if `dim X > 1`, then `X` has the positive square Daugavet property
iff it has the Daugavet property. Via Proposition 2.1 (KMM2007) and KSSW Lemma 2.2 both
properties are statements about good pairs, and the mathematical content of the proof is:

  if every `z ∈ S_X` is a positive square point, then every `x ∈ S_X` is a Daugavet point.

That is `isDaugavetPoint_of_forall_isPositiveSquarePoint` below. The proof follows the paper:
for fixed `f ∈ S_{X*}`, the set `A_f = {z ∈ S_X : (z, f) is good}` is nonempty, and by
property (★) it is clopen in `S_X`; the unit sphere is connected when `dim X > 1`.
-/

namespace SquareDaugavet

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Property (★) in the proof of Theorem 2.2: if every point of `S_X` is a positive square point,
`(z, f)` is good, `x ∈ S_X` and `‖x - z‖ < 1/2`, then `(x, f)` is good. -/
lemma isGood_of_norm_sub_lt_half (hpos : ∀ z : X, ‖z‖ = 1 → IsPositiveSquarePoint z)
    {f : StrongDual ℝ X} (hf : ‖f‖ = 1) {z x : X} (hz : ‖z‖ = 1) (hzf : IsGood z f)
    (hx : ‖x‖ = 1) (hxz : ‖x - z‖ < 1 / 2) : IsGood x f := by
  intro ε hε
  -- The paper writes `ρ = ‖x - z‖`, `δ = 1 - 2ρ` and `η = min{ε, δ} / 12`.
  have hρ0 := norm_nonneg (x - z)
  obtain ⟨η, hη0, hηε, hηδ⟩ : ∃ η : ℝ, 0 < η ∧ 12 * η ≤ ε ∧ 12 * η ≤ 1 - 2 * ‖x - z‖ :=
    ⟨min ε (1 - 2 * ‖x - z‖) / 12,
      div_pos (lt_min hε (by linarith)) (by norm_num),
      by linarith [min_le_left ε (1 - 2 * ‖x - z‖)],
      by linarith [min_le_right ε (1 - 2 * ‖x - z‖)]⟩
  -- Since `z ∈ A_f`, there is `y ∈ S_X` with `f(y) > 1 - η` and `‖z + y‖ > 2 - η`.
  obtain ⟨y, hy1, hfy, hzy⟩ := hzf η hη0
  -- Choose `g ∈ S_{X*}` with `g(z + y) = ‖z + y‖`.
  obtain ⟨g, hg1, hgzy⟩ :=
    exists_dual_vector ℝ (z + y) (by linarith : (0 : ℝ) < ‖z + y‖).ne'
  rw [map_add, RCLike.ofReal_real_eq_id, id_eq] at hgzy
  -- As `g(z), g(y) ≤ 1`, we get `g(z) > 1 - η` and `g(y) > 1 - η`.
  have hgz := (abs_le.mp (abs_apply_le_norm g hz)).2
  have hgy := (abs_le.mp (abs_apply_le_norm g hy1)).2
  rw [hg1] at hgz hgy
  -- `g(x) ≥ g(z) - ‖x - z‖`.
  have hgxz : -‖x - z‖ ≤ g (x - z) := by
    have := g.le_opNorm (x - z)
    rw [hg1, one_mul, Real.norm_eq_abs] at this
    exact (abs_le.mp this).1
  rw [map_sub] at hgxz
  -- `f(x) ≥ -1`.
  have hfx := (abs_le.mp (abs_apply_le_norm f hx)).1
  rw [hf] at hfx
  -- `F = f + 2g`.
  set F : StrongDual ℝ X := f + (2 : ℝ) • g with hF_def
  have hF : ∀ v, F v = f v + 2 * g v := fun v => by
    rw [hF_def, add_apply, smul_apply, smul_eq_mul]
  -- `F(x) > -1 + 2(1 - η - ρ) = δ - 2η > 0`.
  have hFx : 0 < F x := by rw [hF]; linarith
  -- `‖F‖ ≥ F(y) > 3(1 - η)`.
  have hFnorm : 3 * (1 - η) < ‖F‖ := by
    have := (abs_le.mp (abs_apply_le_norm F hy1)).2
    rw [hF] at this
    linarith
  have hFpos : 0 < ‖F‖ := by linarith
  -- `h = F / ‖F‖ ∈ S_{X*}` has `h(x) > 0`, and `x` is a positive square point,
  -- so `(x, h)` is good: there is `w ∈ S_X` with `h(w) > 1 - η` and `‖x + w‖ > 2 - η`.
  obtain ⟨w, hw1, hhw, hxw⟩ := (hpos x hx).2 (‖F‖⁻¹ • F)
    (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hFpos.ne'])
    (by
      rw [smul_apply, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.mpr hFpos.le) hFx.le)
    η hη0
  rw [smul_apply, smul_eq_mul] at hhw
  -- `F(w) > (1 - η) ‖F‖ > 3 (1 - η)²`.
  have hFw : ‖F‖ * (1 - η) < F w := by
    have := mul_lt_mul_of_pos_left hhw hFpos
    rwa [← mul_assoc, mul_inv_cancel₀ hFpos.ne', one_mul] at this
  have hkey : (1 - η) * (3 * (1 - η)) < (1 - η) * ‖F‖ :=
    mul_lt_mul_of_pos_left hFnorm (by linarith)
  have hgw := (abs_le.mp (abs_apply_le_norm g hw1)).2
  rw [hg1] at hgw
  rw [hF] at hFw
  -- `f(w) = F(w) - 2g(w) > 3(1 - η)² - 2 ≥ 1 - 6η > 1 - ε`, and `‖x + w‖ > 2 - η > 2 - ε`.
  refine ⟨w, hw1, ?_, by linarith⟩
  nlinarith [sq_nonneg η]

/-- A functional of norm one is positive at some point of the unit sphere. -/
lemma exists_norm_eq_one_apply_pos {f : StrongDual ℝ X} (hf : ‖f‖ = 1) :
    ∃ z : X, ‖z‖ = 1 ∧ 0 < f z := by
  -- `f ≠ 0`, so `f v ≠ 0` for some `v`; replace `v` by `-v` if needed to get `f u > 0`.
  obtain ⟨v, hv⟩ : ∃ v : X, f v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : f = 0 := ContinuousLinearMap.ext hcon
    rw [this, norm_zero] at hf
    exact zero_ne_one hf
  obtain ⟨u, hu⟩ : ∃ u : X, 0 < f u := by
    rcases hv.lt_or_gt with h | h
    · exact ⟨-v, by rw [map_neg]; linarith⟩
    · exact ⟨v, h⟩
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [map_zero] at hu
    exact lt_irrefl 0 hu
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  -- Normalize: `z = u / ‖u‖`.
  refine ⟨‖u‖⁻¹ • u, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnu.ne']
  · rw [map_smul, smul_eq_mul]
    exact mul_pos (inv_pos.mpr hnu) hu

/-- **Core of Theorem 2.2.** Let `X` be a real normed space with `dim X > 1`. If every point of
`S_X` is a positive square point, then every point of `S_X` is a Daugavet point.

Together with Proposition 2.1 (KMM2007) and KSSW Lemma 2.2, this is the nontrivial direction of
Theorem 2.2. Completeness of `X` is not needed. -/
theorem isDaugavetPoint_of_forall_isPositiveSquarePoint
    (hdim : 1 < Module.rank ℝ X)
    (h : ∀ z : X, ‖z‖ = 1 → IsPositiveSquarePoint z) :
    ∀ x : X, ‖x‖ = 1 → IsDaugavetPoint x := by
  intro x hx
  refine ⟨hx, fun f hf => ?_⟩
  -- `U` is the union of the open balls of radius `1/4` around the points of
  -- `A_f = {z ∈ S_X : (z, f) is good}`. It is an open subset of `X`.
  obtain ⟨U, hU⟩ : ∃ U : Set X,
      U = ⋃ z ∈ {z : X | ‖z‖ = 1 ∧ IsGood z f}, Metric.ball z (1 / 4) := ⟨_, rfl⟩
  have hmemU : ∀ v, v ∈ U ↔ ∃ z, (‖z‖ = 1 ∧ IsGood z f) ∧ ‖v - z‖ < 1 / 4 := by
    intro v
    rw [hU]
    simp only [Set.mem_iUnion, Metric.mem_ball, dist_eq_norm, exists_prop, Set.mem_ofPred_eq]
  have hU_open : IsOpen U := by
    rw [hU]
    exact isOpen_biUnion fun _ _ => Metric.isOpen_ball
  -- Every point of `A_f` lies in `U`.
  have hAU : ∀ z : X, ‖z‖ = 1 → IsGood z f → z ∈ U := fun z hz hzf =>
    (hmemU z).mpr ⟨z, ⟨hz, hzf⟩, by rw [sub_self, norm_zero]; norm_num⟩
  -- By (★), every point of `S_X` that lies in `U` belongs to `A_f`.
  have hUA : ∀ v : X, ‖v‖ = 1 → v ∈ U → IsGood v f := by
    intro v hv hvU
    obtain ⟨z, ⟨hz, hzf⟩, hvz⟩ := (hmemU v).mp hvU
    exact isGood_of_norm_sub_lt_half h hf hz hzf hv (by linarith)
  -- `A_f` is nonempty: it contains every `z ∈ S_X` with `f(z) > 0`.
  obtain ⟨z₀, hz₀, hfz₀⟩ := exists_norm_eq_one_apply_pos hf
  -- The sphere is connected, meets `U`, and `closure U ∩ S_X ⊆ U`; hence `S_X ⊆ U`.
  have hsub : Metric.sphere (0 : X) 1 ⊆ U := by
    refine (isPreconnected_sphere hdim 0 1).subset_of_closure_inter_subset hU_open ?_ ?_
    · exact ⟨z₀, mem_sphere_zero_iff_norm.mpr hz₀,
        hAU z₀ hz₀ ((h z₀ hz₀).2 f hf hfz₀.le)⟩
    · rintro v ⟨hvcl, hvS⟩
      rw [mem_sphere_zero_iff_norm] at hvS
      -- Some `v' ∈ U` has `‖v - v'‖ < 1/4`, and `v'` is within `1/4` of some `z ∈ A_f`,
      -- so `‖v - z‖ < 1/2` and (★) gives `v ∈ A_f`.
      obtain ⟨v', hv'U, hvv'⟩ := Metric.mem_closure_iff.mp hvcl (1 / 4) (by norm_num)
      obtain ⟨z, ⟨hz, hzf⟩, hv'z⟩ := (hmemU v').mp hv'U
      rw [dist_eq_norm] at hvv'
      have hvz : ‖v - z‖ < 1 / 2 := by
        calc ‖v - z‖ = ‖(v - v') + (v' - z)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖v - v'‖ + ‖v' - z‖ := norm_add_le _ _
          _ < 1 / 2 := by linarith
      exact hAU v hvS (isGood_of_norm_sub_lt_half h hf hz hzf hvS hvz)
  exact hUA x hx (hsub (mem_sphere_zero_iff_norm.mpr hx))

/-- **Theorem 2.2.** Let `X` be a real normed space with `dim X > 1`. Then `X` has the positive
square Daugavet property if and only if it has the Daugavet property. (The paper assumes `X`
Banach; completeness is not needed.) -/
theorem hasSquareDaugavetProperty_one_iff_hasDaugavetProperty
    (hdim : 1 < Module.rank ℝ X) :
    HasSquareDaugavetProperty X 1 ↔ HasDaugavetProperty X := by
  -- `dim X > 1` gives `X ≠ {0}`, which Proposition 2.1 needs.
  have : Nontrivial X := rank_pos_iff_nontrivial.mp (zero_lt_one.trans hdim)
  -- Proposition 2.1 with `σ = 1`; `hK.out 1 3` is its equivalence (i) ⇔ (iii).
  have hK := kmm_signed (X := X) (σ := 1) (Or.inl rfl)
  -- KSSW Lemma 2.2: the Daugavet property means that every normalized pair is good.
  rw [hasDaugavetProperty_iff_forall_isGood]
  constructor
  · -- By Proposition 2.1, every point of `S_X` is a positive square point; by the core result,
    -- every point of `S_X` is a Daugavet point.
    intro hsq
    have h3 := (hK.out 1 3).mp hsq
    have hpos : ∀ z : X, ‖z‖ = 1 → IsPositiveSquarePoint z := fun z hz =>
      ⟨hz, fun f hf hfz => h3 z hz f hf (by rwa [one_mul])⟩
    intro x hx f hf
    exact (isDaugavetPoint_of_forall_isPositiveSquarePoint hdim hpos x hx).2 f hf
  · -- "Clearly": if every normalized pair is good, so is every pair with `f(x) ≥ 0`.
    intro hgood
    exact (hK.out 1 3).mpr fun x hx f hf _ => hgood x hx f hf

/-- `X` is *extremely non-complex*: `‖Id + T²‖ = 1 + ‖T²‖` for every bounded operator `T`. -/
def IsExtremelyNonComplex (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ T : X →L[ℝ] X, ‖1 + T ^ 2‖ = 1 + ‖T ^ 2‖

/-- An extremely non-complex space has the positive square Daugavet property
(rank-one operators are bounded operators). -/
lemma IsExtremelyNonComplex.hasSquareDaugavetProperty_one (h : IsExtremelyNonComplex X) :
    HasSquareDaugavetProperty X 1 := fun T _ => by
  rw [one_smul]
  exact h T

/-- **Remark 2.3.** `ℝ` is extremely non-complex, hence has the positive square Daugavet
property, but it does not have the Daugavet property (witnessed by `T = -Id`). -/
theorem real_isExtremelyNonComplex_not_hasDaugavetProperty :
    IsExtremelyNonComplex ℝ ∧ HasSquareDaugavetProperty ℝ 1 ∧ ¬ HasDaugavetProperty ℝ := by
  have hENC : IsExtremelyNonComplex ℝ := by
    intro T
    -- Every operator on `ℝ` is `T = t Id` with `t = T 1`, so `T² = t² Id`.
    have hT2 : T ^ 2 = (T 1 * T 1) • (1 : ℝ →L[ℝ] ℝ) := by
      apply ContinuousLinearMap.ext_ring
      rw [pow_two, mul_apply_eq_comp, smul_apply, one_apply_eq_self,
        smul_eq_mul, mul_one]
      simpa using map_smul T (T 1) (1 : ℝ)
    -- `‖Id + t² Id‖ = |1 + t²| = 1 + t² = 1 + ‖t² Id‖`.
    have hc : 0 ≤ T 1 * T 1 := mul_self_nonneg _
    rw [hT2, show (1 : ℝ →L[ℝ] ℝ) + (T 1 * T 1) • 1 = (1 + T 1 * T 1) • (1 : ℝ →L[ℝ] ℝ) by
        rw [add_smul, one_smul],
      norm_smul, norm_smul, norm_one, mul_one, mul_one, Real.norm_of_nonneg hc,
      Real.norm_of_nonneg (by linarith)]
  refine ⟨hENC, hENC.hasSquareDaugavetProperty_one, fun hD => ?_⟩
  -- `T = -Id` has rank one (its range is all of `ℝ`) but `‖Id + T‖ = 0 ≠ 2 = 1 + ‖T‖`.
  have hrange : LinearMap.range ((-1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) = ⊤ :=
    LinearMap.range_eq_top.mpr fun y => ⟨-y, by simp⟩
  have h := hD (-1) (by rw [hrange, finrank_top, Module.finrank_self])
  rw [add_neg_cancel, norm_zero, norm_neg, norm_one] at h
  norm_num at h

/-- **Corollary 2.4.** Every extremely non-complex real normed space of dimension greater than one
has the Daugavet property. (The paper assumes `X` Banach; completeness is not needed.) -/
theorem hasDaugavetProperty_of_isExtremelyNonComplex (hdim : 1 < Module.rank ℝ X)
    (h : IsExtremelyNonComplex X) : HasDaugavetProperty X :=
  (hasSquareDaugavetProperty_one_iff_hasDaugavetProperty hdim).mp
    h.hasSquareDaugavetProperty_one

end SquareDaugavet
