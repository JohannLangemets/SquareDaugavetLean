import SquareDaugavet.Basic

/-!
# A positive square point that is neither a ∇-point nor a Δ-point (Example 3.4)

`ℓ∞²` is `ℝ × ℝ`: Mathlib's norm on a product is the maximum norm, `‖(s, t)‖ = max |s| |t|`.
-/

namespace SquareDaugavet

/-- If every point of a nonempty set `S` lies within distance `1` of `x`, then
`sup_{y ∈ S} ‖x - y‖ ≤ 1`, so in particular it is not `2`. -/
lemma sSup_ne_two {X : Type*} [NormedAddCommGroup X] {x : X} {S : Set X} (hS : S.Nonempty)
    (h : ∀ z ∈ S, ‖x - z‖ ≤ 1) : sSup ((fun y => ‖x - y‖) '' S) ≠ 2 := by
  intro h2
  have : sSup ((fun y => ‖x - y‖) '' S) ≤ 1 :=
    csSup_le (hS.image _) (by rintro _ ⟨z, hz, rfl⟩; exact h z hz)
  linarith

/-- Every functional on `ℓ∞²` is `f(s, t) = s a + t b` with `a = f(1, 0)`, `b = f(0, 1)`. -/
lemma apply_prod (f : StrongDual ℝ (ℝ × ℝ)) (s t : ℝ) :
    f (s, t) = s * f (1, 0) + t * f (0, 1) := by
  have : ((s, t) : ℝ × ℝ) = s • ((1 : ℝ), (0 : ℝ)) + t • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- `‖f‖ ≤ |a| + |b|` for `f = (a, b)`: the easy half of `(ℓ∞²)* = ℓ₁²`. -/
lemma norm_le_abs_add_abs (f : StrongDual ℝ (ℝ × ℝ)) :
    ‖f‖ ≤ |f (1, 0)| + |f (0, 1)| := by
  refine ContinuousLinearMap.opNorm_le_bound f (add_nonneg (abs_nonneg _) (abs_nonneg _)) ?_
  rintro ⟨s, t⟩
  rw [apply_prod f s t]
  simp only [Prod.norm_mk, Real.norm_eq_abs]
  calc |s * f (1, 0) + t * f (0, 1)| ≤ |s * f (1, 0)| + |t * f (0, 1)| := abs_add_le _ _
    _ = |s| * |f (1, 0)| + |t| * |f (0, 1)| := by rw [abs_mul, abs_mul]
    _ ≤ max |s| |t| * |f (1, 0)| + max |s| |t| * |f (0, 1)| :=
        add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))
    _ = (|f (1, 0)| + |f (0, 1)|) * max |s| |t| := by ring

/-- A point `(s, t)` of `B_{ℓ∞²}` has `|s| ≤ 1` and `|t| ≤ 1`. -/
lemma abs_le_one_of_norm_le_one {s t : ℝ} (h : ‖((s, t) : ℝ × ℝ)‖ ≤ 1) :
    |s| ≤ 1 ∧ |t| ≤ 1 := by
  simpa only [Prod.norm_mk, Real.norm_eq_abs, max_le_iff] using h

/-- Points `(s, t)` of `B_{ℓ∞²}` with `s ≥ 0` lie within distance `1` of `(1, 0)`:
`‖(1, 0) - (s, t)‖ = max {|1 - s|, |t|} ≤ 1`. -/
lemma norm_one_zero_sub_le {s t : ℝ} (hs : |s| ≤ 1) (ht : |t| ≤ 1) (hs0 : 0 ≤ s) :
    ‖((1 : ℝ), (0 : ℝ)) - (s, t)‖ ≤ 1 := by
  rw [Prod.mk_sub_mk]
  simp only [Prod.norm_mk, Real.norm_eq_abs, max_le_iff]
  rw [abs_le] at hs ht
  constructor <;> rw [abs_le] <;> constructor <;> linarith

/-- **Example 3.4.** In `X = ℓ∞²`, the point `x = (1, 0)` is a positive square point but is
neither a ∇-point nor a Δ-point. -/
theorem ex_linfty :
    IsPositiveSquarePoint ((1, 0) : ℝ × ℝ) ∧
      ¬ IsNablaPoint ((1, 0) : ℝ × ℝ) ∧ ¬ IsDeltaPoint ((1, 0) : ℝ × ℝ) := by
  have hx1 : ‖((1, 0) : ℝ × ℝ)‖ = 1 := by
    rw [Prod.norm_mk, norm_one, norm_zero, max_eq_left zero_le_one]
  refine ⟨⟨hx1, fun f hf hfx ε hε => ?_⟩, ?_, ?_⟩
  · -- "Let `f = (a, b) ∈ S_{ℓ₁²}` with `f(x) = a ≥ 0`. Choose `y = (1, sgn b)`.
    -- Then `f(y) = a + |b| = 1` and `‖x + y‖∞ = 2`."
    -- We only need `f(y) = a + |b| ≥ ‖f‖ = 1`.
    have hnorm := norm_le_abs_add_abs f
    rw [hf, abs_of_nonneg hfx] at hnorm
    rcases le_or_gt 0 (f (0, 1)) with hb | hb
    · -- `b ≥ 0`: `y = (1, 1)`.
      rw [abs_of_nonneg hb] at hnorm
      refine ⟨(1, 1), ?_, ?_, ?_⟩
      · simp only [Prod.norm_mk, Real.norm_eq_abs, abs_one, max_self]
      · rw [apply_prod f 1 1]
        linarith
      · rw [Prod.mk_add_mk]
        simp only [Prod.norm_mk, Real.norm_eq_abs]
        exact lt_max_of_lt_left (lt_of_lt_of_le (by linarith) (le_abs_self _))
    · -- `b < 0`: `y = (1, -1)`.
      rw [abs_of_neg hb] at hnorm
      refine ⟨(1, -1), ?_, ?_, ?_⟩
      · simp only [Prod.norm_mk, Real.norm_eq_abs, abs_neg, abs_one, max_self]
      · rw [apply_prod f 1 (-1)]
        linarith
      · rw [Prod.mk_add_mk]
        simp only [Prod.norm_mk, Real.norm_eq_abs]
        exact lt_max_of_lt_left (lt_of_lt_of_le (by linarith) (le_abs_self _))
  · -- "For `g = (1/2, 1/2)`, the slice `S(g, 1/4)` excludes `x`. If `z = (s, t)` belongs to this
    -- slice, then `s + t > 3/2`, so `s, t > 1/2`. Therefore `‖x - z‖∞ ≤ 1`."
    rintro ⟨-, hnabla⟩
    set g : StrongDual ℝ (ℝ × ℝ) :=
      (1 / 2 : ℝ) • (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ) with hg_def
    have hg : ∀ s t : ℝ, g (s, t) = (s + t) / 2 := fun s t => by
      simp [hg_def]; ring
    have hg1 : ‖g‖ = 1 := by
      apply le_antisymm
      · have := norm_le_abs_add_abs g
        norm_num [hg] at this
        linarith
      · have := g.le_opNorm (1, 1)
        norm_num [hg, Prod.norm_mk] at this
        linarith
    have hnot : ((1, 0) : ℝ × ℝ) ∉ slice g (1 / 4) := by
      rw [mem_slice, hg]
      norm_num
    have hmem : ((1, 1) : ℝ × ℝ) ∈ slice g (1 / 4) := by
      rw [mem_slice, hg]
      refine ⟨by simp only [Prod.norm_mk, Real.norm_eq_abs, abs_one, max_self, le_refl], ?_⟩
      norm_num
    have hbound : ∀ z ∈ slice g (1 / 4), ‖((1, 0) : ℝ × ℝ) - z‖ ≤ 1 := by
      rintro ⟨s, t⟩ hz
      rw [mem_slice, hg] at hz
      obtain ⟨hs, ht⟩ := abs_le_one_of_norm_le_one hz.1
      have ht' := (abs_le.mp ht).2
      exact norm_one_zero_sub_le hs ht (by linarith [hz.2])
    exact sSup_ne_two (Set.nonempty_of_mem hmem) hbound
      (hnabla g hg1 (1 / 4) (by norm_num) hnot)
  · -- "For `h = (1, 0)`, the slice `S(h, 1/2)` contains `x`, and every point of this slice also
    -- has distance at most one from `x`."
    rintro ⟨-, hdelta⟩
    set h : StrongDual ℝ (ℝ × ℝ) := ContinuousLinearMap.fst ℝ ℝ ℝ with hh_def
    have hh : ∀ s t : ℝ, h (s, t) = s := fun s t => by simp [hh_def]
    have hh1 : ‖h‖ = 1 := by
      apply le_antisymm
      · have := norm_le_abs_add_abs h
        norm_num [hh] at this
        linarith
      · have := h.le_opNorm (1, 0)
        rw [hh, hx1, norm_one, mul_one] at this
        exact this
    have hmem : ((1, 0) : ℝ × ℝ) ∈ slice h (1 / 2) := by
      rw [mem_slice, hh]
      exact ⟨hx1.le, by norm_num⟩
    have hbound : ∀ z ∈ slice h (1 / 2), ‖((1, 0) : ℝ × ℝ) - z‖ ≤ 1 := by
      rintro ⟨s, t⟩ hz
      rw [mem_slice, hh] at hz
      obtain ⟨hs, ht⟩ := abs_le_one_of_norm_le_one hz.1
      exact norm_one_zero_sub_le hs ht (by linarith [hz.2])
    exact sSup_ne_two (Set.nonempty_of_mem hmem) hbound
      (hdelta h hh1 (1 / 2) (by norm_num) hmem)

end SquareDaugavet
