import SquareDaugavet.Basic

/-!
# A Δ-point that is not a positive square point (Example 3.5)

`c` is the space of convergent real sequences with the supremum norm. We realize it as the
subspace `convergentSeq` of `ℓ∞ = ℕ →ᵇ ℝ` (bounded sequences with the sup norm), and
`c ⊕₂ ℝ` as `WithLp 2 (convergentSeq × ℝ)`, whose norm is `‖(v, t)‖ = √(‖v‖∞² + t²)`.

The paper argues that `yₙ = (𝟏 - 2eₙ, 0)` converges weakly to `x = (𝟏, 0)` and that slices are
relatively weakly open. We prove the special case that is needed directly:
`f(eₙ, 0) → 0` for every `f ∈ X*` (`tendsto_apply_inl_e`), because
`∑_{n<N} |f(eₙ, 0)| = f(∑_{n<N} ±eₙ, 0) ≤ ‖f‖`.
-/

open Filter Topology BoundedContinuousFunction

namespace SquareDaugavet

/-- The space `c` of convergent real sequences with the supremum norm, as a subspace of
`ℓ∞ = ℕ →ᵇ ℝ` (bounded sequences with the sup norm). -/
def convergentSeq : Submodule ℝ (ℕ →ᵇ ℝ) where
  carrier := {f | ∃ L : ℝ, Tendsto (fun n => f n) atTop (𝓝 L)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro f g ⟨L, hL⟩ ⟨M, hM⟩
    exact ⟨L + M, by simpa using hL.add hM⟩
  smul_mem' := by
    rintro a f ⟨L, hL⟩
    exact ⟨a * L, by simpa using hL.const_mul a⟩

/-- The constant sequence `𝟏 = (1, 1, 1, …) ∈ c`. -/
def oneSeq : convergentSeq :=
  ⟨BoundedContinuousFunction.const ℕ 1, 1, tendsto_const_nhds⟩

/-- `c ⊕₂ ℝ`. -/
abbrev CSum := WithLp 2 (convergentSeq × ℝ)

/-! ### Elements of `c` -/

/-- Coordinates of sums, differences and scalar multiples in `c`. -/
lemma coe_add_apply (v w : convergentSeq) (k : ℕ) :
    ((v + w : convergentSeq) : ℕ →ᵇ ℝ) k = (v : ℕ →ᵇ ℝ) k + (w : ℕ →ᵇ ℝ) k :=
  rfl

lemma coe_sub_apply (v w : convergentSeq) (k : ℕ) :
    ((v - w : convergentSeq) : ℕ →ᵇ ℝ) k = (v : ℕ →ᵇ ℝ) k - (w : ℕ →ᵇ ℝ) k :=
  rfl

lemma coe_smul_apply (a : ℝ) (v : convergentSeq) (k : ℕ) :
    ((a • v : convergentSeq) : ℕ →ᵇ ℝ) k = a * (v : ℕ →ᵇ ℝ) k :=
  rfl

lemma oneSeq_apply (k : ℕ) : ((oneSeq : convergentSeq) : ℕ →ᵇ ℝ) k = 1 :=
  rfl

/-- A sequence `u` with `|u k| ≤ 1` for all `k` and `u k = 0` for `k ≥ N`, as an element
of `c` (it converges to `0`). -/
def mkC (u : ℕ → ℝ) (N : ℕ) (hN : ∀ k, N ≤ k → u k = 0) (hu : ∀ k, |u k| ≤ 1) :
    convergentSeq :=
  ⟨BoundedContinuousFunction.mkOfDiscrete u 2 fun a b => by
      have ha := abs_le.mp (hu a)
      have hb := abs_le.mp (hu b)
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2],
    0, tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop N] with k hk
      exact (hN k hk).symm)⟩

lemma mkC_apply (u : ℕ → ℝ) (N : ℕ) (hN : ∀ k, N ≤ k → u k = 0) (hu : ∀ k, |u k| ≤ 1)
    (k : ℕ) : ((mkC u N hN hu : convergentSeq) : ℕ →ᵇ ℝ) k = u k :=
  rfl

lemma norm_mkC_le (u : ℕ → ℝ) (N : ℕ) (hN : ∀ k, N ≤ k → u k = 0) (hu : ∀ k, |u k| ≤ 1) :
    ‖mkC u N hN hu‖ ≤ 1 := by
  rw [← Submodule.norm_coe]
  refine (BoundedContinuousFunction.norm_le zero_le_one).mpr fun k => ?_
  rw [mkC_apply, Real.norm_eq_abs]
  exact hu k

/-- The coordinate vector `eₙ ∈ c`. -/
def e (n : ℕ) : convergentSeq :=
  mkC (fun k => if k = n then 1 else 0) (n + 1)
    (fun k hk => by rw [ite_eq_right_iff]; intro h; exact absurd h (by omega))
    (fun k => by split_ifs <;> simp)

lemma e_apply (n k : ℕ) : ((e n : convergentSeq) : ℕ →ᵇ ℝ) k = if k = n then 1 else 0 :=
  rfl

lemma norm_e (n : ℕ) : ‖e n‖ = 1 := by
  refine le_antisymm (norm_mkC_le ..) ?_
  have := BoundedContinuousFunction.norm_coe_le_norm (e n : ℕ →ᵇ ℝ) n
  simpa [e_apply] using this

lemma norm_oneSeq : ‖oneSeq‖ = 1 := by
  rw [← Submodule.norm_coe]
  exact (BoundedContinuousFunction.norm_const_eq (1 : ℝ)).trans norm_one

/-- `‖𝟏 - 2eₙ‖∞ ≤ 1`: its coordinates are `±1`. -/
lemma norm_oneSeq_sub_le (n : ℕ) : ‖oneSeq - (2 : ℝ) • e n‖ ≤ 1 := by
  rw [← Submodule.norm_coe]
  refine (BoundedContinuousFunction.norm_le zero_le_one).mpr fun k => ?_
  rw [coe_sub_apply, coe_smul_apply, oneSeq_apply, e_apply, Real.norm_eq_abs]
  split_ifs <;> norm_num

/-- The partial sign sums `∑_{n<N} σₙ eₙ ∈ c` (for `|σₙ| ≤ 1`). -/
def partialSeq (σ : ℕ → ℝ) (hσ : ∀ k, |σ k| ≤ 1) (N : ℕ) : convergentSeq :=
  mkC (fun k => if k < N then σ k else 0) N
    (fun k hk => by rw [ite_eq_right_iff]; intro h; exact absurd h (by omega))
    (fun k => by split_ifs <;> simp [hσ k])

lemma partialSeq_apply (σ : ℕ → ℝ) (hσ : ∀ k, |σ k| ≤ 1) (N k : ℕ) :
    ((partialSeq σ hσ N : convergentSeq) : ℕ →ᵇ ℝ) k = if k < N then σ k else 0 :=
  rfl

lemma partialSeq_zero (σ : ℕ → ℝ) (hσ : ∀ k, |σ k| ≤ 1) : partialSeq σ hσ 0 = 0 := by
  apply Subtype.ext
  ext k
  simp [partialSeq_apply]

lemma partialSeq_succ (σ : ℕ → ℝ) (hσ : ∀ k, |σ k| ≤ 1) (N : ℕ) :
    partialSeq σ hσ (N + 1) = partialSeq σ hσ N + σ N • e N := by
  apply Subtype.ext
  ext k
  rw [coe_add_apply, coe_smul_apply, partialSeq_apply, partialSeq_apply, e_apply]
  split_ifs <;> first | (exfalso; omega) | simp_all

/-! ### The embedding `v ↦ (v, 0)` of `c` into `c ⊕₂ ℝ` -/

/-- `inl v = (v, 0) ∈ c ⊕₂ ℝ`. -/
def inl (v : convergentSeq) : CSum := WithLp.toLp 2 (v, 0)

lemma inl_zero : inl 0 = 0 := rfl

lemma inl_add (v w : convergentSeq) : inl (v + w) = inl v + inl w := by
  rw [inl, inl, inl, ← WithLp.toLp_add, Prod.mk_add_mk, add_zero]

lemma inl_sub (v w : convergentSeq) : inl (v - w) = inl v - inl w := by
  rw [inl, inl, inl, ← WithLp.toLp_sub, Prod.mk_sub_mk, sub_zero]

lemma inl_smul (a : ℝ) (v : convergentSeq) : inl (a • v) = a • inl v := by
  rw [inl, inl, ← WithLp.toLp_smul, Prod.smul_mk, smul_zero]

lemma norm_inl (v : convergentSeq) : ‖inl v‖ = ‖v‖ := by
  rw [inl, WithLp.prod_norm_eq_of_L2]
  simp

/-! ### `f(eₙ, 0) → 0` for every functional `f` -/

/-- For every `f ∈ (c ⊕₂ ℝ)*`, `f(eₙ, 0) → 0`: choosing signs `σₙ` with
`σₙ f(eₙ, 0) = |f(eₙ, 0)|`, we get `∑_{n<N} |f(eₙ, 0)| = f(∑_{n<N} σₙ eₙ, 0) ≤ ‖f‖`, so the
series `∑ |f(eₙ, 0)|` converges. -/
lemma tendsto_apply_inl_e (f : StrongDual ℝ CSum) :
    Tendsto (fun n => f (inl (e n))) atTop (𝓝 0) := by
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℕ → ℝ, ∀ n, σ n = if 0 ≤ f (inl (e n)) then 1 else -1 :=
    ⟨_, fun _ => rfl⟩
  have hσ : ∀ k, |σ k| ≤ 1 := fun k => by rw [hσdef]; split_ifs <;> simp
  have hσa : ∀ k, σ k * f (inl (e k)) = |f (inl (e k))| := fun k => by
    rw [hσdef]
    split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [neg_one_mul, abs_of_neg (not_le.mp h)]
  -- `f(∑_{n<N} σₙ eₙ, 0) = ∑_{n<N} |f(eₙ, 0)|`.
  have hpart : ∀ N, f (inl (partialSeq σ hσ N)) = ∑ n ∈ Finset.range N, |f (inl (e n))| := by
    intro N
    induction N with
    | zero => rw [partialSeq_zero, inl_zero, map_zero, Finset.sum_range_zero]
    | succ N ih =>
      rw [partialSeq_succ, inl_add, inl_smul, map_add, map_smul, ih, Finset.sum_range_succ,
        smul_eq_mul, hσa]
  -- `‖(∑_{n<N} σₙ eₙ, 0)‖ ≤ 1`, so these partial sums are at most `‖f‖`.
  have hbound : ∀ N, ∑ n ∈ Finset.range N, |f (inl (e n))| ≤ ‖f‖ := by
    intro N
    rw [← hpart]
    calc f (inl (partialSeq σ hσ N)) ≤ ‖f (inl (partialSeq σ hσ N))‖ := le_abs_self _
      _ ≤ ‖f‖ * ‖inl (partialSeq σ hσ N)‖ := f.le_opNorm _
      _ ≤ ‖f‖ * 1 := by
          gcongr
          rw [norm_inl]
          exact norm_mkC_le ..
      _ = ‖f‖ := mul_one _
  have hsum : Summable fun n => |f (inl (e n))| :=
    summable_of_sum_range_le (fun n => abs_nonneg _) hbound
  exact squeeze_zero_norm (fun n => (Real.norm_eq_abs _).le) hsum.tendsto_atTop_zero

/-! ### Example 3.5 -/

/-- **Example 3.5.** In `X = c ⊕₂ ℝ`, the point `x = (𝟏, 0)` is a Δ-point but not a positive
square point. -/
theorem ex_c_sum_real :
    IsDeltaPoint (WithLp.toLp 2 (oneSeq, (0 : ℝ)) : WithLp 2 (convergentSeq × ℝ)) ∧
      ¬ IsPositiveSquarePoint
        (WithLp.toLp 2 (oneSeq, (0 : ℝ)) : WithLp 2 (convergentSeq × ℝ)) := by
  -- `x = (𝟏, 0) = inl 𝟏`, and `‖x‖ = 1`.
  change IsDeltaPoint (inl oneSeq) ∧ ¬ IsPositiveSquarePoint (inl oneSeq)
  have hx1 : ‖inl oneSeq‖ = 1 := by rw [norm_inl, norm_oneSeq]
  refine ⟨⟨hx1, fun f hf α hα hxS => ?_⟩, ?_⟩
  · -- Δ-point. `yₙ = (𝟏 - 2eₙ, 0) ∈ B_X` and `‖x - yₙ‖ = ‖(2eₙ, 0)‖ = 2`.
    have hy1 : ∀ n, ‖inl (oneSeq - (2 : ℝ) • e n)‖ ≤ 1 := fun n => by
      rw [norm_inl]
      exact norm_oneSeq_sub_le n
    have hdist : ∀ n, ‖inl oneSeq - inl (oneSeq - (2 : ℝ) • e n)‖ = 2 := fun n => by
      rw [← inl_sub, sub_sub_cancel, norm_inl, norm_smul, norm_e, mul_one, Real.norm_two]
    -- `f(yₙ) = f(x) - 2 f(eₙ, 0) → f(x) > 1 - α`, so some `yₙ` lies in the slice.
    have hlim : Tendsto (fun n => f (inl (oneSeq - (2 : ℝ) • e n))) atTop
        (𝓝 (f (inl oneSeq))) := by
      have hfy : ∀ n, f (inl (oneSeq - (2 : ℝ) • e n)) = f (inl oneSeq) - 2 * f (inl (e n)) :=
        fun n => by rw [inl_sub, inl_smul, map_sub, map_smul, smul_eq_mul]
      simp_rw [hfy]
      simpa using ((tendsto_apply_inl_e f).const_mul 2).const_sub (f (inl oneSeq))
    rw [mem_slice] at hxS
    obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds hxS.2)).exists
    have hmem : inl (oneSeq - (2 : ℝ) • e n) ∈ slice f α := ⟨hy1 n, hn⟩
    -- Hence `sup_{y ∈ S} ‖x - y‖ = 2`: it is attained at `yₙ`, and `‖x - y‖ ≤ 2` on `B_X`.
    refine IsGreatest.csSup_eq ⟨⟨_, hmem, hdist n⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    calc ‖inl oneSeq - z‖ ≤ ‖inl oneSeq‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [hx1]; linarith [hz.1]
  · -- Not a positive square point: the functional `g(v, t) = t` has norm one and `g(x) = 0`.
    rintro ⟨-, hpos⟩
    set g : StrongDual ℝ CSum := WithLp.sndL 2 ℝ convergentSeq ℝ with hg_def
    have hg : ∀ z : CSum, g z = z.snd := fun z => rfl
    have hg1 : ‖g‖ = 1 := by
      apply le_antisymm
      · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
        rw [hg, one_mul]
        exact WithLp.norm_snd_le _ z
      · have := g.le_opNorm (WithLp.toLp 2 (0, 1))
        simpa [hg, WithLp.prod_norm_eq_of_L2] using this
    -- `(x, g)` is not good for `ε = 1/8`: suppose `y = (v, t) ∈ S_X` has `t > 7/8` and
    -- `‖x + y‖ > 15/8`.
    obtain ⟨y, hy1, hgy, hxy⟩ :=
      hpos g hg1 (by rw [hg]; simp [inl]) (1 / 8) (by norm_num)
    rw [hg] at hgy
    -- `‖v‖∞² + t² = 1`.
    have hy2 := WithLp.prod_norm_sq_eq_of_L2 y
    rw [hy1, Real.norm_eq_abs, sq_abs] at hy2
    -- `‖x + y‖² = ‖𝟏 + v‖∞² + t²`.
    have hxy2 := WithLp.prod_norm_sq_eq_of_L2 (inl oneSeq + y)
    rw [WithLp.add_fst, WithLp.add_snd, Real.norm_eq_abs, sq_abs] at hxy2
    have hfst : (inl oneSeq).fst = oneSeq := rfl
    have hsnd : (inl oneSeq).snd = 0 := rfl
    rw [hfst, hsnd, zero_add] at hxy2
    -- `‖𝟏 + v‖∞ ≤ 1 + ‖v‖∞`.
    have hv : ‖oneSeq + y.fst‖ ≤ 1 + ‖y.fst‖ := by
      calc ‖oneSeq + y.fst‖ ≤ ‖oneSeq‖ + ‖y.fst‖ := norm_add_le _ _
        _ = 1 + ‖y.fst‖ := by rw [norm_oneSeq]
    have hn0 := norm_nonneg y.fst
    -- `‖v‖∞² = 1 - t² < 1/4`, so `‖v‖∞ < 1/2`.
    have hs : ‖y.fst‖ < 1 / 2 := by nlinarith
    -- `‖x + y‖² ≤ (1 + ‖v‖∞)² + t² = 2 + 2‖v‖∞ < 3 < (15/8)²`.
    have hA : ‖oneSeq + y.fst‖ ^ 2 ≤ (1 + ‖y.fst‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hv 2
    have hB : (2 - 1 / 8 : ℝ) ^ 2 < ‖inl oneSeq + y‖ ^ 2 :=
      pow_lt_pow_left₀ hxy (by norm_num) two_ne_zero
    nlinarith

end SquareDaugavet
