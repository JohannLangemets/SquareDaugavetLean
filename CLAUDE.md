# SquareDaugavet — Lean 4 formalization

Goal: formally verify every result of J. Langemets, *Characterizing the Daugavet property by
squares of rank-one operators*. The paper source is NOT in this repo (gitignored `main.tex`); the
original lives in `C:\Users\johann1\OneDrive - Tartu Ülikool\SquareDaugavetLean\main.tex`.

## Working agreement (from the author)
1. One result at a time. First write only the Lean *statement* and explain in plain English how it
   matches the paper; wait for approval before proving.
2. Run `lake build` after each change and fix errors until it compiles.
3. Never leave `sorry`, `admit`, or new `axiom`s without saying so; list any remaining at the end.
   Final check: `#print axioms <name>` should show only `propext, Classical.choice, Quot.sound`.
4. Explain the main tactics used — the author is new to Lean (but an expert in the mathematics).

## Layout
- `SquareDaugavet/Basic.lean` — definitions (`IsGood`, `IsDaugavetPoint`,
  `IsNegativeSquarePoint`) and helper `abs_apply_le_norm`.
- `SquareDaugavet/NegativeSquarePoint.lean` — Theorem 2.6 (proved, no sorry).
- `SquareDaugavet/NablaPoint.lean` — Proposition 3.2 (proved, no sorry). `slice`, `IsNablaPoint`,
  `IsPositiveSquarePoint` live in Basic.lean; ∇-point uses the literal `sSup` (Real.sSup ∅ = 0).
- `SquareDaugavet/LinftyExample.lean` — Example 3.4; ℓ∞² is `ℝ × ℝ` (Mathlib's max norm).
  `IsDeltaPoint` and `mem_slice` are in Basic.lean.
- New results: one file per result, imported from `SquareDaugavet.lean`; update the README table.
- Conventions: real normed space `X`, dual is `StrongDual ℝ X`; Banach-space results take
  `[CompleteSpace X]`; unit sphere written as `‖x‖ = 1`.

## Status / next
- Done: Theorem 2.2 core (good-pair form, `PositiveGlobal.lean`), Theorem 2.6, Proposition 3.2,
  Example 3.4.
- Done: Prop. 2.1 (`kmm_signed`, a `List.TFAE`) and KSSW Lemma 2.2, in `KMM.lean`, which also
  holds the operator-level definitions `HasDaugavetProperty`, `HasSquareDaugavetProperty X σ`
  (rank-one = `finrank ℝ (LinearMap.range (T : X →ₗ[ℝ] X)) = 1`, `f ⊗ x` = `f.smulRight x`,
  `Id` = `1`, `T²` = `T ^ 2`). The author asked that proofs of cited results mimic the original
  article (KMM: S = (σf(x))^{-1/2} f⊗x, closure/approximation for f(x) = 0).
- Next: Theorem 2.2 in literal operator form (from the core + `kmm_signed` + KSSW), then
  Cor. 2.7, Cor. 2.4 (extremely non-complex), Remarks 2.3, 3.3.
- Later: Example 3.5 (c ⊕₂ ℝ: Δ-point, not positive square point).

## Environment gotchas (Windows)
- elan is not on PATH in existing shells: prefix with `$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"`.
- Imports are narrow (see top of `Basic.lean`), not `import Mathlib`: a full rebuild dropped from
  ~14 min to ~4 min (cold) / <1 min (warm). If a lemma or tactic is missing, add the specific
  Mathlib module to `Basic.lean` rather than going back to `import Mathlib`.
  GitHub Actions CI (`.github/workflows/lean_action_ci.yml`) also builds on every push.
- Never write files with PowerShell 5.1 `Set-Content -Encoding utf8` — it adds a BOM, which Lean
  rejects (`expected token` at 1:0).
- Mathlib here is recent: use `neg_apply`/`add_apply`/`smul_apply` (not the deprecated
  `ContinuousLinearMap.*` versions). `exists_dual_vector ℝ v h` returns `g v = ↑‖v‖`; remove the
  cast with `RCLike.ofReal_real_eq_id, id_eq`.
- Remote: private repo https://github.com/JohannLangemets/SquareDaugavetLean (branch `main`).
