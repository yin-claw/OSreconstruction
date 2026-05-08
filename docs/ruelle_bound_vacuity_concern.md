# `RuelleAnalyticClusterHypotheses.bound` vacuity concern

**Date**: 2026-05-08
**Surfaced during**: L4 (uniform polynomial bound) axiom-vetting via Gemini chat.
**Status (2026-05-08, later)**: **Repaired via Option A** (boundary-distance regulator). See "Resolution" at the bottom.
**Severity**: medium — pre-existing structural issue; resolved on branch `r2e/ruelle-l5-grind`.

## Summary

The `bound` field of `RuelleAnalyticClusterHypotheses` in
`OSReconstruction/Wightman/Reconstruction/WickRotation/RuelleClusterBound.lean:151–167`
was, as originally formulated, **mathematically unsatisfiable** for
any actual Wightman QFT. Adding a production axiom asserting it would
have introduced inconsistency (the system would prove `False`). The
conditional cluster theorem consuming `RuelleAnalyticClusterHypotheses`
was formally correct but its premise was vacuous in general — only
model-specific or boundary-restricted instances could supply it.

## The current bound

```lean
bound : ∃ (C : ℝ) (N : ℕ) (R : ℝ),
  0 < C ∧ 0 < R ∧
  ∀ (z₁ : Fin n → Fin (d + 1) → ℂ),
  ∀ (z₂ : Fin m → Fin (d + 1) → ℂ),
    z₁ ∈ ForwardTube d n →
    z₂ ∈ ForwardTube d m →
    ∀ (a : SpacetimeDim d), a 0 = 0 →
      (∑ i : Fin d, (a (Fin.succ i)) ^ 2) > R ^ 2 →
      (joint_config) ∈ PermutedExtendedTube d (n + m) →
      ‖(W_analytic_BHW Wfn (n + m)).val (joint_config)‖
        ≤ C * (1 + ‖z₁‖ + ‖z₂‖) ^ N
```

The constants `C, N` are quantified **outside** `∀ z₁, z₂`. The bound
must therefore hold uniformly over the entire forward tube, with the
polynomial only in `‖z‖` (which does not blow up at the tube boundary).

## Free-field counterexample

For `n = m = 2`, Wick's theorem gives
```
W_4(z₁,₁, z₁,₂, z₂,₁ + a, z₂,₂ + a)
  = W₂(z₁,₁, z₁,₂) · W₂(z₂,₁ + a, z₂,₂ + a)
  + W₂(z₁,₁, z₂,₁ + a) · W₂(z₁,₂, z₂,₂ + a)
  + W₂(z₁,₁, z₂,₂ + a) · W₂(z₁,₂, z₂,₁ + a)
```

The first term:
- Decomposes as a product where the `z₁`-only factor `W₂(z₁,₁, z₁,₂)`
  is independent of `a`.
- The free-field 2-point function `W₂(z, w) = ((z - w)² + m²)⁻¹` (with
  appropriate Lorentz signature) blows up as `(z₁,₁ - z₁,₂) → ∂V+`,
  which is allowed within `ForwardTube d 2` (the tube is open).
- For fixed `(z₂,₁, z₂,₂, a)`, sending `(z₁,₁ - z₁,₂)` toward `∂V+`
  drives `‖W_4‖ → ∞` while `(1 + ‖z₁‖ + ‖z₂‖)^N` stays bounded.

No global `(C, N)` can therefore witness the bound — the hypothesis
is unsatisfiable for the free scalar field.

## What the textbook actually says

**Streater-Wightman Theorem 3.1.1**:
```
‖W(z)‖ ≤ C · (1 + ‖z‖)^N · (1 + Δ(Im z)⁻¹)^M
```
where `Δ(y)` is the invariant distance of the imaginary-difference
variables to `∂V+`. The boundary-distance factor `Δ(y)⁻¹` is essential.

**Bogoliubov-Logunov-Todorov, Axiomatic QFT, Theorem 11.2**: same
shape, on the extended tube `T'`:
```
‖W(z)‖ ≤ C · (1 + ‖z‖)^N · dist(z, ∂T')⁻ᴷ
```

**Ruelle 1962 / Araki-Hepp-Ruelle 1962**: the cluster theorem proofs
work natively with **smeared** distributions (Schwartz test functions
absorb the boundary singularities), avoiding the pointwise bound issue
entirely. The pointwise version on the analytic side comes from the
Streater-Wightman polynomial-behavior theorem and inherits its
boundary-distance factor.

## Two repair options

### Option A — boundary-distance regulator (faithful to S-W)

Add the `Δ(Im z)⁻ᴹ` factor to the bound. Requires defining a
`tubeBoundaryDist : ForwardTube d n → ℝ` (or analog) and threading it
through the bound:
```lean
bound : ∃ (C : ℝ) (N M : ℕ) (R : ℝ),
  ... ‖W_analytic_BHW(joint_config)‖
    ≤ C * (1 + ‖z₁‖ + ‖z₂‖)^N
       * (1 + tubeBoundaryDist z₁⁻¹)^M
       * (1 + tubeBoundaryDist z₂⁻¹)^M
```

Pros: matches Streater-Wightman exactly; satisfiable for free fields.
Cons: requires defining `tubeBoundaryDist`; threads through downstream
consumers of `RuelleAnalyticClusterHypotheses`.

### Option B — quantifier reordering (compact-base form)

Move `∃ C, N` *inside* `∀ z₁, z₂` (or inside `∀ y₁, y₂` for fixed
imaginary parts):
```lean
bound : ∀ (z₁ : Fin n → ...) (z₂ : Fin m → ...),
  z₁ ∈ ForwardTube d n → z₂ ∈ ForwardTube d m →
  ∃ (C : ℝ) (N : ℕ) (R : ℝ),
    0 < C ∧ 0 < R ∧
    ∀ (a : SpacetimeDim d), a 0 = 0 →
      (∑ i, (a (Fin.succ i))^2) > R^2 →
      (joint_config) ∈ PET d (n + m) →
      ‖W_analytic_BHW(joint_config)‖ ≤ C * (1 + ‖z₁‖ + ‖z₂‖)^N
```

Pros: minimal-change refactor; satisfiable point-by-point
(`C, N` are allowed to blow up as `(z₁, z₂)` approach the boundary).
Cons: weaker than the textbook statement; the cluster-theorem
*proof* may need adjustment if it relied on pointwise-uniform
constants for downstream estimates (likely not — the cluster proof
fixes `(z₁, z₂)` and varies `a`).

## Recommendation

- **Short term** (this branch): document the issue (this file). Do
  *not* axiomatize `L4SpectralData` or any structurally-equivalent
  unconditional discharge — that would introduce inconsistency. Keep
  the conditional reduction `ruelle_analytic_cluster_bound_of` as
  scaffolding.
- **Medium term**: refactor `RuelleAnalyticClusterHypotheses.bound`
  to Option B (lower-cost change). Verify the cluster theorem proof
  still goes through with pointwise `C, N`. Coordinate with @xiyin137
  per `CLAUDE.md` shared-repo policy.
- **Long term**: prove the boundary-regulated bound (Option A form)
  from the Streater-Wightman polynomial-behavior theorem +
  `spectrum_condition`, removing the hypothesis entirely.

## Effect on the L4 file

`OSReconstruction/Wightman/Spectral/Ruelle/L4_UniformPolynomialBound.lean`
contains:

* `L4SpectralData` — a structural hypothesis whose shape mirrors
  `RuelleAnalyticClusterHypotheses.bound`. Defined for completeness;
  inherits the same satisfiability concern.
* `ruelle_analytic_cluster_bound_of` — the conditional reduction
  (proved). This is `(possibly-vacuous antecedent) → (possibly-vacuous
  conclusion)` and remains valid regardless of whether the antecedent
  is satisfiable.
* **No production axiom** (intentionally).

Once `RuelleAnalyticClusterHypotheses.bound` is repaired, both
`L4SpectralData` and the conditional reduction will be updated
to mirror the new shape, and a vetted production axiom can be
considered.

## Resolution (2026-05-08, same day, Option A applied on `r2e/ruelle-l5-grind`)

Option A was implemented:

1. **`tubeBoundaryDist`** defined in `RuelleClusterBound.lean:166`:
   for `z : Fin n → Fin (d+1) → ℂ`, takes the minimum
   `Metric.infDist` of consecutive imaginary differences `Im(z_k -
   z_{k-1})` to the closed complement of the open forward cone
   `(openForwardConeSet d)ᶜ`. Returns `1` for `n = 0`.
2. **`RuelleAnalyticClusterHypotheses.bound`** updated to include the
   factor `(1 + (tubeBoundaryDist z₁)⁻¹)^M · (1 + (tubeBoundaryDist
   z₂)⁻¹)^M` with new exponent `M`. Now matches Streater-Wightman
   3.1.1 shape (and aligns with the proven
   `fourierLaplaceExtMultiDim_vladimirov_growth` in
   `OSReconstruction/SCV/PaleyWienerSchwartz.lean:3286`).
3. **`L4SpectralData`** updated to mirror the new shape; the
   conditional reduction `ruelle_analytic_cluster_bound_of`
   re-proved with the regulator.
4. **`wightman_l4_spectral_data_axiom`** now shipped (vetted "Likely
   correct / Standard" by Gemini chat after the regulator fix);
   discharges `RACH.bound` unconditionally.
5. **Active sorry**: `W_analytic_cluster_integral_via_ruelle`
   (`RuelleClusterBound.lean:718`) — the dominator-integrability
   step. The new dominator includes the regulator factor
   `(1 + (tubeBoundaryDist (wick z))⁻¹)^M` after Wick rotation,
   which becomes `min_k (x_k 0 - x_{k-1} 0)`-style for OPTR
   configs. For `M ≥ 1`, naive local integrability fails (the
   diagonal singularity is codim-1). Resolution requires IBP in
   the time differences, transferring derivatives onto Schwartz
   `f, g` — Streater-Wightman §3.4 / Ruelle 1962. This is its own
   ~1–2 week follow-up; the project Vladimirov-Tillmann
   infrastructure (`bv_implies_fourier_support`,
   `fl_representation_from_bv`, `fourierLaplaceExtMultiDim_*`)
   provides the building blocks.

PR forthcoming on `r2e/ruelle-l5-grind` → `myfork`.

## References

* Streater, R. F., and Wightman, A. S. *PCT, Spin and Statistics, and
  All That*. Princeton University Press, 1964 (and reprints). §3.1
  (Theorem 3.1.1) and §3.4 (cluster theorem).
* Bogoliubov, N. N.; Logunov, A. A.; Todorov, I. T. *Introduction to
  Axiomatic Quantum Field Theory*. Benjamin, 1975. Theorem 11.2.
* Ruelle, D. "On the asymptotic condition in quantum field theory."
  *Helvetica Physica Acta* 35 (1962), 147–163.
* Araki, H.; Hepp, K.; Ruelle, D. "On the asymptotic behaviour of
  Wightman functions in space-like directions." *Helvetica Physica
  Acta* 35 (1962), 164–174.
* Glimm, J., and Jaffe, A. *Quantum Physics: A Functional Integral
  Point of View*. 2nd ed., Springer, 1987. Chapter 19.
