# Cluster Property Analysis (R→E Direction)

## Scope and contract

This note is **only** about the reverse-direction `E4_cluster` lane.
It must not be read as a generic late reverse-direction positivity/cluster
status note.

Source-checked reverse-direction split (2026-04-08):
- `E2_reflection_positive` and `E4_cluster` do **not** sit on the same status.
- `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean ::
  wickRotatedBoundaryPairing_reflection_positive` is a checked-present theorem
  surface, but it remains **quarantined** because its current proof still runs
  through the false OS=`Wightman` pairing chain.
- `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean ::
  W_analytic_cluster_integral` is instead a live theorem-shaped **Section-4.4
  supplier** on the honest common-BHW/full-`SchwartzNPoint` lane; it is not a
  quarantined theorem, but it is still only upstream input to the final
  `ZeroDiagonalSchwartz` `E4_cluster` packaging.

Accordingly, this file tracks the reverse-direction cluster transport package
only:
1. common-BHW/full-Schwartz supplier work,
2. then reverse Section-4.4 transport/density closure,
3. then final packaging into
   `SchwingerOS.lean :: OsterwalderSchraderAxioms.E4_cluster`.

It does **not** assign any `E2_reflection_positive` ownership, and later Lean
work should not cite this note as if it documented a combined late
reverse-direction positivity/cluster package.

## Summary

This document describes the work in the reverse-direction cluster lane:
given Wightman functions satisfying R4 (cluster decomposition), show the
constructed Schwinger functions satisfy `E4_cluster`.

## What was done

### Bug fix

The statement of `bhw_pointwise_cluster_forwardTube` in `SchwingerAxioms.lean`
had `↑(a μ) * Complex.I` (imaginary spatial shift) where `↑(a μ)` (real
spatial shift) was needed.  The imaginary version:
- Breaks PET membership for large |a| (imaginary spatial parts violate the
  forward cone condition η₀ > |η⃗|)
- Doesn't match the downstream consumer `W_analytic_cluster_integral`, which
  translates the test function by a real vector via `g_a(x) = g(x - a)`

### New axiom: `distributional_cluster_lifts_to_tube`

**File:** `SCV/VladimirovTillmann.lean`

A tube-domain SCV axiom stating that distributional cluster on the boundary
lifts to pointwise cluster on the tube interior.

**Hypotheses:**
- C ⊂ ℝᵐ is an open convex salient cone
- F holomorphic on T(C) with distributional BV W (continuous linear functional
  on Schwartz space)
- F₁, F₂ holomorphic on sub-tubes T(C₁), T(C₂) with BVs W₁, W₂
- Distributional cluster (R4 format): for all Schwartz f₁, f₂ and ε > 0,
  ∃ R > 0 such that for |a| > R:
  ‖W(f₁ ⊗ τ_a f₂) - W₁(f₁) · W₂(f₂)‖ < ε

**Conclusion:** For all z₁ ∈ T(C₁), z₂ ∈ T(C₂) with (z₁,z₂) ∈ T(C),
and ε > 0: ∃ R > 0 such that for purely spatial a with |a| > R:
‖F(z₁, z₂ + a) - F₁(z₁) · F₂(z₂)‖ < ε

**Proof sketch (not formalized):** The Poisson integral representation for
tube domains (Vladimirov Thm 25.1) gives F(z) = W(K_z) where K_z is a
Schwartz-class kernel.  For product configurations, K factors as
K_{z₁} ⊗ K_{z₂}, and a real shift translates K_{z₂}.  Applying the
distributional cluster condition to these kernels gives the pointwise result.
The Riemann-Lebesgue lemma (`Mathlib.Analysis.Fourier.RiemannLebesgueLemma`)
provides decay of the connected spectral component under spatial oscillation.

**References:**
- Vladimirov, "Methods of the Theory of Generalized Functions", §25
- Reed-Simon, "Methods of Modern Mathematical Physics" II, Thm IX.16
- Streater-Wightman, "PCT, Spin and Statistics", §2.4 + Thm 3-5

**Vetting:** Reviewed by Gemini Deep Think, which identified and helped fix:
- A soundness bug (vacuous Prop hypothesis)
- Redundant tube membership check in the conclusion (real shifts preserve Im)
- Comment accuracy ("compact subcones" → "compact subsets")
- Elaborator robustness (explicit ℝ→ℂ casts)

### Sorry-free proof of `bhw_pointwise_cluster_forwardTube`

The pointwise cluster theorem is now fully proved (modulo the axiom above).
The proof wires together:

1. **mkCLM:** Packages `Wfn.W n` (function + linearity + continuity) as a
   `ContinuousLinearMap` on Schwartz space, matching the axiom's type.

2. **ForwardTube ↔ TubeDomainSetPi bridge:** Uses `forwardTube_eq_imPreimage`
   to convert between the Wightman-namespace `ForwardTube` and the
   SCV-namespace `TubeDomainSetPi (ForwardConeAbs)`.

3. **BV convergence bridge:** Converts the spectrum condition's `InForwardCone`
   form to the axiom's `ForwardConeAbs` form via `inForwardCone_iff_mem_forwardConeAbs`.

4. **h_bv_cluster from R4:** The axiom's tensor-product cluster hypothesis
   matches `Wfn.cluster` exactly — no tensor-product density argument needed.

5. **Shifted ForwardTube membership:** Real spatial block-shift preserves
   ForwardTube (imaginary parts unchanged), proved via
   `forwardTube_add_real_pointwise`.

6. **BHW = spectrum_condition bridge:** On ForwardTube, `W_analytic_BHW.val`
   equals `spectrum_condition.choose` (BHW property 2).

### New helper lemmas

- `isEuclidean_realSpatialShift` — IsEuclidean preserved under real spatial shift
- `forwardTube_add_real_pointwise` — ForwardTube closed under pointwise real shifts
- `permutedForwardTube_add_real_pointwise` — lifts to PermutedForwardTube
- `append_realSpatialShift_mem_PET_of_permutedForwardTube` — Fin.append block
  shift preserves PET membership (proved via the pointwise result)

## What remains: `W_analytic_cluster_integral` as a supplier, not the final axiom field

The key documentation discipline here is that
`W_analytic_cluster_integral` is **not** the final reverse theorem target.
It is the live full-Schwartz/common-BHW supplier theorem on the honest
Section-4.4 lane. The final target is still the zero-diagonal Euclidean axiom
field
`SchwingerOS.lean :: OsterwalderSchraderAxioms.E4_cluster`.

So the later Lean transcript must stay split as:
1. prove / repair `W_analytic_cluster_integral` on the common-BHW side,
2. use `wickRotatedBoundaryPairing_cluster` as the checked full-`SchwartzNPoint`
   wrapper in `SchwingerAxioms.lean`,
3. build the exact zero-diagonal witnesses demanded by
   `OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean:792-804` in the
   literal local order
   `constructSchwinger_cluster_translate_adapter -> constructSchwinger_cluster_tensor_adapter -> constructSchwinger_cluster`,
4. close by assigning that packaged witness to
   `SchwingerOS.lean :: OsterwalderSchraderAxioms.E4_cluster`.

Equivalently, the consumer ladder is frozen as
`W_analytic_cluster_integral -> wickRotatedBoundaryPairing_cluster -> constructSchwinger_cluster_translate_adapter -> constructSchwinger_cluster_tensor_adapter -> constructSchwinger_cluster -> OsterwalderSchraderAxioms.E4_cluster`.

The file-ownership contract should now be read literally:
- `OSReconstruction/Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean`
  owns both checked-present theorem surfaces on this lane — the live supplier
  `W_analytic_cluster_integral` and the checked wrapper
  `wickRotatedBoundaryPairing_cluster`.
- `OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean` owns only the
  final axiom-field consumer surface
  `OsterwalderSchraderAxioms.E4_cluster`.
- The missing theorem `constructSchwinger_cluster` is therefore not an
  unspecified extra lemma inside `SchwingerAxioms.lean`; it is the explicit
  zero-diagonal packaging seam between the checked wrapper and the final field
  witness.
- More sharply, that seam is not a one-line coercion. The live field surface in
  `SchwingerOS.lean:792-804` quantifies first a translated witness
  `g_a : ZeroDiagonalSchwartz d m` (line 802) and then a product witness
  `fg_a : ZeroDiagonalSchwartz d (n + m)` (line 804), so the docs must reserve
  theorem slots for exactly those two witness-building obligations before the
  final norm-inequality theorem `constructSchwinger_cluster` is allowed to
  fire.

This is exactly the opposite of the reverse positivity situation, where the
currently existing checked theorem surface is a quarantined wrapper rather than
an honest live supplier.

## The open supplier theorem: `W_analytic_cluster_integral`

### The problem

`W_analytic_cluster_integral` says: the Schwinger integral
∫ W_BHW(n+m)(wick(x)) · (f ⊗ g_a)(x) dx clusters as |a| → ∞.

The natural proof uses `bhw_pointwise_cluster_forwardTube` + dominated
convergence.  However, there is a **time-ordering subtlety**:

- `bhw_pointwise_cluster_forwardTube` requires the combined config
  `Fin.append(wick(x_n), wick(x_m))` to be in `ForwardTube d (n+m)`.
- ForwardTube requires the times to be ordered: all n-block times before all
  m-block times.
- The integral runs over ALL x, including configs where m-block times precede
  n-block times (~half the domain).
- The spatial shift a doesn't change times (a₀ = 0), so the time ordering is
  the same for all a.  On the "wrong ordering" sector, the pointwise cluster
  theorem doesn't apply.
- BHW permutation invariance doesn't help directly: it permutes ALL arguments,
  but the cluster factorization depends on WHICH indices are in the n-block vs
  m-block (determining which get shifted by a).

### Why it doesn't block the current production bridge

`W_analytic_cluster_integral` and the later `E4_cluster` packaging are
**late reverse-direction leaf theorems**. The production bridge
`wightman_to_os_full` requires only continuity, linearity, and
`IsWickRotationPair`; it does **not** require `E4_cluster`.

But this should not be misread as “the whole late reverse package is leaf and
uniform.” The doc-level contract is now:
- reverse `E2_reflection_positive` belongs to a separate Section-4.3 transport
  package and currently has only a quarantined checked wrapper,
- reverse `E4_cluster` belongs to the Section-4.4 transport package tracked in
  this file,
- neither late field is part of the current minimal bridge theorem, but they
  must stay separated because one is quarantined-wrapper debt and the other is
  live-supplier-plus-packaging debt.

### Endorsed resolution: sector decomposition (and only sector decomposition)

The implementation route for `W_analytic_cluster_integral` is now fixed:

- **Endorsed route:** finite **time-ordering sector decomposition** of the
  `(n+m)`-point Wick-rotated integral, followed by sectorwise application of
  `bhw_pointwise_cluster_forwardTube` and sectorwise dominated convergence.
- **Blocked-only alternative:** strengthening
  `distributional_cluster_lifts_to_tube` from a single tube to full PET. This
  would change the current SCV theorem surface and is therefore **not** the
  default implementation contract for the reverse cluster lane.
- **Blocked-only alternative:** a brand-new direct distributional proof from
  `Wfn.cluster` to `constructSchwinger_cluster` bypassing the common-BHW
  interior theorem. That would change the route and require new bridge
  infrastructure, so it is also **not** the default contract.

So later Lean work should not reopen the route question here. The proof target
is the existing theorem surface
`SchwingerAxioms.lean :: W_analytic_cluster_integral`, and the endorsed way to
close it is by decomposing the integral into finitely many ordering sectors.

### Exact proof transcript for `W_analytic_cluster_integral`

The theorem statement in the live file already fixes the consumer shape:
- input theorem surface:
  `SchwingerAxioms.lean :: W_analytic_cluster_integral`
- immediate wrapper consumer:
  `SchwingerAxioms.lean :: wickRotatedBoundaryPairing_cluster`
- later zero-diagonal packager:
  `SchwingerOS.lean`-side theorem slot `constructSchwinger_cluster`
- final field consumer:
  `SchwingerOS.lean :: OsterwalderSchraderAxioms.E4_cluster`

For the still-open supplier theorem itself, the implementation transcript is
now fixed more sharply as:

1. **Partition the integration domain by time-ordering sector.**
   Decompose `NPointDomain d (n+m)` into the finitely many sectors determined
   by the relative order of the Wick-rotated time coordinates, modulo the fact
   that the first `n` variables and last `m` variables are still remembered as
   the two cluster blocks. This is a local proof block inside
   `W_analytic_cluster_integral`, not a new public reverse-route theorem.
2. **Identity sector first.**
   On the sector where all first-block times precede all second-block times,
   the configuration already lies in the identity `ForwardTube` chart after
   Wick rotation, so the pointwise cluster input is exactly the checked theorem
   `bhw_pointwise_cluster_forwardTube`.
3. **Permuted sectors next.**
   On every other sector, use BHW permutation invariance to rewrite the
   `(n+m)`-point BHW value into the corresponding order-compatible chart before
   applying `bhw_pointwise_cluster_forwardTube`. The proof obligation here is
   not a new cluster theorem: it is the explicit sectorwise rewrite showing
   that the reordered common-BHW integrand still compares against the same
   `n`-block × `m`-block product limit. Within-block permutation symmetry of
   the factorized limit must be used explicitly; later Lean work should not
   hide this as a vague "by symmetry" step.
4. **Uniform domination on every sector.**
   Use the already-documented shift-independent growth majorant coming from the
   `HasForwardTubeGrowth` package in `SchwingerTemperedness.lean` to dominate
   the sectorwise integrands uniformly in the spatial translation parameter
   `a`. This is the same growth source already cited in the source comment
   above `W_analytic_cluster_integral`; no new PET-strengthened growth theorem
   is part of the endorsed route.
5. **Apply sectorwise dominated convergence.**
   First prove convergence on each sector separately, then sum the finitely many
   sector contributions. The finite-sector sum is part of the proof transcript,
   not an optional optimization.
6. **Only after the sectorwise integral theorem is closed, pass to the checked
   wrapper** `wickRotatedBoundaryPairing_cluster` by unfolding
   `wickRotatedBoundaryPairing` exactly as the current source does.

### Helper-lemma decomposition for the supplier theorem

To make the later Lean implementation mechanical, the open work inside
`W_analytic_cluster_integral` should be decomposed into the following local
proof blocks, in this order:

1. a **sector partition** lemma for the `(n+m)`-point integration domain;
2. an **identity-sector ForwardTube membership** lemma matching the exact input
   shape of `bhw_pointwise_cluster_forwardTube`;
3. a **sectorwise permutation-rewrite** lemma converting a bad time-ordering
   sector to the good chart on the common-BHW side;
4. a **uniform sectorwise majorant** lemma using the existing
   `HasForwardTubeGrowth`-style weighted polynomial bound together with
   Schwartz decay of `f.tensorProduct g_a`;
5. a **sectorwise dominated-convergence** lemma;
6. the final **finite sector sum + block factorization** closure for
   `W_analytic_cluster_integral`.

These are implementation-order obligations for the existing theorem surface,
not permission to invent a different public route.

## Exact ownership boundary versus the reverse positivity lane

To prevent later implementation drift, the reverse late-field ownership split
should be read as:

1. `E2_reflection_positive`
   - transport/density-core owner:
     `OSReconstruction/Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean`
   - final packaging owner:
     `OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean`
   - honest frozen theorem-slot order:
     `wickRotated_positiveTimeCore -> wickRotatedBoundaryPairing_eq_transport_inner_on_core -> wickRotatedBoundaryPairing_nonneg_on_core -> wickRotated_positiveTimeCore_dense -> wickRotatedBoundaryPairing_nonneg_by_density -> constructSchwinger_positive -> OsterwalderSchraderAxioms.E2_reflection_positive`
   - current checked theorem surface:
     `wickRotatedBoundaryPairing_reflection_positive`
   - status: **quarantined**; not trusted infrastructure
   - slot contract:

     | Slot | Owner | Consumes | Exports | Next allowed consumer |
     |---|---|---|---|---|
     | `wickRotated_positiveTimeCore` | `WickRotation/SchwingerAxioms.lean` | forward Section-4.3 transport/Hilbert-side positive-time data | the Wick-rotated positive-time dense core | `wickRotatedBoundaryPairing_eq_transport_inner_on_core` |
     | `wickRotatedBoundaryPairing_eq_transport_inner_on_core` | `WickRotation/SchwingerAxioms.lean` | `wickRotated_positiveTimeCore` plus the forward Section-4.3 transport inner-product identity | reverse Euclidean pairing = forward transport inner product on the core | `wickRotatedBoundaryPairing_nonneg_on_core` |
     | `wickRotatedBoundaryPairing_nonneg_on_core` | `WickRotation/SchwingerAxioms.lean` | the core pairing identity plus forward positivity on the transport side | nonnegativity on the positive-time core | `wickRotated_positiveTimeCore_dense`, `wickRotatedBoundaryPairing_nonneg_by_density` |
     | `wickRotated_positiveTimeCore_dense` | `WickRotation/SchwingerAxioms.lean` | the chosen reverse positive-time core | density of that core in the ambient positive-time Euclidean test-function space | `wickRotatedBoundaryPairing_nonneg_by_density` |
     | `wickRotatedBoundaryPairing_nonneg_by_density` | `WickRotation/SchwingerAxioms.lean` | core nonnegativity + density | ambient positive-time reverse nonnegativity | `constructSchwinger_positive` only |
     | `constructSchwinger_positive` | reverse packaging layer targeting `Reconstruction/SchwingerOS.lean` | the ambient positive-time reverse nonnegativity theorem; no false OS=`Wightman` shortcut | the exact field witness `OsterwalderSchraderAxioms.E2_reflection_positive` | final field packaging only |
2. `E4_cluster`
   - checked supplier/wrapper owner:
     `OSReconstruction/Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean`
   - final field owner:
     `OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean`
   - checked/open supplier surface:
     `W_analytic_cluster_integral`
   - checked intermediate wrapper:
     `wickRotatedBoundaryPairing_cluster`
   - honest frozen packaging order:
     `constructSchwinger_cluster_translate_adapter -> constructSchwinger_cluster_tensor_adapter -> constructSchwinger_cluster`
   - final consumer field:
     `SchwingerOS.lean :: OsterwalderSchraderAxioms.E4_cluster`
   - slot contract:

     | Slot | Owner | Consumes | Exports | Next allowed consumer |
     |---|---|---|---|---|
     | `W_analytic_cluster_integral` | `WickRotation/SchwingerAxioms.lean` | common-BHW/full-`SchwartzNPoint` cluster setup, with the fixed proof transcript sector partition -> identity-sector ForwardTube step -> bad-sector permutation rewrites -> uniform majorant -> sectorwise DCT -> finite sector sum | the reverse Section-4.4 supplier estimate on the common-BHW/full-`SchwartzNPoint` side | `wickRotatedBoundaryPairing_cluster` only |
     | `wickRotatedBoundaryPairing_cluster` | `WickRotation/SchwingerAxioms.lean` | `W_analytic_cluster_integral` only | the checked Wick-rotated full-`SchwartzNPoint` wrapper, still below any zero-diagonal field witness | `constructSchwinger_cluster_translate_adapter`, `constructSchwinger_cluster_tensor_adapter`, `constructSchwinger_cluster` |
     | `constructSchwinger_cluster_translate_adapter` | reverse packaging layer targeting `Reconstruction/SchwingerOS.lean` | `g : ZeroDiagonalSchwartz d m` plus a spatial translation vector `a` | the exact quantified witness `g_a : ZeroDiagonalSchwartz d m` required by `SchwingerOS.lean :: OsterwalderSchraderAxioms.E4_cluster` | `constructSchwinger_cluster_tensor_adapter`, `constructSchwinger_cluster` |
     | `constructSchwinger_cluster_tensor_adapter` | same reverse packaging layer | `f : ZeroDiagonalSchwartz d n` plus the translated witness `g_a` | the exact witness `fg_a : ZeroDiagonalSchwartz d (n + m)` required by `SchwingerOS.lean :: OsterwalderSchraderAxioms.E4_cluster` | `constructSchwinger_cluster` |
     | `constructSchwinger_cluster` | same reverse packaging layer, final target `Reconstruction/SchwingerOS.lean` | `wickRotatedBoundaryPairing_cluster` plus the manufactured witnesses `g_a` and `fg_a`; no black-box tensor-restriction shortcut | the literal norm inequality demanded by `OsterwalderSchraderAxioms.E4_cluster` | final field packaging only |

This note therefore owns only item (2), but it now records item (1) at enough
resolution that later Lean work cannot misread this file as assigning the same
ownership pattern to both late reverse fields.

## File inventory

| File | Changes |
|------|---------|
| `SCV/VladimirovTillmann.lean` | +2 axioms (`vladimirov_tillmann` pre-existing, `distributional_cluster_lifts_to_tube` new) |
| `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean` | Bug fix + 4 new lemmas + sorry-free `bhw_pointwise_cluster_forwardTube` |
| `README.md` | Documentation of fork changes |
