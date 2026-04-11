# Sorry Analysis: OS Reconstruction Bridge Theorems

> Status note (2026-02-27, tightened 2026-04-08): this analysis is stale and
> kept for history only. Its monolithic `WickRotation.lean` decomposition,
> counts, and axiom list do **not** match the current split production tree.
> Canonical current plan and counts live in
> `docs/development_plan_systematic.md`,
> `docs/proof_docs_completion_plan.md`,
> `docs/theorem2_locality_blueprint.md`,
> `docs/theorem3_os_route_blueprint.md`,
> `docs/theorem4_cluster_blueprint.md`, and
> `OSReconstruction/Wightman/TODO.md`.

*Updated 2026-02-20. Covers WickRotation.lean (18 sorrys), Reconstruction.lean (4 sorrys), and axioms.*

## Current Status

### Fully proved (sorry-free)
- `SCV/Analyticity.lean` — multi-variable power series from Cauchy integrals
- `SCV/TubeDomainExtension.lean` — edge-of-the-wedge theorem
- `SCV/MoebiusMap.lean` — Möbius maps
- `SCV/EOWMultiDim.lean` — multi-dim EOW helpers
- `SCV/IteratedCauchyIntegral.lean` — Cauchy integral on polydiscs
- `SCV/IdentityTheorem.lean` — identity theorem for SCV (proved via `differentiableOn_analyticAt`)
- `Reconstruction/AnalyticContinuation.lean` — BHW bridge, Euclidean invariance proofs
- `Reconstruction/Helpers/SeparatelyAnalytic.lean` — Osgood lemma chain
- `Reconstruction/Helpers/EdgeOfWedge.lean` — 1D edge-of-the-wedge

### Axioms (taken on faith)

#### In AnalyticContinuation.lean
| Axiom | Line | Notes |
|-------|------|-------|
| `bargmann_hall_wightman` | ~788 | Requires connectedness of SO⁺(1,d;ℂ) and identity theorem on complex manifolds |
| ~~`edge_of_the_wedge`~~ | ~730 | **NOW PROVED**: replaced axiom with theorem using `edge_of_the_wedge_theorem` from SCV/TubeDomainExtension.lean |

#### In SCV/TubeDistributions.lean (NEW)
| Axiom | Notes |
|-------|-------|
| `continuous_boundary_tube` | Vladimirov §26.2: holomorphic on tube domain with distributional BVs → continuous at real boundary |
| `distributional_uniqueness_tube` | Vladimirov §26.3: same distributional BVs → equal on tube |
| `polynomial_growth_tube` | S-W Thm 2-6: tempered distributional BVs → polynomial growth |

#### In WickRotation.lean (NEW — forward-tube specializations)
| Axiom | Notes |
|-------|-------|
| `continuous_boundary_forwardTube` | Specialization of `continuous_boundary_tube` to `ForwardTube d n` |
| `distributional_uniqueness_forwardTube` | Specialization of `distributional_uniqueness_tube` to `ForwardTube d n` |

### Recently closed sorrys
- `IdentityTheorem.lean`: `analyticOnNhd_of_finiteDimensional` — proved using `SCV.differentiableOn_analyticAt`
- `WickRotation.lean`: `W_analytic_continuous_boundary` — proved using `continuous_boundary_forwardTube` axiom

---

## R→E Direction (Wightman → Schwinger): historical monolith view only

This section is retained only as a historical decomposition of the old
`WickRotation.lean` monolith. It is **not** the live implementation ledger.
In the current split tree, later Lean work must read reverse ownership from
`Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean` together with
`docs/r_to_e_blueprint.md`, `README.md`, and
`OSReconstruction/Wightman/TODO.md`.

For the late reverse fields, the implementation contract is now explicitly
split:
- `E2_reflection_positive` does **not** currently have an honest supplier
  theorem. The checked wrapper
  `SchwingerAxioms.lean :: wickRotatedBoundaryPairing_reflection_positive`
  stays quarantined because it still depends on the false OS=`Wightman` chain.
- `E4_cluster` already has a live supplier theorem
  `SchwingerAxioms.lean :: W_analytic_cluster_integral`, but that theorem is
  only the first supplier in the frozen consumer ladder
  `W_analytic_cluster_integral -> wickRotatedBoundaryPairing_cluster -> constructSchwinger_cluster_translate_adapter -> constructSchwinger_cluster_tensor_adapter -> constructSchwinger_cluster -> OsterwalderSchraderAxioms.E4_cluster`.
  The final packaging step is now frozen at the exact field shape from
  `SchwingerOS.lean:792`: later Lean work must not stop at a vague
  `constructSchwinger_cluster` slogan, but must pass through the literal
  zero-diagonal adapter order
  `constructSchwinger_cluster_translate_adapter ->`
  `constructSchwinger_cluster_tensor_adapter ->`
  `constructSchwinger_cluster`, where the first adapter manufactures the
  quantified witness `g_a : ZeroDiagonalSchwartz d m` and the second
  manufactures `fg_a : ZeroDiagonalSchwartz d (n + m)` before the final norm
  inequality theorem is even well-typed.

The forward theorem-4 lane now also needs an explicit anti-drift note here,
even though this file is historical: later Lean work must not read the old
`WickRotation.lean` story as permission to re-collapse theorem 4 into one vague
cluster theorem. Against the live repo tree, the owner split is:
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean`
  owns the positivity/extraction package ending at
  `cluster_left_factor_transport -> cluster_right_factor_transport`;
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean`
  owns only the repaired base bridge
  `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison -> bvt_cluster_positiveTime_singleSplit_core`;
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`
  owns the public canonical-shell adapter queue
  `canonical_cluster_integrand_eq_singleSplit_integrand -> canonical_translate_factor_eq_singleSplit_translate_factor -> singleSplit_core_rewrites_to_canonical_shell -> canonical_shell_limit_of_rewrite -> bvt_cluster_canonical_from_positiveTime_core`,
  and the checked private frontier remains
  `OSToWightmanBoundaryValues.lean:398 :: bvt_F_clusterCanonicalEventually_translate`.

The critical theorem-surface contract on that forward theorem-4 lane is now:
1. `cluster_right_factor_transport` is not a slogan-level symmetric analogue of
   the left-factor row. It must reuse the same normalization package only via
   the definitional alias `normalizedZeroDegreeLeftVector d :=
   normalizedZeroDegreeRightVector d`; then consume the corresponding
   right-single Wightman/OS extraction rewrites together with
   `zero_degree_component_comparison_for_normalized_right_vector`; then move the
   unique nontrivial shell to the second input; and then close without
   introducing a second normalization witness package, a second degree-`0`
   comparison theorem, or any new right-single algebra.
2. `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`
   is a pure base-file repair slot in
   `OSToWightmanBoundaryValuesBase.lean`, source-anchored only to
   `:2214 :: ...singleSplitLargeSpatial`,
   `:2352 :: ...singleSplitSchwingerLargeSpatial`, and
   `:2514 :: ...singleSplitFactorComparison`. Its internal Lean-order
   transcript is frozen: instantiate the legacy single-split factor-comparison
   shell unchanged; replace only the two false same-shell hypotheses by
   `cluster_left_factor_transport` and `cluster_right_factor_transport`; close
   the repaired theorem under the new name; then package it exactly once into
   `bvt_cluster_positiveTime_singleSplit_core`. No canonical-direction rewrite,
   translated-factor rewrite, or `BoundaryValueLimits.lean` import is allowed
   in this file.
3. `singleSplit_core_rewrites_to_canonical_shell` is a pure shell-rewrite slot
   in
   `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`.
   Its source-checked downstream target is the literal frontier shell at
   `:398 :: private theorem bvt_F_clusterCanonicalEventually_translate`, and
   its Lean-order transcript must therefore be read against that exact shell:
   first freeze the full quantifier block `(n, m, f, g, ε, a, t)` from the
   `:398` statement; second rewrite only the analytic kernel
   `bvt_F OS lgc (n + m) (fun k μ => ↑(x k μ) + t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I)`
   by a local theorem slot
   `canonical_cluster_integrand_eq_singleSplit_integrand`; third rewrite only
   the translated Schwartz factor
   `((f.tensorProduct (translateSchwartzNPoint (d := d) a g)) x)` by the
   sibling slot `canonical_translate_factor_eq_singleSplit_translate_factor`;
   fourth verify that the eventual / ordered-positive-time quantifier shell is
   otherwise unchanged; and only fifth apply
   `bvt_cluster_positiveTime_singleSplit_core`. This historical note should no
   longer be readable as permission to mix shell rewrites with limit transport
   or to jump directly from the base wrapper into the frontier theorem.
4. `canonical_shell_limit_of_rewrite` is a pure limit-transport slot in that
   same wrapper file. Its imports are now source-checked against
   `OSToWightmanBoundaryValueLimits.lean:260, :273, :290, :314, :350, :446,
   :494, :536`, and its internal proof transcript is frozen more tightly than
   before: (i) start from the already-exported canonical shell statement coming
   from `singleSplit_core_rewrites_to_canonical_shell`; (ii) instantiate the
   scalar holomorphic object
   `bvt_singleSplit_xiShiftHolomorphicValue` (`:260`) for that fixed shell;
   (iii) identify the real-axis shell only through
   `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq` (`:290`); (iv) if a
   right-half-plane uniqueness step is needed, use only
   `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue` (`:273`) together
   with `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq` (`:536`),
   whose proof itself sits over `eqOn_rightHalfPlane_of_ofReal_eq` (`:494`);
   and (v) perform the final Wightman-target `t -> 0+` transport only through
   `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`
   (`:446`). The Schwinger-target theorems
   `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift`
   (`:314`) and
   `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger`
   (`:350`) are lower supplier legs only, and the deprecated bridge at `:388`
   remains forbidden on the theorem-4 lane.
5. `bvt_cluster_canonical_from_positiveTime_core` is only the one-line public
   restatement of the result from `canonical_shell_limit_of_rewrite` in
   `OSToWightmanBoundaryValues.lean`: state exactly the eventual canonical-shell
   theorem consumed by `:398 :: private theorem
   bvt_F_clusterCanonicalEventually_translate`, apply
   `canonical_shell_limit_of_rewrite`, and close. It may not reopen kernel
   rewrites, translated-factor rewrites, uniqueness, or limit transport, and it
   may not import any `BoundaryValueLimits.lean` theorem directly.

So later docs and later Lean work must not collapse either the late reverse
backlog or the forward theorem-4 adapter lane into a generic
`constructedSchwinger_*` / `bvt_cluster_*` bucket.

### Group A: BHW Hypotheses (2 sorrys remaining, 1 closed)

#### A1. `W_analytic_lorentz_on_tube` (line ~152) — SORRY

**Goal**: `W_analytic(Λz) = W_analytic(z)` for connected Lorentz `Λ` on the public Wightman-side covariance surface and `z ∈ ForwardTube`.

**Proof sketch**: Both `z ↦ W_analytic(z)` and `z ↦ W_analytic(Λz)` are holomorphic on ForwardTube with the same distributional boundary values (by `Wfn.lorentz_covariant`). Apply `distributional_uniqueness_forwardTube`.

**Remaining work**: Need to show (1) `z → W_analytic(Λz)` is holomorphic on ForwardTube (the connected proper-orthochronous Lorentz action preserves ForwardTube on the checked public route `Wightman/Groups/Lorentz.lean -> Bridge/AxiomBridge.lean ->` Wick-rotation consumers), and (2) distributional BVs agree (from `Wfn.lorentz_covariant` + change of variables). The internal `ComplexLieGroups/LorentzLieGroup.lean :: RestrictedLorentzGroup` alias is support infrastructure only, not a second public covariance contract.

#### A2. `W_analytic_continuous_boundary` — PROVED ✓

Proved using `continuous_boundary_forwardTube` axiom with `Wfn.W n` as the boundary distribution.

#### A3. `W_analytic_local_commutativity` (line ~183) — SORRY

**Goal**: At real spacelike-separated points, swapping consecutive arguments doesn't change W_analytic.

**Proof sketch**: By A2, W_analytic extends continuously to boundary. The boundary value agrees with W_n (from `spectrum_condition`). By `Wfn.locally_commutative`, W_n(swap) = W_n at spacelike points. Hence W_analytic(swap(x)) = W_analytic(x).

**Remaining work**: Connecting distributional BVs to pointwise continuous extension values. Needs ~20 lines.

### Group B: F_ext Pointwise Invariance (3 sorrys)

#### B1. `F_ext_translation_invariant` (line ~273)
#### B2. `F_ext_rotation_invariant` (line ~315)
#### B3. `F_ext_permutation_invariant` (line ~423)

All three follow the same pattern: use proved results from AnalyticContinuation.lean (`schwinger_euclidean_invariant`, `schwinger_permutation_symmetric`) at distinct-positive-time Euclidean points, extend to all points by density + analyticity.

**Blocker**: A density/full-measure lemma showing distinct-time configurations are generic in NPointDomain.

### Group C: OS Axiom Verification (4 sorrys)

#### C1. `constructedSchwinger_tempered` — E0 (line ~253)
Needs polynomial growth bounds. Enabler: `polynomial_growth_tube` / `polynomial_growth_forwardTube`.

#### C2. reverse `E2_reflection_positive` transport package (historical monolith label)
Current sharpened status: the checked theorem surface
`wickRotatedBoundaryPairing_reflection_positive` exists, but it is only a
**quarantined wrapper** because it still closes through the false
OS=`Wightman` chain. So the real missing work is not to finish a theorem named
`constructedSchwinger_reflection_positive`; it is to build an honest reverse
Section-4.3 transport/density package that lands directly in
`SchwingerOS.lean :: OsterwalderSchraderAxioms.E2_reflection_positive`.

The file-ownership split is now explicit even in this historical note:
- `OSReconstruction/Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean`
  owns the honest transport/density core slots
  `wickRotated_positiveTimeCore -> wickRotatedBoundaryPairing_eq_transport_inner_on_core -> wickRotatedBoundaryPairing_nonneg_on_core -> wickRotated_positiveTimeCore_dense -> wickRotatedBoundaryPairing_nonneg_by_density`.
- `OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean` owns the final
  packaging theorem `constructSchwinger_positive` adjacent to the target field
  `OsterwalderSchraderAxioms.E2_reflection_positive` at `SchwingerOS.lean:774`.
  Repo-tree check: there is currently no separate reverse-packaging support
  file between `SchwingerAxioms.lean` and `SchwingerOS.lean` for this last E2
  slot.

The local execution transcript for that final packaging slot is now fixed too:
1. instantiate the literal `SchwingerOS.lean:774` field goal on the given
   `F : BorchersSequence d` with ordered positive-time support;
2. rewrite the field-side quantity `(OSInnerProduct d S F F).re` to the ambient
   reverse positivity theorem supplied by
   `wickRotatedBoundaryPairing_nonneg_by_density`;
3. discharge nonnegativity there exactly with
   `wickRotatedBoundaryPairing_nonneg_by_density`;
4. close the field witness by definitional rewriting only.

Anti-drift rule for this historical note: `constructSchwinger_positive` is a
pure last-step packager. It may not reopen the positive-time core definition,
reprove density, or sneak back through the quarantined false
OS=`Wightman` comparison chain.

#### C3. `W_analytic_cluster_integral` — reverse `E4_cluster` supplier, not final field witness
Current sharpened status: `W_analytic_cluster_integral` is a real live theorem
on the common-BHW / full-`SchwartzNPoint` side, but it is **not** itself the
final reverse cluster theorem. The frozen implementation order is
`W_analytic_cluster_integral -> wickRotatedBoundaryPairing_cluster -> constructSchwinger_cluster_translate_adapter -> constructSchwinger_cluster_tensor_adapter -> constructSchwinger_cluster -> OsterwalderSchraderAxioms.E4_cluster`,
so the still-missing theorem slots above the checked wrapper are the two
explicit witness-building adapters plus the final norm-inequality packager,
not a vague monolithic `constructedSchwinger_*` closure.

The ownership split is likewise literal:
- `OSReconstruction/Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean`
  owns the checked supplier `W_analytic_cluster_integral` and the checked
  wrapper `wickRotatedBoundaryPairing_cluster`.
- `OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean` owns only the
  final field consumer `OsterwalderSchraderAxioms.E4_cluster`.
- The still-missing theorem seam on the `SchwingerOS.lean` side must therefore
  be split into three explicit slots, not one slogan: the translated witness
  adapter at `SchwingerOS.lean:802-804`, the tensor witness adapter at
  `SchwingerOS.lean:804-807`, and only then the final theorem
  `constructSchwinger_cluster` packaging the field at `SchwingerOS.lean:792`.

The packaging seam is now frozen more tightly against the actual field
statement in `SchwingerOS.lean:792-807`. The route above the checked wrapper
must run in the local order
`constructSchwinger_cluster_translate_adapter ->`
`constructSchwinger_cluster_tensor_adapter -> constructSchwinger_cluster`,
and the first two slots are adapter-only manufacture theorems:
- `constructSchwinger_cluster_translate_adapter` consumes only
  `g : ZeroDiagonalSchwartz d m` plus the spatial translation vector `a`; it
  does **not** consume `wickRotatedBoundaryPairing_cluster`.
- `constructSchwinger_cluster_tensor_adapter` consumes only
  `f : ZeroDiagonalSchwartz d n` plus the translated witness `g_a`; it still
  does **not** consume `wickRotatedBoundaryPairing_cluster`.
- `constructSchwinger_cluster` is the first and only theorem in this local lane
  allowed to consume `wickRotatedBoundaryPairing_cluster`.

The local execution transcript is now fixed as:
1. define `g_a` and prove the exact translate equation
   `g_a.1 x = g.1 (fun i => x i - a)`;
2. define `fg_a` and prove the exact tensor shell
   `fg_a.1 x = f.1 (splitFirst n m x) * g_a.1 (splitLast n m x)`;
3. instantiate the literal `SchwingerOS.lean:792-807` field goal with those two
   witness slots already present;
4. only then rewrite that quantified field goal to the checked
   full-`SchwartzNPoint` estimate exported by `wickRotatedBoundaryPairing_cluster`;
5. substitute the witness equations for `g_a` and `fg_a` in that order;
6. discharge the final norm inequality.

Anti-drift rule for this historical note: later Lean work may not hide steps
(1)-(5) inside a black-box tensor-restriction wrapper, and neither adapter slot
is allowed to touch the checked wrapper before the final packaging theorem.

#### C4. Boundary values in `wightman_to_os_full` (line ~755)
Sign convention issue. See `docs/sign_convention_analysis.md`.

---

## E→R Direction (Schwinger → Wightman): 9 sorrys

### Group D: Inductive Analytic Continuation (3 sorrys)
- D1. `inductive_analytic_continuation` (line ~601) — OS II Theorem 4.1
- D2. `full_analytic_continuation` (line ~611) — d+1 steps of D1
- D3. `boundary_values_tempered` (line ~664) — growth estimates from E0'

### Group E: Wightman Axiom Verification (6 sorrys)
| Field | Proof from | Difficulty |
|-------|-----------|------------|
| `normalized` | S_0 = 1 → W_0 = evaluation | Easy (once D2 done) |
| `translation_invariant` | E1 restricted to translations | Medium |
| `lorentz_covariant` | E1 via BHW | Hard |
| `locally_commutative` | E3 + edge-of-the-wedge | Hard |
| `positive_definite` | E2 (reflection positivity) | Hard |
| `hermitian` | Reality of Schwinger functions | Medium |
| `os_to_wightman_full` | Wire everything | Depends on D+E |

---

## Dependency Graph

```
continuous_boundary_forwardTube (axiom)
    │
    ├── A2 (continuous boundary) ← PROVED ✓
    ├── A3 (local commutativity) ← via A2 + locally_commutative (~20 LOC)
    └── A1 (Lorentz on tube) ← via distributional_uniqueness_forwardTube (~60 LOC)

distributional_uniqueness_forwardTube (axiom)
    │
    └── A1 (Lorentz on tube) ← + holomorphy of W_analytic ∘ Λ + BV agreement

polynomial_growth_tube (axiom)
    │
    └── C1 (E0 temperedness) ← growth bounds + Schwartz decay

Sign fix (x - iεη → x + iεη)
    │
    └── C4 (boundary values in wightman_to_os_full)

Still blocked (deeper arguments needed):
    B1-B3 (F_ext invariance) ← density/full-measure lemma
    C2 (E2 reflection positivity) ← reverse Section-4.3 transport/density package on the Wick-rotated positive-time core; do not use the false OS=`Wightman` pairing chain
    C3 (E4 cluster) ← reverse Section-4.4 transport/density package in the frozen order `W_analytic_cluster_integral -> wickRotatedBoundaryPairing_cluster -> constructSchwinger_cluster_translate_adapter -> constructSchwinger_cluster_tensor_adapter -> constructSchwinger_cluster -> OsterwalderSchraderAxioms.E4_cluster`
    D1-D3 (E→R inductive continuation) ← OS II Laplace transform theory
    E1-E6 (Wightman axiom verification) ← depends on D1-D3
```

## Summary

| Category | Total Sorrys | Closed | Remaining |
|----------|-------------|--------|-----------|
| BHW hypotheses (A1-A3) | 3 | 1 (A2) | 2 |
| F_ext invariance (B1-B3) | 3 | 0 | 3 |
| OS axiom verification (C1-C4) | 4 | 0 | 4 |
| E→R continuation (D1-D3) | 3 | 0 | 3 |
| Wightman axioms (E1-E6) | 6 | 0 | 6 |
| `os_to_wightman_full` | 1 | 0 | 1 |
| **Total WickRotation** | **20** | **2** | **18** |
| **Reconstruction.lean** | **4** | **0** | **4** |

With the 5 new axioms (3 general tube domain + 2 forward tube) and continuous boundary proved, the path forward is:
- A1, A3: ~80 lines of proof connecting axioms to Wightman axiom hypotheses
- B1-B3: need density/full-measure lemma (~50 lines)
- C1: need polynomial growth bounds wired through (~30 lines)
- C4: sign convention fix (~5 line change, but affects all downstream)
- late reverse fields: keep the split explicit — `E2_reflection_positive`
  still needs the honest reverse Section-4.3 transcript
  `wickRotated_positiveTimeCore -> wickRotatedBoundaryPairing_eq_transport_inner_on_core -> wickRotatedBoundaryPairing_nonneg_on_core -> wickRotated_positiveTimeCore_dense -> wickRotatedBoundaryPairing_nonneg_by_density -> constructSchwinger_positive -> OsterwalderSchraderAxioms.E2_reflection_positive`,
  while `E4_cluster` already has the live supplier
  `W_analytic_cluster_integral` but still needs the full wrapper/package ladder
  `W_analytic_cluster_integral -> wickRotatedBoundaryPairing_cluster -> constructSchwinger_cluster_translate_adapter -> constructSchwinger_cluster_tensor_adapter -> constructSchwinger_cluster -> OsterwalderSchraderAxioms.E4_cluster`,
  with the exact `g_a` / `fg_a` witness obligations coming from the field
  statement in `SchwingerOS.lean`
- D1-D3, E1-E6: deeper mathematical arguments needed
