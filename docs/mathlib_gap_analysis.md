# Mathlib Gap Analysis For OS Reconstruction

Purpose: this note records the external infrastructure gaps that still matter
for `OSReconstruction`, and separates them from gaps that should simply be
proved locally in this repo.

This note should be read together with:
- `docs/general_k_continuation_blueprint.md`
- `docs/scv_infrastructure_blueprint.md`
- `docs/nuclear_spaces_blueprint.md`
- `docs/gns_pipeline_blueprint.md`
- `docs/unbounded_spectral_project.md`
- `docs/mathlib_issue_draft.md`

It is not a summary of all Mathlib limitations. It is a route-facing guide to
the exact missing infrastructure that still matters for later Lean work here.

## 1. Decision rule

For every missing ingredient, the docs should now decide one of:

1. **prove locally now**: the theorem is specialized to the repo and should not
   wait on upstream,
2. **prove locally but keep upstream-compatible shape**: theorem is general but
   current progress benefits from a local proof first,
3. **prepare an upstream issue / import route**: the best long-term home is
   Mathlib or another Lean library, but work here can still proceed in a local
   staging file,
4. **do not block on upstream**: the user-facing route should continue without
   waiting for ecosystem work.

The default for the OS-route frontiers should be (1) or (2), not (3).

## 2. Confirmed current Mathlib regression

The only concrete current upstream issue already isolated in local docs is the
instance-synthesis regression recorded in:

- `docs/mathlib_issue_draft.md`

The exact issue is:

1. `NormSMulClass ℝ ℂ` does not synthesize automatically in Mathlib `v4.29.0`
   in some downstream contexts,
2. this breaks `fun_prop` chains involving `Continuous.smul`,
3. the local workaround is to install the explicit instances:
   `NormedSpace.toNormSMulClass` and `NormSMulClass.toIsBoundedSMul`.

This is a genuine upstream regression report candidate. It is not a reason to
delay proof work in this repo.

## 3. Functional-analysis gaps

### 3.1. Separate continuity on Frechet/Schwartz products

Current repo surface:

1. `exists_continuousMultilinear_ofSeparatelyContinuous`
   is still an axiom in `Wightman/WightmanAxioms.lean`.

Current local documentation:

1. `docs/nuclear_spaces_blueprint.md`
2. `docs/gns_pipeline_blueprint.md`

Mathlib status:

1. multilinear continuity in Banach settings is well supported,
2. the exact Frechet/Schwartz separate-to-joint theorem is not packaged in the
   form needed here.

Decision:

1. prove locally but keep the theorem statement generic,
2. do not wait for Mathlib,
3. later upstreaming is plausible once the proof is isolated from QFT.

Exact implementation consequence:

1. **Primary route**: import/wrap the theorem from the local
   `gaussian-field` dependency if the exact statement matches;
2. **Fallback route**: prove the Frechet-space Banach-Steinhaus package locally
   under the theorem slots listed in
   `docs/nuclear_spaces_blueprint.md`;
3. do not block GNS/kernel-theorem work on opening a Mathlib issue first.

### 3.2. Schwartz nuclear / kernel theorem

Current repo surface:

1. `schwartz_nuclear_extension`
   is still an axiom in `Wightman/WightmanAxioms.lean`.

Mathlib status:

1. no turnkey Schwartz kernel theorem in core Mathlib,
2. local docs note relevant infrastructure in the `gaussian-field` library.

Decision:

1. prove locally with import-compatible interfaces if possible,
2. treat `gaussian-field` as the first place to look for reusable lemmas,
3. do not make GNS cyclicity depend on waiting for a future upstream package.

Exact implementation consequence:

1. **Primary route**: import the local `gaussian-field` nuclear/Schwartz facts
   and derive the repo-facing theorem
   `schwartz_nuclear_extension`;
2. **Fallback route**: prove the tensor-extension package locally via the
   intermediate theorem slots listed in
   `docs/nuclear_spaces_blueprint.md`;
3. the consumer-facing GNS/Wightman files should only see the repo theorem
   surface, never the import-path details.

### 3.3. Bochner-Minlos

Current repo surface:

1. the current checked tree **does** contain
   `OSReconstruction/Wightman/NuclearSpaces/BochnerMinlos.lean`; it belongs to
   the checked local NuclearSpaces support lane rather than to the theorem-2/3/4
   critical-path ledger.
2. doc readers should therefore distinguish three separate things explicitly:
   the checked local support file itself, any remaining bridge/import work above
   that support lane, and the downstream exported consumer surfaces in
   `Wightman/WightmanAxioms.lean`.

Mathlib status:

1. finite-dimensional measure theory is strong,
2. projective/tightness/Minlos packaging is not available as a ready-made
   theorem family.

Decision:

1. prove locally in repo-specific files,
2. keep statements generic enough for later extraction,
3. do not confuse this with the critical theorem-2/3/4 route.

## 4. Several-complex-variables gaps

### 4.1. Tube boundary values from polynomial growth

Current repo surface:

1. `tube_boundaryValueData_of_polyGrowth` is still axiomatic in
   `SCV/TubeBoundaryValues.lean`.

Mathlib status:

1. SCV holomorphy, connectedness, and identity theorems exist locally here,
2. the exact Vladimirov/Streater-Wightman tube-boundary theorem is not in
   Mathlib.

Decision:

1. prove locally in `OSReconstruction/SCV`,
2. keep it QFT-free,
3. do not wait for upstream.

### 4.2. Malgrange-Zerner gluing

Current repo surface:

1. needed by `docs/general_k_continuation_blueprint.md`,
2. not implemented in current repo or Mathlib.

Mathlib status:

1. the ingredients around open/connected sets and holomorphy exist,
2. the exact MZ theorem is not present.

Decision:

1. implement locally in a dedicated SCV file,
2. document every domain/gluing theorem slot first,
3. consider upstreaming only after the local proof stabilizes.

### 4.3. Envelope-of-holomorphy continuation on the mixed OS II domains

Current repo surface:

1. needed for `(P_N) -> (A_{N+1})` in the general-`k` blueprint,
2. not implemented anywhere current.

Mathlib status:

1. no general envelope-of-holomorphy package.

Decision:

1. treat this as local SCV infrastructure,
2. keep the theorem split into generating-union and envelope-identification
   theorems,
3. do not let later docs write "by envelope" without exact theorem names.

### 4.4. Bochner tube theorem

Current repo surface:

1. `bochner_local_extension`
2. `bochner_tube_extension`

Mathlib status:

1. no ready-made Bochner tube theorem.

Decision:

1. prove locally in `SCV/BochnerTubeTheorem.lean`,
2. do not block theorem-2/3/4 work on it unless a later route truly consumes
   it directly.

## 5. Forward-tube / boundary-value constructor gaps

The theorem-2 blueprint now depends on one important missing constructor:

```lean
flatRegular_of_boundary_distribution_and_polyGrowth
```

This is **not** a Mathlib gap. It is a missing local theorem package in the
repo’s own flattened forward-tube language.

Decision:

1. prove locally in the SCV/forward-tube files,
2. document it as a repo theorem, not as a missing upstream theorem,
3. do not open a Mathlib issue for this until the local formulation has
   stabilized.

Exact implementation consequence:

1. theorem 2 and the GNS matrix-coefficient bridge should both consume the same
   one-point package documented in
   `docs/scv_infrastructure_blueprint.md`,
2. the constructor
   `flatRegular_of_boundary_distribution_and_polyGrowth`
   should be treated as a repo-local flattening/adapter theorem above that
   one-point SCV package,
3. neither theorem 2 nor GNS should invent its own custom boundary-value
   constructor route.

## 5b. Theorem-3 raw `BorchersSequence` surface is a repo representation gap, not a Mathlib gap

Current repo surface:

1. `Wightman/Reconstruction/Core.lean :: BorchersSequence`
   is a bounded-record encoding of finitely supported Borchers data;
2. the file provides raw pointwise operations (`Zero`, `Add`, `Neg`, `SMul`, `Sub`);
3. it does **not** currently provide the full `AddCommMonoid` / `Module ℂ` /
   topological structure that a literal
   `Submodule ℂ (BorchersSequence d)` implementation would need.

This is not a missing theorem from Mathlib. It is a local representation issue
in how the repo currently packages Borchers data.

Decision:

1. treat this as a theorem-3 implementation/documentation issue inside the repo,
2. do not open an upstream Mathlib issue for it,
3. prefer the Section 4.3 transport-map / norm-square implementation route
   recorded in
   `docs/theorem3_os_route_blueprint.md`
   before attempting to force a raw `Submodule` / topology layer onto
   `BorchersSequence d`.
4. if a local continuity helper is wanted for legacy consumer theorems, keep it
   explicitly subordinate to those fixed-bound finite-sum consumers, not as a
   new global topological structure on raw `BorchersSequence d`.

Important current-status clarification:

1. the old Package-C / `hschw` route is quarantined rather than active;
2. the active theorem-3 blocker is now the corrected Package-I Section 4.3
   transport package, and its real missing seams are more specific than the
   old slogan “codomain + dense range”: the contract-level blockers are the
   branch-`3b` one-variable / degreewise transport surfaces
   `os1TransportOneVar`, `os1TransportOneVar_eq_zero_iff`,
   `os1TransportComponent`, `os1TransportComponent_eq_zero_iff`,
   `BvtTransportImageSequence`,
   `bvt_transport_to_osHilbert_onImage_wellDefined`,
   `bvt_transport_to_osHilbert_onImage`,
   `lemma42_matrix_element_time_interchange`, and
   `bvt_wightmanInner_eq_transport_norm_sq_onImage`;
3. the main missing content there is the OS I Section 4.3 one-variable
   Fourier-Laplace / Paley-Wiener / extension proof above the already checked
   local suppliers `partialFourierSpatial_fun`,
   `partialFourierSpatial_timeSliceSchwartz`,
   `partialFourierSpatial_timeSlice_hasPaleyWienerExtension`, and
   `partialFourierSpatial_timeSliceCanonicalExtension`, not a new topology on
   raw `BorchersSequence d`;
4. the old public density layer F/G/H is now withdrawn rather than repaired,
   because ordered-positive-time support is not dense in the full Schwartz
   space;
5. the final public closure route is Package I in its corrected Section 4.3
   form, in exact implementation order:
   transformed positive-time Euclidean data
   -> transformed-image core in the Section-4.3 half-space Schwartz codomain
   -> preimage-independence theorem
      `bvt_transport_to_osHilbert_onImage_wellDefined`
   -> on-image transport `bvt_transport_to_osHilbert_onImage`
   -> Lemma-4.2 adapter `lemma42_matrix_element_time_interchange`
   -> quadratic identity
      `bvt_wightmanInner_eq_transport_norm_sq_onImage`
   -> Hilbert-space density / bounded finite-support continuity closure
      `bvt_W_positive_of_transportImage_density`
   -> only then the exported frontier wrapper
      `OSToWightmanBoundaryValues.lean :: bvt_W_positive`;
6. so theorem-3 work should not drift back to either a raw density theorem, a
   vague “prove dense range first” slogan, or “add a `Submodule`/topology layer
   first” as if any of those were the main obstruction.

Implementation-facing theorem-3 slot ledger for this gap note:

| Slot | Owned by | Consumes | Exports | Next consumer |
| --- | --- | --- | --- | --- |
| `os1TransportOneVar` | `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean` | checked branch-`3b` suppliers in `OSReconstruction/SCV/PartialFourierSpatial.lean` (`partialFourierSpatial_fun`, `partialFourierSpatial_timeSliceSchwartz`, `partialFourierSpatial_timeSlice_hasPaleyWienerExtension`, `partialFourierSpatial_timeSliceCanonicalExtension`) plus the theorem-3 `singleSplit_xiShift` support route; source-checked scalar entry seam `identity_theorem_right_halfplane` (`OSToWightmanPositivity.lean:48`) -> `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single` (`:110`) | the one-variable Section-4.3 transport map on the corrected half-space codomain | `os1TransportOneVar_eq_zero_iff`, `os1TransportComponent` |
| `os1TransportOneVar_eq_zero_iff` | same file | `os1TransportOneVar` together with the positive-half-line boundary-value uniqueness input; first-consumer restriction: the checked `:48` / `:110` scalar suppliers are consumed here and in `os1TransportOneVar` before any later transport-image closure slot | the one-variable kernel-zero theorem | `os1TransportComponent`, `bvt_transport_to_osHilbert_onImage_wellDefined` |
| `os1TransportComponent` | same file | `os1TransportOneVar`, `os1TransportOneVar_eq_zero_iff`, and the degreewise assembly above the checked branch-`3b` supplier chain | the degreewise transformed-image transport map | `os1TransportComponent_eq_zero_iff`, `BvtTransportImageSequence` |
| `os1TransportComponent_eq_zero_iff` | same file | `os1TransportComponent` | the degreewise kernel-zero theorem | `BvtTransportImageSequence`, `bvt_transport_to_osHilbert_onImage_wellDefined` |
| `BvtTransportImageSequence` | same file | `os1TransportComponent` | the transformed-image core object on which the quadratic identity is proved | `bvt_transport_to_osHilbert_onImage_wellDefined` only; the transformed-image core may re-enter only downstream of the transport map and the separate Lemma-4.2 seam |
| `bvt_transport_to_osHilbert_onImage_wellDefined` | same file | `BvtTransportImageSequence`, degreewise representative choice, difference of two preimage families, then kernel-zero consumption in the strict order `os1TransportOneVar_eq_zero_iff` -> `os1TransportComponent_eq_zero_iff` | proof that the OS-Hilbert transport value is independent of the chosen transformed-image preimage | `bvt_transport_to_osHilbert_onImage` |
| `bvt_transport_to_osHilbert_onImage` | same file | `BvtTransportImageSequence`, `bvt_transport_to_osHilbert_onImage_wellDefined`, and the checked general Hilbert embedding surface `positiveTimeBorchersVector`; the first checked equalities available on this lane are `positiveTimeBorchersVector_inner_eq` / `positiveTimeBorchersVector_norm_sq_eq`, while the single-component wrapper `euclideanPositiveTimeSingleVector` (`OSToWightmanPositivity.lean:1523`) together with norm supplier `euclideanPositiveTimeSingleVector_norm_sq_eq` (`:1530`) is only a later specialization of that more primitive embedding package; first-consumer restriction: the general Hilbert embeddings first enter here, not earlier in Stage A/B | the OS Hilbert vector attached to transformed-image data | `lemma42_matrix_element_time_interchange` first, then `bvt_wightmanInner_eq_transport_norm_sq_onImage`; later rows may not bypass this map and consume representative data directly |
| `lemma42_matrix_element_time_interchange` | same file | `bvt_transport_to_osHilbert_onImage`, transformed-image data, and the repaired OS-II-backed `bvt_F` / `bvt_W` continuation kernel | the explicit Lemma-4.2 matrix-element interchange seam between the transport map and the quadratic identity | `bvt_wightmanInner_eq_transport_norm_sq_onImage` |
| `bvt_wightmanInner_eq_transport_norm_sq_onImage` | same file | `bvt_transport_to_osHilbert_onImage_wellDefined` to freeze one representative family first, then `bvt_transport_to_osHilbert_onImage`, then `lemma42_matrix_element_time_interchange`, and only then norm-square recognition against the repaired OS-II-backed `bvt_F` / `bvt_W` continuation kernel, using the checked general norm identity `positiveTimeBorchersVector_norm_sq_eq` on the actual transport target rather than skipping straight to the single-component specialization | the on-image quadratic identity `(W(F,F)).re = ‖u(F)‖^2` | `bvt_W_positive_of_transportImage_density` |
| `bvt_W_positive_of_transportImage_density` | same file | `bvt_wightmanInner_eq_transport_norm_sq_onImage`, Hilbert-space density, and bounded finite-support continuity, with checked density supplier `positiveTimeBorchersVector_dense` (`OSToWightmanPositivity.lean:1506`) reserved as the first input consumed here | the implementation-side theorem-3 positivity closure | `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean :: bvt_W_positive` |

Additional theorem-3 clarification:

1. the Section-4.3 test-function transport `(4.19)`-`(4.20)` is explicit and
   should not be documented as a spectral-measure definition;
2. the Wightman-side kernel used later in `(4.24)`-`(4.28)` is the OS-II-repaired
   `bvt_F` / `bvt_W` object, so the production route is safe even though the
   original OS I paper used Lemma 8.8;
3. the half-space dense-range theorem from Lemma 4.1 is a paper-faithfulness
   theorem, but it is not the current minimal blocker for theorem 3; the live
   closure seam is the explicit on-image route through
   `os1TransportComponent_eq_zero_iff`,
   `bvt_transport_to_osHilbert_onImage_wellDefined`,
   `bvt_transport_to_osHilbert_onImage`,
   `lemma42_matrix_element_time_interchange`, and
   `bvt_W_positive_of_transportImage_density`, with `bvt_W_positive` only the
   exported downstream wrapper; and
4. the Stage-C proof transcript is now fixed tightly enough that later Lean
   work should not have to rediscover its internal order: representative choice
   must be discharged first by `bvt_transport_to_osHilbert_onImage_wellDefined`,
   then the transport map is formed into the checked general target
   `positiveTimeBorchersVector`, then Lemma 4.2 rewrites matrix elements, and
   only after that may the norm-square identity be recognized via
   `positiveTimeBorchersVector_norm_sq_eq`; the single-component wrapper
   `euclideanPositiveTimeSingleVector` is downstream specialization only, not
   the primitive Stage-C target.

## 6. Operator-theory gaps

### 6.1. Unbounded spectral theorem / Stone package

Current repo surfaces:

1. `vNA/Unbounded/StoneTheorem.lean`
2. `docs/unbounded_spectral_project.md`

Mathlib status:

1. no unbounded spectral theorem / PVM package,
2. bounded functional calculus exists, but not the needed unbounded theorem.

Decision:

1. this is a serious ecosystem gap,
2. but it is not on the current theorem-2/3/4 OS route,
3. so it should remain a dedicated side project rather than absorbing frontier
   proof time now.

### 6.2. Predual / sigma-weak topology / KMS

Current repo surfaces:

1. `vNA/Predual.lean`
2. `vNA/KMS.lean`
3. `vNA/ModularTheory.lean`
4. `vNA/ModularAutomorphism.lean`

Mathlib status:

1. partial operator-topology infrastructure exists,
2. the full Tomita-Takesaki / KMS / predual packages do not.

Decision:

1. prove locally if and when the project prioritizes operator-algebra work,
2. keep them separate from the OS-route documentation and execution order.

## 7. What should definitely be solved locally first

The following are local project gaps, not reasons to wait for Mathlib:

1. theorem-2 regular-input constructor from boundary data and growth,
2. theorem-3 corrected Section 4.3 transformed-image / quadratic-identity /
   density-closure layer,
3. theorem-4 one-factor extraction bookkeeping,
4. SCV tube boundary-value constructor from polynomial growth,
5. general-`k` Malgrange-Zerner / envelope packages,
6. GNS matrix-coefficient holomorphic bridge in the one-variable forward-tube
   language.

## 8. What is plausible to upstream later

The following later packages could plausibly be generalized and upstreamed:

1. separate continuity on Frechet products,
2. Schwartz kernel/nuclear theorem packaging,
3. some SCV gluing lemmas around tube domains,
4. possibly the bounded parts of the spectral/integral story.

But none of those should be prerequisites for current documentation-guided
progress in this repo.

## 9. Route consequences for later Lean work

When Lean proof work resumes, the first question should not be:

> "does Mathlib already have this?"

It should be:

> "is this theorem already explicitly documented as a local package we need?"

If yes, implement it locally first and upstream later only if that becomes the
best cleanup path.

## 10. Quick-reference table

| Gap | Current status | Action |
|---|---|---|
| `NormSMulClass ℝ ℂ` regression | confirmed | upstream issue + local shim |
| Frechet separate-to-joint continuity | missing | local proof |
| Schwartz kernel theorem | missing | local proof/import package |
| tube BV from polynomial growth | axiomatic | local SCV proof |
| Malgrange-Zerner | missing | local SCV proof |
| envelope theorem on mixed domains | missing | local SCV proof |
| theorem-2 regular constructor | missing local theorem | local proof |
| unbounded spectral theorem | ecosystem gap | side project / defer |
| full predual/KMS package | ecosystem gap | side project / defer |

This file should evolve whenever a gap moves from "external blocker" to
"explicit local theorem package."
