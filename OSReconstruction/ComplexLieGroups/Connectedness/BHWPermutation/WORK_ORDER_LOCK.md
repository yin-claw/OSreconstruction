# WORK_ORDER_LOCK (d=1, n=2 blocker only)

## Scope Lock
This lock file tracks only the active analytic blocker for the `d=1, n=2` route.

- Priority lock (2026-03-04):
  - Top priority is numerical verification of the remaining `sorry` lemmas.
  - For each active deferred statement, first establish high-quality numerical
    support/falsification checks aligned with the exact theorem hypotheses.
  - Whether a lemma can be proved immediately in the current Lean
    infrastructure is secondary to first confirming the mathematical statement.

- Hard-focus lock (2026-03-04):
  - Active proof work is restricted to `d=1, n=2` lemmas only.
  - `n = 3` / `n ≥ 4` geometric branches are explicitly out of scope for this
    lock unless a separate lock update states otherwise.
  - Within `d=1,n=2`, current sprint focus is analytic extension only.
  - Do not spend active proof effort on connectivity/preconnectedness lemmas in
    this sprint; they are parked unless explicitly re-enabled.

- Active blocker theorem:
  - `blocker_d1N2InvariantKernelSwapEq_onSectionWitnessPair_invariantFunction_core_deferred`
  - File: `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlowBlockers/Tail.lean`
- Route lock:
  - Lorentz-invariant-function route only.
  - No translation-invariance detour.
  - No new axioms.

## Invariant-Only Statement Lock (2026-03-03)
- The deferred core blocker must be stated only for the invariant kernel
  `f(q0,q1,p,s)` and invariant tuple predicates on `(q0,q1,p,s)`.
- In the deferred core theorem statement, do **not** mention:
  - `D1N2Config`
  - `ForwardTube`
  - `complexLorentzAction`
  - explicit Lorentz witnesses (`Γ`, `Λ`)
  - explicit coordinate witnesses (`z`, `y`, etc.)
- Forward/FT witness geometry must be encoded via invariant predicates only
  (for example `d1N2InvariantSectionWitnessPair`, realizability, forwardizable).
- Analytic/local-commutativity assumptions in the deferred core statement must be
  assumptions on the invariant kernel function `f` (function-level packaging),
  not coordinate-level transition statements.
- Coordinate-level bridges from source-field data to those function-level
  assumptions are wrapper lemmas and are outside the deferred core blocker.
- The deferred core theorem must include an explicit correction-condition
  hypothesis on `f` (in invariant variables), not assert swap symmetry with no
  analytic/correction premises.

## Critical Statement Lock (2026-03-04)
The active deferred lemmas in `PermutationFlowBlockers/Tail.lean` are
locked exactly as currently stated:

1. `blocker_d1N2InvariantKernelSwapEq_onSectionWitnessPair_invariantFunction_core_deferred`
   - assumptions: `hAnalytic`, `hConnected`, real-slice spacelike `hCorrection`;
   - goal: swap equality on doubly witnessed quadric points.
   - proof-body status (2026-03-04):
     now explicitly decomposed in `Tail.lean` into intrinsic objects
     `D(q0,q1,p,s)` and `g(q0,q1,p,s)`, with the real-slice correction
     reduction (`hCorrOnReal`) formalized; the only remaining `sorry` in this
     theorem is the intrinsic analytic propagation step
     (`DifferentiableOn + IsPreconnected + real-slice vanishing -> g = 0 on D`).
     Current substep closure inside the theorem also includes the pullback
     charted differentiability fact on `U := {w | chart w ∈ D}`.
     New geometric note (formalized helper lemmas): under both intrinsic witness
     inequalities on real tuples, one gets
     `q0.re + q1.re - 2*p.re < 0`; hence real-spacelike (`> 0`) correction
     anchors do not directly lie in the witnessed domain.
     The intrinsic witnessed domain is confirmed nonempty/nontrivial by an
     explicit formal example with `q0 ≠ q1`:
     `d1N2InvariantWitnessedDomain_nontrivial_example`.
     Supporting numerics (2026-03-04): stress sampling over `12000` real-spacelike
     tuples with random complex witness search (`4000` witness attempts each)
     yielded `0` hits for simultaneous original+swapped witness inequalities.
     Formal obstruction harness (2026-03-04):
     `ProofHarness/D1N2InvariantCoreCounterexample.lean`,
     theorem `d1N2InvariantCore_counterexample_if_connected` shows that if this
     witnessed domain is preconnected, the current core hypothesis shape
     (analyticity + connectedness + only real-spacelike `>0` correction) is
     inconsistent; hence an additional bridge/input is required.
2. `blocker_d1N2InvariantBridgeAnalyticity_fromSource_deferred`
   - source package to `DifferentiableOn` of invariant swap-difference on the
     witnessed quadric domain.
   - status (2026-03-04): proved in `Tail.lean` (sorry-free).
3. `blocker_d1N2InvariantBridgePreconnected_fromSource_deferred`
   - geometry-only `IsPreconnected` input for the same witnessed quadric domain
     (no source wrapper parameters).
4. source-to-invariant correction bridge
  - no source-only boundary-identification theorem claim is kept in `Tail.lean`
    (that shape is formally false from source data alone),
  - `blocker_d1N2InvariantBridgeCorrection_fromSource_deferred` remains a proved
    conditional bridge: given an explicit boundary-identification witness, it
    yields intrinsic correction equality in `(q0,q1,p,s)`,
  - `blocker_d1N2InvariantBoundaryApproachFamilies_fromSource_deferred` is now a
    sound obstruction theorem (real-spacelike hypotheses imply simultaneous
    original+swapped fixed-invariant `FT` approach families are impossible),
  - active deferred source input is now explicit as the local `hBoundary` `sorry`
    inside
    `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariantOnly_core_deferred`.

No wrapper aliases are to be introduced for these statements; edits should
target these declarations directly.

### Active-sprint subset (2026-03-04)
- Active target:
  - analytic-extension components feeding
    `blocker_d1N2InvariantKernelSwapEq_onSectionWitnessPair_invariantFunction_core_deferred`.
  - `blocker_d1N2InvariantBridgeAnalyticity_fromSource_deferred` is closed.
- Parked (not active this sprint):
  - `blocker_d1N2InvariantBridgePreconnected_fromSource_deferred`
  - other connectivity-only obligations.

## Bridge-Lemma Lock (2026-03-03 update)
- The invariant-function reduction step is now explicit and proved as:
  - `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_invariantFunction_core_deferred`.
- This theorem takes exactly the three intrinsic invariant-function inputs:
  1. witnessed-locus differentiability of the swap-difference,
  2. witnessed-locus preconnectedness,
  3. real-slice spacelike correction rule for `f`.
- The source-to-invariant bridge is locked to three explicit bridge inputs:
  1. `blocker_d1N2InvariantBridgeAnalyticity_fromSource_deferred`,
  2. `blocker_d1N2InvariantBridgePreconnected_fromSource_deferred`,
  3. `blocker_d1N2InvariantBridgeCorrection_fromSource_deferred`.
- The source wrapper theorem
  `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariantOnly_core_deferred`
  must consume these three bridge inputs directly (no hidden bridge packaging).
- Numerical checks support only the intrinsic witness-inequality translation
  (section-coordinate FT inequalities ↔ invariant inequalities), not the full
  proofs of (1)-(3).
- Correction-hypothesis lock (current statement):
  - the correction premise in the invariant core is:
    quadric relation + real-slice conditions + spacelike inequality
    `q0.re + q1.re - 2*p.re > 0`.
  - no explicit `ForwardTube`/`D1N2Config`/Lorentz-action terms appear in this
    correction premise.
  - `blocker_d1N2InvariantBridgeCorrection_fromSource_deferred` targets this
    intrinsic real-slice spacelike correction statement.
- Source-implies-correction status:
  - deriving the required per-point boundary-identification witness from
    `d1N2InvariantKernelSource` remains deferred as a local input (`hBoundary`)
    in
    `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariantOnly_core_deferred`.
  - numerics now include an explicit off-image spike stress (test 8) that
    reports `SOURCE_ONLY_SHAPE_PLAUSIBLY_FALSE`.
  - a formal counterexample records that source data alone does not force
    arbitrary off-image values of `f` on that real-spacelike set, so bridge
    closure must include the source-to-invariant analytic/boundary
    identification step.
  - harness theorem:
    `ProofHarness/D1N2SourceCorrectionCounterexample.lean`
    (`d1N2InvariantKernelSource_not_sufficient_for_realSpacelikeCorrection_nonzero`).

## Current Lean State
- The entire `OSReconstruction/ComplexLieGroups` folder compiles.
- Remaining `sorry` frontiers in this branch are concentrated in `PermutationFlowBlockers/Tail.lean`.
- Current `d=1,n=2` status:
  - `blocker_d1N2InvariantKernelSwapDiffZeroOnLightConeWitness_invariantQuadric_core_deferred`
    is now a clean reduction theorem (no internal `sorry`).
  - `blocker_d1N2PairedChartAnchorPair_fromSource_deferred` is now structural
    (no internal `sorry`) and reduces to forward witness equality.
  - active deferred front is split between:
    1. invariant-core theorem
       `blocker_d1N2InvariantKernelSwapEq_onSectionWitnessPair_invariantFunction_core_deferred`,
    2. source-to-invariant bridge lemmas
       (`...BridgePreconnected...`) plus the explicit boundary-identification
       input (`hBoundary`) inside
       `...InvariantKernelDiffZeroOnForwardizableQuadric_source_invariantOnly...`.
  - local `d=1,n=2` fixed-witness neighborhood theorem
    `blocker_d1N2LocalForwardEqNhd_core_deferred` is now sorry-free and derived
    from `blocker_d1N2ForwardWitnessEq_field_deferred`.
- Wrapper cleanup status:
  - removed unused paired-chart equivalence wrappers from
    `PermutationFlowBlockers/Core.lean` to keep the blocker route minimal.
  - removed additional dead forwardizable/pair-swap equivalence wrappers in
    `PermutationFlowBlockers/Core.lean` (light-cone/section/witness-form and
    source/open-anchor adapters) that had no downstream references.
  - removed unused `d=1,n=2` EOW-package adapter cluster from
    `PermutationFlowBlockers/Core.lean`.
  - removed the now-unused connected-open-anchor bridge theorem in
    `PermutationFlowBlockers/Core.lean` after confirming zero downstream uses.
  - removed dead `Tail.lean` wrappers (`invariantModel`, pointwise-anchor, and
    source-open-anchor helpers) that had no call sites.
  - removed additional dead `Tail.lean` correction wrappers with no call sites
    (`d1N2InvariantKernelSwapEq_onSectionWitnessPair_realSlice_of_correction`
    and the real-spacelike witness-negation wrapper chain).
- no change to blocker mathematics; only proof-graph pruning.
- `PermutationFlowBlockers/Core.lean` is now reduced to 658 lines.

## Canonical Reduction Chain
From current theorems in `Core/Tail`:

1. `d1N2InvariantKernelSource f`
2. target blocker:
   - light-cone witness diff-zero on invariant quadric tuples
3. exact reduction already formalized:
   - enough to prove `blocker_d1N2PairedChartAnchorPair_fromSource_deferred`
     (one anchored pair equality per doubly witnessed tuple)
   - via `d1N2PairedChartAnchorConnected_of_exists_anchorPair`, this yields
     `d1N2PairedChartAnchorConnected (Classical.choose hsource)`
4. once paired-chart anchor is obtained, the blocker follows immediately through
   `d1N2InvariantKernelSwapDiffZeroOnLightConeWitness_of_pairedChartAnchorConnected`.

## Mathematical Content of the Blocker
For `f : C^4 -> C`, prove:

- for all `q0 q1 p s` with `s^2 = 4(p^2 - q0 q1)`,
- if both `(q0,q1,p,s)` and `(q1,q0,p,-s)` admit light-cone witnesses in `FT_{1,2}`,
- then
  - `f q0 q1 p s - f q1 q0 p (-s) = 0`.

Equivalent involution form:

- `f(q0,q1,p,s) = f(q1,q0,p,-s)`
- on the doubly-witnessed locus of the invariant quadric.

## What Is Already Settled
- Invariant factorization exists on `FT_{1,2}`.
- Forwardizable/realizable/light-cone witness reformulations are in place.
- Source-level bridge lemmas between invariant equalities and forward equalities are in place.
- Obstruction that source data alone does not force full-quadric involution (`off-image` values) is formalized in:
  - `d1N2InvariantKernelSource_not_sufficient_for_quadricDiffZero`.

## Failed Routes / Guardrails (Do Not Reopen)
- EOW geometry/open-anchor route for `d=1,n=2` is not the closure path for this blocker.
- Proof attempts requiring fixed-anchor charts (`v0 = i` or `u0 = i` globally) are too rigid.
- Full-quadric identity theorem without realizability restrictions is false under current hypotheses.

Details are recorded in:
- `D1_N2_BLOCKER_AUDIT.md`
- `D1_N2_LORENTZ_INVARIANT_ROUTE.md`

## Work Plan (Execution Order)
1. Keep active blocker statement unchanged.
2. Prove paired-chart anchor connectivity from source package on variable charts.
3. Feed it into the existing reduction theorem to close blocker.
4. Re-run:
   - `lake env lean OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlowBlockers/Tail.lean`
   - `lake env lean OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlowBlockers.lean`
   - full folder compile for `OSReconstruction/ComplexLieGroups`.

## Parallel Falsification Track (Required)
Run this in parallel with constructive proof work to avoid proving a false target.

1. Counterexample target:
   - search for `f` and a doubly light-cone-witnessed quadric tuple
     `(q0,q1,p,s)` such that
     `f q0 q1 p s - f q1 q0 p (-s) ≠ 0`
     under `d1N2InvariantKernelSource f`.
2. Candidate pruning:
   - reject off-image tuples that are not realizable/light-cone-witnessed.
   - keep all checks on the exact blocker hypotheses, not weaker surrogates.
3. If a valid counterexample is found:
   - stop closure attempt, record witness in local docs and tests,
   - restate blocker theorem accordingly.
4. If no counterexample is found:
   - continue constructive route and keep search harness tests compiling.
5. Latest heuristic sweep status (2026-03-03):
   - reproducible script:
     `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/ProofHarness/d1n2_counterexample_search.py`
   - run A (degree 3, 500 real constraints, 1200 forwardizable tuples, 20 nullspace combos):
     - antisym basis size: 27
     - nullspace dim under sampled local-comm constraints: 13
     - max observed `|g|` on sampled forwardizable tuples: `2.18e-11`
     - violations above `1e-6`: 0
   - run B (degree 4, 1200 real constraints, 1500 forwardizable tuples):
     - antisym basis size: 56
     - nullspace dim: 0 (no nonzero sampled antisymmetric ansatz survives)
   - run C (degree 5, 2200 real constraints, 2200 forwardizable tuples):
     - antisym basis size: 106
     - nullspace dim: 0 (no nonzero sampled antisymmetric ansatz survives)
   - run D (degree 6, 3200 real constraints, 2600 forwardizable tuples):
     - antisym basis size: 180
     - nullspace dim: 0 (no nonzero sampled antisymmetric ansatz survives)
   - run E (degree 7, 4500 real constraints, 3200 forwardizable tuples):
     - antisym basis size: 290
     - nullspace dim: 0 (no nonzero sampled antisymmetric ansatz survives)
   - run F (degree 8, 6200 real constraints, 4200 forwardizable tuples):
     - antisym basis size: 440
     - nullspace dim: 0 (no nonzero sampled antisymmetric ansatz survives)
   - no sampled counterexample found.

## Numerical Test Interpretability Note (2026-03-04)
- Harness assumptions are aligned with current theorem statements
  (quadric + real slice + spacelike).
- Current stress-run counts from
  `ProofHarness/d1n2_tail_four_critical_lemma_checks.py`:
  - correction anchors: `9000`,
  - complex witnessed-domain points: `4000`,
  - source-constraint points: `9000`,
  - direct z-family correction hits: `30000/30000`,
  - boundary-geometry reconstruction checks (test 6): `200000` with
    `0` failures (max reconstruction error `2.10e-11`).
  - local prepared-neighborhood surrogate checks (test 7): `14400`
    sampled local points, no falsifier found.
  - source-only correction off-image spike stress (test 8):
    status `SOURCE_ONLY_SHAPE_PLAUSIBLY_FALSE`.
  - swapped-branch FT realizability stress (test 9) on sampled real-spacelike
    tuples:
    - sampled tuples: `360` (`180` real-FT family + `180` phase-locked family),
    - per-tuple randomized exact-invariant search trials: `9000`,
    - original-branch FT hits: `360/360`,
    - swapped-branch FT hits: `0/360`,
    - status:
      `SWAPPED_BRANCH_NOT_FOUND_ON_SAMPLED_REAL_SPACELIKE_TUPLES`.
  - multi-seed test 9 sweep (`20260300..20260305`) with
    `240` tuples/seed and `7000` searches/tuple:
    - original-branch hits: `240/240` on all `6/6` seeds,
    - swapped-branch hits: `0/240` on all `6/6` seeds.
- Multi-seed sweep (`20260300..20260305`) with the same harness:
  - per seed: source constraints `3700`, correction anchors `7500`,
    complex witnessed-domain points `3200`, boundary reconstruction checks
    `100000`;
  - aggregate boundary reconstruction checks: `600000`, failures: `0`,
    worst max reconstruction error across seeds: `2.97e-11`;
  - source and correction nullspace dimensions were `0` on all seeds;
  - all reported test statuses were `NO_NUMERIC_FALSIFIER_FOUND`.
- Therefore tests 1/3/4 are not vacuous empty-domain checks; they evaluate the
  antisymmetric kernel on populated sampled domains.
- For bridge-correction interpretation, test 4 by itself can be inconclusive
  when sampled source-constrained nullspace collapses to `0`;
  test 8 is the relevant stress for off-image freedom.
- For source-side boundary identification on real-spacelike tuples, test 9
  indicates an additional geometric/analytic mechanism is needed beyond simple
  swapped-branch FT realizability.
- Test 2 is also non-vacuous in sampling, but remains a finite-ansatz
  differentiability surrogate (not a formal analytic proof).

## Formal Obstruction Note (Bridge Correction)
- There is a formal counterexample theorem in
  `ProofHarness/D1N2SourceCorrectionCounterexample.lean`:
  `d1N2InvariantKernelSource_not_sufficient_for_realSpacelikeCorrection_nonzero`.
- The same file now also records the direct shape-level negation:
  `d1N2_source_not_sufficient_for_bridgeCorrection_shape`.
- This records that `d1N2InvariantKernelSource` alone does not force arbitrary
  off-image values of `f` on the full real-spacelike quadric set.
- Practical consequence for proving campaign:
  - do not attempt a source-only correction theorem shape;
    keep the explicit boundary-identification bridge input in the source wrapper
    reduction step.
  - formalized geometric obstruction in `Tail.lean`:
    `d1N2InvariantRealizablePair_real_spacelike_impossible` and
    `d1N2InvariantForwardizableSwap_real_spacelike_impossible`.

Counterexample harness file:
- `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/ProofHarness/D1N2CounterexampleSearch.lean`
  - includes formal proposition `d1N2ActiveBlockerStatement`,
    formal counterexample predicate, and lemma
    `d1N2ActiveCounterexample_implies_not_statement`.

Proof-harness test files:
- `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/ProofHarness/D1N2ReductionChain.lean`
- `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/ProofHarness/D1N2SectionInvariants.lean`
- `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/ProofHarness/D1N2ObstructionChecks.lean`
- `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/ProofHarness/D1N2LocalAnchorTransport.lean`

## Notes for Collaborators
- This file intentionally omits d>=2 and n>=3 planning.
- If adding new docs, include only material directly tied to proving the active blocker or documenting a failed d=1,n=2 attempt/counterexample.
