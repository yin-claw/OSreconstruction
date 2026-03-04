# Invariant Function Proof (d=1, n=2)

This is the primary local note for the blocker proof route.

## Problem
Given a sourced invariant kernel `f(q0,q1,p,s)`, prove swap involution on the doubly witnessed invariant locus:

- `f(q0,q1,p,s) - f(q1,q0,p,-s) = 0`
- under `s^2 = 4(p^2 - q0 q1)` and paired light-cone witness assumptions.

## Invariant Setup
- Invariants used: `q0, q1, p, s` with one algebraic relation.
- Independent invariant count is effectively 3; `s` records branch/sign data.
- Swap involution acts by
  - `(q0,q1,p,s) -> (q1,q0,p,-s)`.

## Working Function
Define
- `g(q0,q1,p,s) := f(q0,q1,p,s) - f(q1,q0,p,-s)`.

Goal is `g = 0` on the doubly witnessed locus.

## Formal Route in Lean
1. Start from `d1N2InvariantKernelSource f`.
2. Use existing reduction theorem in `PermutationFlowBlockers/Tail.lean`:
   - blocker follows from paired-chart anchor connectivity of sourced `F`.
3. Prove paired-chart anchor connectivity on variable charts.
4. Conclude blocker equation (`g=0`) on the target locus.

## Why Not Full Quadric
A formal theorem shows source package does not force `g=0` on the entire quadric for arbitrary off-image extensions of `f`.

Hence the proof target is intentionally the realizable/light-cone witnessed locus.

## Current Practical Focus
- construct and prove the remaining paired-chart anchor step,
- without adding extra axioms,
- and without detouring through unrelated d>=2 infrastructure.

### Current intrinsic-core decomposition (Tail, 2026-03-04)
Inside
`blocker_d1N2InvariantKernelSwapEq_onSectionWitnessPair_invariantFunction_core_deferred`,
the proof is now factored as:

1. intrinsic witnessed domain `D ⊂ ℂ^4`,
2. intrinsic swap-difference `g(q0,q1,p,s)`,
3. direct reductions
   - `hDiffD : DifferentiableOn ℂ g D`,
   - `hPreD : IsPreconnected D`,
   - `hCorrOnReal :` real-slice spacelike tuples imply `g = 0`.

The remaining deferred step is only the analytic propagation:

- from the three items above, derive `g = 0` on all of `D`.

This is exactly where a boundary-identification/analytic-propagation bridge is
still needed (quadric chart + totally-real identity route).

Implemented chart helpers in `Tail.lean` for this route:
- `d1N2QuadricChart`,
- `d1N2QuadricChart_quadric`,
- `d1N2QuadricChart_apply_of_quadric`,
- `d1N2QuadricChart_differentiableAt`.

Also added real-slice sign lemmas showing an intrinsic obstruction:

- with both original and swapped witness inequalities, real tuples satisfy
  `q0.re + q1.re - 2*p.re < 0`.

So the real-spacelike correction anchors (`> 0`) do not directly lie in the
witnessed domain, confirming that a separate boundary-identification /
propagation bridge is still required.

Tail now also has an explicit nontrivial witnessed-domain point
(`d1N2InvariantWitnessedDomain_nontrivial_example`) with `q0 ≠ q1`, so this
domain is not vacuous and the swap-difference target is genuinely nontrivial.

A formal harness now also records a consistency obstruction:
- `ProofHarness/D1N2InvariantCoreCounterexample.lean`
- theorem `d1N2InvariantCore_counterexample_if_connected`.

It shows that, under preconnectedness of the current witnessed domain, the
present core theorem hypothesis shape (analyticity + connectedness + only
real-spacelike correction `>0`) yields a contradiction. This confirms that an
additional bridge/input is required for this route.

Numerical check aligned with this sign fact:
- random stress over `12000` sampled real-spacelike quadric tuples
  (`q0.im=q1.im=p.im=s.im=0`, `q0+q1-2p>0`) with random complex witness search
  (`4000` random `(v0,w0)` attempts per tuple) found `0` tuples satisfying both
  intrinsic witness-inequality blocks simultaneously.

## New Formal Geometry Fact (Tail)
`Tail.lean` now includes:

- `d1N2SectionOrig_mem_forwardTube_of_witnessIneq`
- `d1N2SectionSwap_mem_forwardTube_of_witnessIneq`

These are kept as direct geometric conversion lemmas (intrinsic witness
inequalities to section-coordinate `ForwardTube` membership), without extra
wrapper packaging.

## Source-to-Invariant Bridge Split (Current Tail State)
`Tail.lean` now separates:

1. a proved invariant-function reduction theorem
   `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_invariantFunction_core_deferred`
   that consumes intrinsic invariant-function assumptions
   (analyticity + preconnectedness + correction),
2. a single deferred source-wrapper bridge theorem
   `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariantOnly_core_deferred`
   whose remaining work is deriving the source-to-invariant bridge inputs from
   `d1N2InvariantKernelSource f`.
   The remaining source-side deferred input is now an explicit local witness
   requirement (`hBoundary`) inside this theorem: per real-slice spacelike
   tuple, produce `x` with matching invariants and the two boundary
   value-identifications for `f`.
   The theorem
   `blocker_d1N2InvariantBoundaryApproachFamilies_fromSource_deferred` is now a
   proved obstruction statement (not an existence bridge): under real-slice
   spacelike assumptions, simultaneous original+swapped fixed-invariant `FT`
   approach families are impossible.
   A non-deferred pass-through theorem remains available once the three bridge
   inputs are provided explicitly:
   `d1N2InvariantKernelDiffZeroOnForwardizableQuadric_of_source_and_invariantBridgeInputs`.

Correction statement lock:
- The correction premise is now real-slice spacelike and fully intrinsic:
  on the quadric, with
  `q0.im = q1.im = p.im = s.im = 0` and
  `q0.re + q1.re - 2*p.re > 0`, enforce
  `f q0 q1 p s = f q1 q0 p (-s)`.
- `blocker_d1N2InvariantBridgeCorrection_fromSource_deferred` is now a proved
  reduction, provided an explicit per-point source-to-invariant
  boundary-identification witness.
- The false claim that this boundary-identification follows from
  `d1N2InvariantKernelSource` alone has been removed from the proved bridge
  chain; the unresolved bridge is tracked explicitly as the local `hBoundary`
  deferred input inside
  `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariantOnly_core_deferred`.
- The existing formal counterexample harness records the key obstruction:
  source data alone does not constrain arbitrary off-image values of `f` on
  this real-spacelike set, so the bridge must include source-to-invariant
  analytic/boundary identification.
  - `ProofHarness/D1N2SourceCorrectionCounterexample.lean`
  - theorem:
    `d1N2InvariantKernelSource_not_sufficient_for_realSpacelikeCorrection_nonzero`.

These assumptions are consumed directly by
`blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_invariantFunction_core_deferred`;
the source-wrapper theorem remains deferred at the bridge step.

## Meaning of "Bridge Analyticity"
`bridgeAnalyticity` is a statement of `DifferentiableOn ℂ` for the invariant
swap-difference function on the intrinsic witnessed quadric locus.

It is not an analytic-continuation/extension claim to a larger ambient domain.

## Numerical Validation Scope
The numerical harness
`ProofHarness/d1n2_invariant_witness_equivalence.py` validates the intrinsic
witness inequalities used in the core theorem statement against the intended
section-coordinate `ForwardTube` inequalities on sampled data.

The stress harness
`ProofHarness/d1n2_tail_four_critical_lemma_checks.py` now samples:
- source constraints on real-spacelike tuples (intrinsic + z-constructed),
- correction anchors on real-spacelike tuples (intrinsic + z-constructed),
- complex witnessed-domain tuples from `z in FT` with explicit swap-then-Lorentz
  witness,
- boundary-geometry reconstruction checks from intrinsic real invariants
  `(q0,q1,p,s)` back to real witness coordinates,
- a direct source-to-forwardizable surrogate check for
  `blocker_d1N2ForwardWitnessEq_field_deferred` (test 5),
- a local fixed-witness neighborhood surrogate for
  `blocker_d1N2LocalForwardEqNhd_core_deferred` (test 7),
- an explicit off-image spike stress for the source-only correction shape
  (test 8),
- a swapped-branch FT realizability stress on sampled real-spacelike tuples
  (test 9).
Current runs report no numeric falsifier for tests 1/2/3/4/5/6/7 in the finite
ansatz model.

This numerical check supports the witness-inequality translation only; it does
not prove the three bridge lemmas above.

## Why These Tests Are Informative
These runs test populated sampled domains under the current theorem
assumptions, so the reported “no falsifier found” outcomes are based on actual
constraint-and-evaluation checks (not empty-set behavior).

Latest stress runs (2026-03-04) from
`ProofHarness/d1n2_tail_four_critical_lemma_checks.py`:

- Deep single run:
  - Test 1 (invariant core implication):
    - correction-anchor samples: `9000`,
    - complex witnessed-domain samples: `4000`,
    - correction-constrained nullspace dimension: `0`,
    - worst sampled `|g|` on complex witnessed domain: `0.0` (threshold `1e-6`).
  - Test 4 (bridge correction surrogate):
    - correction-anchor samples: `9000`,
    - direct z-family correction-hit rate: `30000/30000`,
    - worst sampled `|g|` on correction anchors: `0.0`.
  - Test 3 (bridge preconnectedness surrogate):
    - complex witnessed-domain samples: `4000`,
    - KNN graph components: `1`,
    - largest component: `4000/4000` points (`k=10`).
  - Test 2 (bridge analyticity surrogate):
    - source-constraint samples: `9000`,
    - source-constrained antisymmetric nullspace dimension: `0`,
    - finite-difference checks: `300` points, max sampled `|∂̄g| = 0.0`.
  - Test 5 (forward witness equality surrogate):
    - source-constraint samples: `4000`,
    - complex forwardizable samples: `1800`,
    - worst sampled `|g|` on forwardizable domain: `0.0`.
  - Test 6 (boundary geometry reconstruction):
    - intrinsic + near-`q0=0` + z-constructed tuples checked: `200000`,
    - reconstruction failures: `0`,
    - max invariant reconstruction error: `2.10e-11`.
  - Test 7 (local fixed-witness neighborhood surrogate):
    - local centers: `120/120` collected,
    - local prepared-neighborhood points checked: `14400`,
    - rejected local perturbations: `1`,
    - worst sampled `|g|` on local prepared points: `0.0`
      (threshold `1e-6`).
  - Test 8 (source-only correction shape, off-image spike surrogate):
    - probe tuple `(9,1,3,0)` satisfies quadric + real-slice + spacelike,
    - min sampled supnorm distance from probe to source-domain samples:
      `4.05`,
    - sampled source-domain hits near probe (`tol=1e-4`): `0`,
    - spike value on source-domain samples: `0`,
    - spike value at probe: `1`,
    - status: `SOURCE_ONLY_SHAPE_PLAUSIBLY_FALSE`.
  - Test 9 (swapped-branch FT realizability on real-spacelike samples):
    - sampled tuples: `360` (`180` real-FT family + `180` phase-locked family),
    - randomized exact-invariant search trials per tuple: `9000`,
    - original branch FT hits: `360/360`,
    - swapped branch FT hits: `0/360`,
    - status: `SWAPPED_BRANCH_NOT_FOUND_ON_SAMPLED_REAL_SPACELIKE_TUPLES`.

- Multi-seed sweep (`20260300..20260305`):
  - per seed:
    - source constraints: `3700`,
    - correction anchors: `7500`,
    - complex witnessed-domain samples: `3200`,
    - boundary reconstruction checks: `100000`.
  - aggregate across 6 seeds:
    - boundary reconstruction checks: `600000`,
    - boundary reconstruction failures: `0`,
    - worst boundary reconstruction error across seeds: `2.97e-11`,
    - source/correction nullspace dimensions: always `0`,
    - all reported statuses: `NO_NUMERIC_FALSIFIER_FOUND` (`24/24` checks),
    - test 9 (swapped-branch FT realizability):
      original branch hits `240/240` on all seeds,
      swapped branch hits `0/240` on all seeds.

Interpretation:
- These are genuine finite-model falsification checks because sampled anchor
  and target domains are populated (not empty), and `g` is evaluated on those
  sets under the intended constraint families.
- For the source-only correction shape, test 4 alone is inconclusive when the
  sampled source-constrained nullspace collapses to dimension `0`; test 8 is
  the relevant stress for off-image freedom.
- Test 9 supports the current formal concern that real-spacelike correction data
  does not naturally come from swapped-branch FT realizability, so a separate
  source-to-invariant boundary-identification mechanism is required.
- This geometric obstruction is now also formalized in `Tail.lean`:
  `d1N2InvariantRealizablePair_real_spacelike_impossible` and
  `d1N2InvariantForwardizableSwap_real_spacelike_impossible`.
- They remain heuristic (not formal proof): finite ansatz + finite sampling.
