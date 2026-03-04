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
   whose remaining work is deriving those three assumptions from
   `d1N2InvariantKernelSource f`.
   A non-deferred pass-through theorem is now available once those three bridge
   inputs are provided explicitly:
   `d1N2InvariantKernelDiffZeroOnForwardizableQuadric_of_source_and_invariantBridgeInputs`.

Correction statement lock:
- The correction premise is now real-slice witnessed and fully intrinsic:
  on the quadric, with both intrinsic witness inequalities and
  `q0.im = q1.im = p.im = s.im = 0`, enforce
  `f q0 q1 p s = f q1 q0 p (-s)`.
- This avoids the incompatible standalone spacelike-sign condition (`> 0`) on
  real paired-witness points.
- Deriving this witnessed correction premise from
  `d1N2InvariantKernelSource` remains part of the deferred bridge work.
- The existing formal counterexample harness still records why the old
  spacelike-only correction variant is unusable:
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

This numerical check supports the witness-inequality translation only; it does
not prove the three bridge lemmas above.
