# BHW Permutation Status

`BHWPermutation/PermutationFlow.lean` is now direct-sorry-free.

## Current Status

The former local blocker file `PermutationFlowBlocker.lean` has been deleted.
Its two unresolved geometric inputs are no longer hidden as local `sorry`s.
They now appear explicitly as theorem hypotheses on the live BHW surfaces:

- `Connectedness/BHWPermutation/PermutationFlow.lean`
- `Wightman/Reconstruction/AnalyticContinuation.lean`

Concretely, the active theorem surfaces now require:

1. connectedness of `permSeedSet` in the nontrivial `d >= 2` branch
2. the `d = 1` ET-overlap permutation-invariance bridge

This keeps the code honest: the permutation-flow lane itself has no hidden local
blockers, and the remaining geometry is exposed exactly where it is used.

Use `docs/BHW_STATUS.md` for the higher-level mathematical plan.
