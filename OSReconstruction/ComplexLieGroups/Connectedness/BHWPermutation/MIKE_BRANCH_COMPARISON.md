# Mike Branch Comparison (Detailed)

Last updated: 2026-03-01

This note records a careful comparison between:

- local branch: `wip/permutationflow-unblock` (this repository),
- Mike's branch snapshot from:
  - `https://github.com/mrdouglasny/OSreconstruction-1`
  - file used for high-level claims:
    `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/STATUS.md`.

## Scope of Comparison

Compared files from Mike's branch (downloaded to `/tmp/mike_bhw`):

- `SeedSlices.lean`
- `JostWitnessGeneralSigma.lean`
- `Adjacency.lean`
- `IndexSetD1.lean`
- `OverlapConnected.lean`
- `PermutationFlow.lean`
- `STATUS.md`

### Verified facts

1. Mike introduces a new large module:
   - `OverlapConnected.lean` (~1037 lines).
2. Mike's `PermutationFlow.lean` is substantially slimmer (~2651 lines) and imports
   `OverlapConnected`.
3. No `sorry` remain in Mike's compared files, but three explicit axioms are present
   in `OverlapConnected.lean`:
   - `complexLorentzGroup_KAK`
   - `isConnected_boostStrip_inter_sliceIndexSet`
   - `hExtPerm_of_d1`

These are not hidden assumptions; they are explicitly declared as `axiom`.

## What Mike Has Achieved (Mathematical/Architectural)

Mike's branch has a clean, explicit `d>=2` proof route packaged in one place:

1. connectedness of slice index set (`isConnected_sliceIndexSet`) from KAK + boost-strip axioms,
2. connectedness of forward-overlap set by iUnion/slice gluing
   (`isConnected_permForwardOverlapSet`),
3. connectedness of ET-overlap (`isConnected_etOverlap`),
4. identity-theorem closure on ET-overlap, yielding `hExtPerm_of_d2`.

Then `PermutationFlow.lean` does a direct case split:

- `d=0`: vacuous/forced permutation identity branch,
- `d=1`: use axiom `hExtPerm_of_d1`,
- `d>=2`: use theorem `hExtPerm_of_d2`.

This is a major architecture simplification for the global theorem flow.

## Precise Relation to Our Current Blockers

Our active `sorry`s in local `PermutationFlow.lean`:

1. `deferred_isConnected_permOrbitSeedSet_dge2`
2. `deferred_isConnected_permOrbitSeedSet_d1`
3. `deferred_d1_adjSwap_forward_open_anchor`
4. `deferred_d1_forward_triple_nonempty_nge4`

Compatibility map:

- Mike's KAK + boost-strip axioms are conceptually aligned with (1)
  (`d>=2` connectedness chain), though not in the exact same theorem names.
- Mike's `hExtPerm_of_d1` is a higher-level axiom that bypasses our local `d=1`
  blocker subtree; it does not constructively prove (2)/(3)/(4) individually.
- Therefore Mike's branch and ours are compatible in conclusion, but at different
  granularity:
  - Mike: assume high-level `d=1` extension invariance.
  - Ours: construct `d=1` through local geometric/analytic lemmas.

## What Is Already Constructive on Our Side

Current constructive local progress (no axioms added):

1. `d=1, n=3` nontrivial forward-triple branch is fully constructive via
   `D1N3Witnesses.lean` and integrated into
   `deferred_d1_forward_triple_nonempty_nontrivial`.
2. `d=1, n=2` nontrivial left-adj anchor branch is discharged by finite
   permutation-case contradiction in `deferred_d1_leftAdj_anchor_nonempty`.
3. `d=1, n>=4` arithmetic witness infrastructure is extracted and reusable in
   `D1Nge4LinearWitness.lean`.
4. left-adj anchor/triple equivalence bridge is extracted in
   `LeftAdjAnchorBridge.lean`.

So our branch is ahead on explicit small-`n` constructive infrastructure,
while Mike's is ahead on top-level `d>=2` architectural condensation.

## Immediate Integration Recommendation

Do not full-merge Mike's `PermutationFlow`/`OverlapConnected` yet.

Reason:

- it would replace our constructive `d=1` route with a high-level d=1 axiom,
- it creates substantial structural churn without directly closing our current
  local deferred lemmas.

Preferred near-term mode:

- continue constructive work on our branch,
- cherry-pick architecture pieces only when assumptions are discharged or when a
  piece is assumption-free and directly useful.

## Focus Plan: `d=1, n=2,3` (Current Priority)

Goal: completely settle small-`n` d=1 behavior in theorem form, then use the
observed pattern to guide general `n`.

### Priority A: Make the small-`n` closure explicit in code

Add dedicated local theorems documenting what is already proved:

1. `d=1, n=2`: left-adj anchor nonempty nontrivial branch is closed.
2. `d=1, n=3`: forward-triple nonempty nontrivial branch is closed.

This should be exposed in theorem statements (not only as internal case splits)
to reduce ambiguity in future attempts.

### Priority B: Target the small-`n` version of the adjacent-swap open anchor

Main unresolved d=1 analytic lemma is:

- `deferred_d1_adjSwap_forward_open_anchor`.

For `n=2,3`, attack this directly using explicit overlap witnesses and local
EOW-compatible neighborhoods, avoiding midpoint-route assumptions.

### Priority C: Keep `n>=4` isolated

Do not mix `n>=4` geometry while proving small-`n`.
Maintain the current isolation:

- `deferred_d1_forward_triple_nonempty_nge4` remains the only `n>=4` geometric
  deferred in this chain.

## Practical Checkpoint

After each small-`n` milestone, run:

- `lake env lean OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlow.lean`

and update:

- `D1_SCHEME_INPUTS_NOTES.md`
- `PERMUTATION_FLOW_BLOCKER.md`

to keep future agents synchronized.

