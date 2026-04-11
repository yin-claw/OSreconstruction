# Connected Lorentz/Poincare Migration

## Purpose

This note explains the April 2026 cleanup that changed the default meaning of
`LorentzGroup` and `PoincareGroup` in the Wightman/reconstruction layer.

This is now a **checked-tree navigation note**, not just a naming memo. Its job
is to pin which files own the connected/default covariance surfaces, which files
still expose the explicit full-group variants, and which surviving
`RestrictedLorentzGroup` names are merely local compatibility aliases inside the
independent `ComplexLieGroups` subsystem rather than contradictory public API
surfaces.

The short version is:

- `LorentzGroup d` now means the connected proper-orthochronous Lorentz group
  `SO^+(1,d)`.
- `PoincareGroup d` now means the connected proper-orthochronous Poincare group
  `ISO^+(1,d) = R^(d+1) ⋊ SO^+(1,d)`.
- The full disconnected groups are still present, but under explicit names:
  `FullLorentzGroup d` and `FullPoincareGroup d`.

This matches the standard physics-facing covariance convention used by the
Wightman and Osterwalder-Schrader axioms. Parity and time reversal are not part
of the default covariance group.

## Why this change was needed

Before this migration, the repo used a stronger and less standard default
meaning:

- `LorentzGroup d` meant the full group `O(1,d)`.
- `PoincareGroup d` meant the full semidirect product with `O(1,d)`.
- the physically standard proper-orthochronous subgroup appeared as a
  secondary `Restricted` surface.

That created a mismatch between:

- the mathematical objects used in the Wick-rotation / BHW / forward-tube route,
- the standard Wightman/OS axiom surfaces,
- and the names exposed to collaborators working in the public reconstruction
  API.

The result was repeated translation layers like “restricted covariance,” even in
places where the connected component was already the only physically intended
group.

## New naming convention

### Lorentz side

New default meaning:

- `LorentzGroup d` = connected proper-orthochronous Lorentz group `SO^+(1,d)`

Explicit full group:

- `FullLorentzGroup d` = full Lorentz group `O(1,d)`

Discrete symmetry helpers that remain available:

- `LorentzGroup.parity`
- `LorentzGroup.timeReversal`

These now live as compatibility accessors into the full group, rather than
being bundled into the default covariance group.

### Poincare side

New default meaning:

- `PoincareGroup d` = connected proper-orthochronous Poincare group

Explicit full group:

- `FullPoincareGroup d` = full Poincare group with full Lorentz factor

## Mathematical rationale

The standard scalar QFT covariance convention is:

- Wightman side: proper-orthochronous Poincare covariance
- Euclidean/OS side: Euclidean rotation covariance by `SO`, with reflection
  positivity handling the time-reflection part separately

So the connected component is the right default object for the ordinary axiom
package. Full `O(1,d)` or full `O(d+1)` symmetry is extra structure, not the
default covariance assumption.

This migration does **not** delete the full groups. It just stops treating them
as the default meaning of “Lorentz group” or “Poincare group.”

## Main code changes

### Checked-tree scope of the migration

The migration affects the **Wightman/reconstruction-facing API** first:

- `OSReconstruction/Wightman/Groups/Lorentz.lean`
- `OSReconstruction/Wightman/Groups/Poincare.lean`
- `OSReconstruction/Bridge/AxiomBridge.lean`
- the public Wightman / analytic-continuation / Wick-rotation consumer files
  that now speak directly in terms of `LorentzGroup d` and `PoincareGroup d`
  rather than old restricted-wrapper surfaces.

It does **not** mean that every internal theorem in the repo was globally
rewritten to avoid the word `Restricted`. In the current checked tree the
independent `ComplexLieGroups` development still uses
`RestrictedLorentzGroup` pervasively, but source-checking shows that this is a
local compatibility alias in `OSReconstruction/ComplexLieGroups/LorentzLieGroup.lean`
for the same connected proper-orthochronous object. So when later docs or Lean
work encounter:

- `ComplexLieGroups/LorentzLieGroup.lean :: RestrictedLorentzGroup`
- `ComplexLieGroups/Connectedness/*`
- `ComplexLieGroups/Connectedness/BHWPermutation/*`
- `Wightman/Reconstruction/WickRotation/OSToWightmanEuclideanLorentz.lean`

that should be read as **internal connected-group infrastructure**, not as a
signal that the public Wightman-side migration was incomplete or that full
`O(1,d)` covariance has silently re-entered the default route.

### Foundational group definitions

The key files are:

- [Lorentz.lean](../OSReconstruction/Wightman/Groups/Lorentz.lean)
- [Poincare.lean](../OSReconstruction/Wightman/Groups/Poincare.lean)

The main outcome is:

- `LorentzGroup d` now packages the proper + orthochronous conditions directly
- `PoincareGroup d` now uses that connected Lorentz factor directly
- `FullLorentzGroup d` and `FullPoincareGroup d` preserve the old ambient full
  groups

### Bridge layer

The bridge file is:

- [AxiomBridge.lean](../OSReconstruction/Bridge/AxiomBridge.lean)

The preferred conversion names are now:

- `lorentzGroupToWightman`
- `wightmanToLorentzGroup`

Old restricted-wrapper bridge names were removed from the Wightman side.

### Public analytic / Wick-rotation surfaces

The following public theorem surfaces were normalized from old
`Restricted`-typed statements to bare `LorentzGroup d`:

- [WightmanAxioms.lean](../OSReconstruction/Wightman/WightmanAxioms.lean)
- [AnalyticContinuation.lean](../OSReconstruction/Wightman/Reconstruction/AnalyticContinuation.lean)
- [BHWExtension.lean](../OSReconstruction/Wightman/Reconstruction/WickRotation/BHWExtension.lean)
- [BHWReducedExtension.lean](../OSReconstruction/Wightman/Reconstruction/WickRotation/BHWReducedExtension.lean)
- [ForwardTubeLorentz.lean](../OSReconstruction/Wightman/Reconstruction/WickRotation/ForwardTubeLorentz.lean)
- [OSToWightmanEuclideanLorentz.lean](../OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanEuclideanLorentz.lean)
- [OSToWightmanTubeIdentity.lean](../OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanTubeIdentity.lean)
- [OSToWightmanBoundaryValuesBase.lean](../OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean)
- [OSToWightmanBoundaryValues.lean](../OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean)
- [SchwingerAxioms.lean](../OSReconstruction/Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean)

For later implementation work, the checked-tree ownership split is now:

1. **group-definition owners**
   - `Wightman/Groups/Lorentz.lean`
   - `Wightman/Groups/Poincare.lean`
2. **bridge owner**
   - `Bridge/AxiomBridge.lean`
3. **public consumers**
   - `WightmanAxioms.lean`
   - `Reconstruction/AnalyticContinuation.lean`
   - `WickRotation/BHWExtension.lean`
   - `WickRotation/BHWReducedExtension.lean`
   - `WickRotation/ForwardTubeLorentz.lean`
   - `WickRotation/OSToWightmanEuclideanLorentz.lean`
   - `WickRotation/OSToWightmanTubeIdentity.lean`
   - `WickRotation/OSToWightmanBoundaryValuesBase.lean`
   - `WickRotation/OSToWightmanBoundaryValues.lean`
   - `WickRotation/SchwingerAxioms.lean`

To make this executable rather than just navigational, later Lean work should
follow the theorem-surface queue below instead of jumping between files by
guesswork.

### Public covariance execution queue

1. **Public group surface first**
   - if the missing object is the connected default Lorentz/Poincaré group
     itself, start in `Wightman/Groups/Lorentz.lean` or
     `Wightman/Groups/Poincare.lean`;
   - do **not** start from `ComplexLieGroups/*` unless the task is genuinely an
     internal connectedness/path-component proof.
2. **Only then cross the public bridge**
   - if the consumer theorem needs the internal/external conversion, use the
     checked bridge surfaces in `Bridge/AxiomBridge.lean`:
     `lorentzGroupToWightman` and `wightmanToLorentzGroup`;
   - the bridge is the only endorsed place where later Lean work should change
     representation of the public connected covariance group.
3. **Then enter the specific public consumer lane**
   - `ForwardTubeLorentz.lean`: forward-tube Lorentz covariance / boundary-value
     transport, e.g. `lorentz_covariant_distributional_bv`;
   - `BHWExtension.lean`: raw BHW-extension covariance consumers below the OS→W
     boundary-value wrappers;
   - `OSToWightmanBoundaryValues.lean`: final public OS→W covariance wrappers,
     with the checked local queue
     `bvt_lorentz_covariant_restricted -> bvt_lorentz_covariant ->
     constructWightmanFunctions`;
   - `SchwingerAxioms.lean`: reverse E1 packaging, with the checked split queue
     `F_ext_translation_invariant ->
      wickRotatedBoundaryPairing_translation_invariant`
     and
     `F_ext_rotation_invariant ->
      wickRotatedBoundaryPairing_rotation_invariant`,
     after which any full `OsterwalderSchraderAxioms` wrapper may only package
     those separate fields rather than reopening the Wightman-side covariance
     migration.

So later Lean work should not reopen the migration at random consumer sites.
If a covariance-type mismatch appears, first decide whether it belongs in the
public Wightman group-definition layer, in `AxiomBridge.lean`, or only inside a
local `ComplexLieGroups` compatibility proof.

This is the main user-facing effect of the migration.

## What was removed

On the Wightman/Poincare side, the following compatibility surfaces are now
gone:

- `LorentzGroup.Restricted`
- `PoincareGroup.IsRestricted`
- `PoincareGroup.Restricted`
- `restrictedLorentzGroupToWightman`
- `wightmanToRestrictedLorentzGroup`

If you still have local code using those names, the fix is not to recreate the
old wrappers. The fix is to use the connected default objects directly.

## What remains

This migration did **not** try to rename every historical occurrence of the word
“restricted” across the entire repository.

In particular, the independent `ComplexLieGroups` subsystem still contains the
name:

- `LorentzLieGroup.RestrictedLorentzGroup`

But in that subsystem it is only a local alias. The actual default connected
object there is already:

- `LorentzLieGroup.LorentzGroup`

So this remaining name is not a mathematical mismatch in the production
Wightman/reconstruction API. It is just older local terminology inside that
independent copy of the connected-complex-Lorentz infrastructure.

The practical documentation rule is therefore stricter than before:

- if a doc is describing the **public Wightman/reconstruction API**, it should
  speak in terms of `LorentzGroup d` / `PoincareGroup d` and explicit
  `FullLorentzGroup d` / `FullPoincareGroup d` when needed;
- if a doc is describing the **internal ComplexLieGroups/BHW connectedness
  machinery**, it may still mention `RestrictedLorentzGroup`, but it must say
  clearly that this is the checked local alias for the connected component, not
  a different covariance convention;
- docs must not present those internal alias uses as evidence that the repo
  still has two competing default Lorentz-group meanings.

## Collaborator guidance

If you are touching Wightman/reconstruction code, use this rule:

- use `LorentzGroup d` when you mean the ordinary physical covariance group
- use `PoincareGroup d` when you mean the ordinary physical Poincare symmetry
- use `FullLorentzGroup d` or `FullPoincareGroup d` only when you genuinely
  need parity, time reversal, or another disconnected-component argument

If you see old local notes or comments talking about “restricted Lorentz” on the
Wightman side, interpret them as historical language for what is now just the
default `LorentzGroup`.

For file navigation, use the following decision tree before editing theorem
surfaces:

1. **Need the actual group definition or the full-group variant?**
   Start in `Wightman/Groups/Lorentz.lean` or `Wightman/Groups/Poincare.lean`.
2. **Need the API bridge between Wightman-side and internal group packaging?**
   Start in `Bridge/AxiomBridge.lean`.
3. **Need a public covariance consumer on the OS/BHW/Wick-rotation route?**
   Start in the consuming theorem file (`AnalyticContinuation.lean`,
   `BHWExtension.lean`, `BHWReducedExtension.lean`,
   `ForwardTubeLorentz.lean`, `OSToWightmanEuclideanLorentz.lean`,
   `OSToWightmanTubeIdentity.lean`, `OSToWightmanBoundaryValuesBase.lean`,
   `OSToWightmanBoundaryValues.lean`, or `SchwingerAxioms.lean`).
4. **Need a connectedness/path-component proof inside ComplexLieGroups?**
   It is normal to land in local `RestrictedLorentzGroup` code there; do not
   "fix" those names unless the task is explicitly to clean that subsystem.

## Verification

The migration was verified with exact Lean builds on the final local state:

- `lake build OSReconstruction.Bridge.AxiomBridge` -> `0`
- `lake build OSReconstruction.Wightman` -> `0`

Those checks were run after the final removal of the dead Wightman-side
compatibility wrappers.

## Bottom line

This migration is a semantic cleanup, not a new physics theorem.

It makes the repo’s default group names match the standard mathematical meaning
used by the Wightman and OS axioms:

- connected proper-orthochronous group as the default
- full disconnected group available only under explicit `Full...` names

That is the intended convention going forward.
