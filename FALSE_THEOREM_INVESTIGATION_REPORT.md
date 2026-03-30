# False Theorem Investigation Report

Last updated: 2026-03-30

## Scope

This report tracks the repair of the over-strong OS -> Wightman export surface.
The original false packaging problem had two distinct layers:

1. an upstream `k = 2` VI.1 seam around `exists_probeSeq_euclid_local`
2. a downstream over-packaging seam around `bvt_cluster` / `os_to_wightman_full`

On the current upstream base at `309a2f00cb5d5ec2c14db2ee2d9b1a06d0761ba8`, the
first layer is repaired. The remaining active repair target is the second
layer: the cluster transfer needed for a full `WightmanFunctions` export.

## Current Status

### 1. Upstream route: repaired on the current base

The former probe-root route through `exists_probeSeq_euclid_local` is no longer
the active production path, and its old role as a live blocker has ended.

Current base-state summary:
- the upstream/base repair replaced the unsafe probe-root route with the
  common-witness comparison route
- `exists_probeSeq_euclid_local` is no longer the theorem around which the
  active downstream export story is organized
- `K2VI1/Frontier.lean` now treats the old probe-root lane as obsolete
  archeology rather than current production justification
- downstream repair must therefore not regress this upstream K2 VI.1 fix while
  working on the export layer

Consequence:
- the upstream K2 VI.1 issue is not the present blocker
- the live repair frontier has moved downstream to the cluster-transfer layer

### 2. Downstream route: still intentionally incomplete

The remaining issue is not the existence of the boundary-value package itself.
The remaining issue is the false upgrade from that package to a full
`WightmanFunctions` record.

The key live frontier theorem is:
- `bvt_cluster` in
  `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`

Why this matters:
- `WightmanFunctions` contains clustering as a required field
- any theorem exporting a full `WightmanFunctions` object must therefore prove
  cluster transfer honestly
- the old `os_to_wightman_full` packaging overstated what the present proof
  graph justifies

Current repair decision:
- keep `bvt_cluster` explicit as the remaining frontier theorem
- make the cluster-free boundary-value export the active honest route
- do not claim a full `WightmanFunctions` object until cluster transfer is
  genuinely proved

## Honest Current Export Surface

The current mathematically honest top theorem is:
- `os_to_wightman_boundary_values`

Its output is:
- a cluster-free `BoundaryValueWightmanData` package
- together with `IsWickRotationPair OS.schwinger Wdata.W`

This means the current formalized chain does justify:
- tempered Wightman-side distributions on Schwartz space
- their forward-tube analytic continuation and distributional boundary values
- the transferred normalization, translation invariance, Lorentz covariance,
  local commutativity, positive-definiteness, hermiticity, and
  spectrum-condition package
- the Wick-rotation pairing back to the OS Schwinger family

It does not yet justify:
- the Wightman-side cluster axiom
- a full `WightmanFunctions` export
- any restoration of `os_to_wightman_full` as an honest top theorem

## Gemini Use

Gemini use was successful and materially useful in this repair effort.

Confirmed useful outcomes:
- it helped vet intermediate theorem statements in the Wick-rotation lane before
  they were treated as stable public surfaces
- it helped flag prior over-strong formulations and packaging claims for
  re-checking
- it supported convergence on the current split:
  upstream common-witness repair, downstream explicit cluster frontier

Gemini did not discharge proof obligations. Its successful use was as a
screening and theorem-surface sanity-check aid, not as a replacement for Lean
proofs.

## Files Most Relevant Right Now

- `OSReconstruction/Wightman/Reconstruction/WickRotation/K2VI1/Frontier.lean`
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`
- `OSReconstruction/Wightman/Reconstruction/Main.lean`
- `OSReconstruction/Wightman/Reconstruction/WickRotation.lean`
- `FALSE_THEOREM_INVESTIGATION_REPORT.md`

## Remaining Focus

The active work target is now:

1. keep the upstream common-witness route intact
2. avoid any fake reintroduction of the old probe-root seam
3. continue presenting `os_to_wightman_boundary_values` as the active honest
   export surface
4. prove `bvt_cluster` honestly, or keep it explicitly outside the public export
   surface
5. only restore a full `WightmanFunctions` export once the cluster packaging is
   genuinely complete

## Build Note

On 2026-03-30, targeted rebuild attempts for
`OSReconstruction.Wightman.Reconstruction.Main` and
`OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValues`
both stopped before Lean elaboration because Lake tried to clone the external
dependency `GaussianField` from GitHub and network access is restricted here.

That means:
- the source-level export-surface repair is locally updated
- no new theorem-level elaboration failure appeared in these attempted builds
- complete build verification still depends on the dependency already being
  present in the local Lake cache
