# SCV TODO: OS-Critical Analytic Continuation Chain

Last updated: 2026-03-07

This TODO tracks the remaining `SCV` blockers on the OS reconstruction path.

Count convention in this file: direct tactic holes only,
`rg -n '^[[:space:]]*sorry([[:space:]]|$)' OSReconstruction/SCV --glob '*.lean'`.

## Live Sorry Census

| Scope | Direct `sorry` lines |
|---|---:|
| `OSReconstruction/SCV` | 0 |

Breakdown:
- `SCV/BochnerTubeTheorem.lean`: 0
- `SCV/PaleyWiener.lean`: 0
- `SCV/LaplaceSchwartz.lean`: 0
- `SCV/TubeDistributions.lean`: 0

## Session Summary

- The fake multidimensional support scaffolding was removed from `PaleyWiener.lean`.
- `LaplaceSchwartz.lean` now has the correct weak/regular split:
  - `HasFourierLaplaceRepr`
  - `HasFourierLaplaceReprRegular`
- `TubeDistributions.lean` now keeps only the proved regular variants; the unused weak
  placeholder fronts were removed.
- The fake weak-to-regular upgrade theorem and the unused weak theorem fronts are gone.

## Load-Bearing Items

### `SCV/LaplaceSchwartz.lean` (0)

Meaning:
- the weak/regular split is now honest
- no fake upgrade theorem from weak BV data remains

### `SCV/TubeDistributions.lean` (0)

Meaning:
- only the rigorous regular variants remain
- the unused weak placeholder fronts were removed instead of being carried as public `sorry`s

### `SCV/BochnerTubeTheorem.lean` (0)

Status:
- the unused Bochner theorem surface has been removed
- the file now contains only sorry-free convex-hull/tube-domain helpers and the compatible-family gluing theorem

### `SCV/PaleyWiener.lean` (0)

Status:
- sorry-free
- `paley_wiener_half_line` and the slice-wise `paley_wiener_one_step` are proved
- no fake multidimensional Fourier-support notion remains in the public API

## Execution Order

1. `SCV` is currently sorry-free.
2. If the measure-construction / stronger Fourier-Laplace lane is revived later,
   reintroduce it with a genuine proof rather than a wrapper interface.

## Stable Completed Core

- `Polydisc.lean`
- `IteratedCauchyIntegral.lean`
- `Osgood.lean`
- `Analyticity.lean`
- `TubeDomainExtension.lean`
- `IdentityTheorem.lean`
- `FourierLaplaceCore.lean`
- `PaleyWiener.lean`

`edge_of_the_wedge_theorem` is proved and axiom-free.
