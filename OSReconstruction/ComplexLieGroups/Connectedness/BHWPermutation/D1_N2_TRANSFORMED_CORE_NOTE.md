# d=1, n=2 Transformed-Core Note

Last updated: 2026-03-02

## Active local blocker

In `PermutationFlowBlockers.lean`, the remaining n=2 local analytic blocker is:

- `blocker_eventuallyEq_on_adjSwapExtendedOverlap_nhds_at_transformed_anchor_d1_swap01_n2_deferred`

(path line ~344 in current file).

## Equivalent local formulations (proved)

For fixed prepared data `(z0, Gamma, U, hU_good)`:

1. Prepared-neighborhood deterministic base form:

- `eventually z near z0, z in U -> extendF(swap z) = F z`.

2. Transformed-anchor ET-overlap local form:

- `eventually y near Gamma·(swap z0), y in D -> extendF(swap y) = extendF y`,
  where `D = ET ∩ swap^{-1}(ET)`.

The equivalence is now explicit in code:

- forward direction (transformed -> base):
  `blocker_eventuallyExtendFBaseEq_on_prepared_nhds_at_anchor_adjSwap_d1_swap01_n2_reduce`
- reverse direction (base -> transformed):
  `blocker_eventuallyEq_on_adjSwapExtendedOverlap_nhds_at_transformed_anchor_d1_swap01_n2_of_base`
- packaged iff:
  `blocker_eventuallyExtendFBaseEq_iff_eventuallyEq_at_transformed_anchor_adjSwap_d1_swap01_n2`

Therefore the n=2 local blocker is mathematically concentrated in one statement,
not spread across multiple wrappers.

## Geometric hard constraints already proved

Two n=2 obstruction lemmas are available in `D1N2Invariants.lean`:

- `no_common_forwardizer_d1_swap01_n2`
- `prepared_unswapped_not_forward_d1_swap01_n2`

Consequence:

- any route requiring one fixed witness `Gamma` to send both `w` and `swap w`
  to `FT` (pointwise or eventually) is invalid in `d=1,n=2`.

This blocks the naive local route through eventual unswapped-forwardization.

## Practical implication for next proof attempts

To close the deferred transformed core, one must use a route that does not rely
on eventual `Gamma·w in FT` on prepared neighborhoods.

The remaining route should instead work directly on ET-overlap local equality,
using only currently allowed hypotheses (`hF_holo`, `hF_lorentz`, `hF_bv`,
`hF_local`) plus existing EOW/identity infrastructure.
