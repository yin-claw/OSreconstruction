# Connectivity + EOW Insight (Blocker Decomposition)

This note records the precise mathematical point from our discussion and how it
maps to the current `PermutationFlow` blocker.

## 1. What is assumed about `F` at the start

In the BHW theorem setup, `F` is assumed to satisfy:

1. Holomorphicity on the forward tube:
   `DifferentiableOn ℂ F (ForwardTube d n)`.
2. Boundary-value regularity at real points:
   `hF_bv : ContinuousWithinAt F (ForwardTube d n) (x as complex)`.
3. Local commutativity on real spacelike configurations:
   `hF_local` gives swap-equality at such real points.

Important: we do **not** assume `F` is holomorphic across the real boundary a
priori.

## 2. Why connectedness alone is not enough

To prove

`extendF F (σ·z) = extendF F z`

on a connected domain `D`, define

`g(z) := extendF F (σ·z) - extendF F z`.

Connectedness alone does not force `g = 0`. We also need an interior anchor
where `g` vanishes (open set or at least uniqueness-valid set with accumulation
inside the holomorphic domain).

## 3. Why boundary equality still helps: EOW is the bridge

Boundary swap equality on real spacelike points is not by itself an interior
zero set. The role of EOW is exactly to convert that boundary trace agreement
into holomorphic gluing across the edge, yielding interior equality on an open
complex neighborhood.

Then identity theorem propagates from that interior anchor across connected
domain `D`.

So the full mechanism is:

1. boundary equality (`hF_bv` + `hF_local`),
2. EOW/gluing to interior anchor,
3. connectedness of target overlap domain,
4. identity theorem propagation.

## 4. Explicit `d = 1, n = 2` picture

Write each point as `(z_1, z_2)` with `z_i = (z_i^0, z_i^1) ∈ ℂ^2`.

Forward tube condition is:

`Im(z_2^0 - z_1^0) > |Im(z_2^1 - z_1^1)|`.

For swap `σ(1)=2, σ(2)=1`, the overlap domain is

`D_σ = { z ∈ ET | σ·z ∈ ET }`.

The difficult part in `d = 1` is that the real-anchor route used in higher
dimension is not uniformly available; this is why a separate complex-anchor
argument is needed in that branch.

## 5. Where this appears in code

Core analytic propagation templates already exist:

- `eow_adj_swap_on_overlap`:
  `Adjacency.lean:193`
- `extendF_perm_eq_on_connectedDomain_of_realOpen`:
  `Adjacency.lean:406`
- `extendF_adjSwap_eq_of_connected_overlap`:
  `Adjacency.lean:1254`

Open-anchor variants also exist:

- `extendF_perm_overlap_of_open_anchor_and_forwardOverlapConnected`:
  `OverlapAnchor.lean:115`
- `forward_base_eq_of_open_anchor`:
  `OverlapAnchor.lean:212`
- `extendF_perm_overlap_of_forward_open_anchor`:
  `OverlapAnchor.lean:270`

## 6. Current blocker decomposition in `PermutationFlow`

The single blocker inside `iterated_eow_permutation_extension` has been split
into deferred geometric lemmas:

- `deferred_isConnected_permOrbitSeedSet_dge2`
  (`PermutationFlow.lean:2260`)
- `deferred_isConnected_permOrbitSeedSet_d1`
  (`PermutationFlow.lean:2266`)
- `deferred_extendF_perm_overlap_d1_of_seedConnected`
  (`PermutationFlow.lean:2274`)

The nontrivial branch now dispatches as:

1. `d ≥ 2`:
   use `extendF_perm_overlap_dge2_of_seedConnected` with deferred seed
   connectedness.
2. `d = 1`:
   use deferred `d=1` connectivity-to-overlap bridge.

See the branch at:

- `PermutationFlow.lean:2350` (construction of `hExtPerm`)
- `PermutationFlow.lean:2376` (`d ≥ 2` dispatch)
- `PermutationFlow.lean:2383` (`d = 1` dispatch)

## 7. Practical takeaway

The analytic continuation logic is not the blocker anymore. The remaining work
is geometric:

1. prove the deferred connectedness input(s), and
2. complete the dedicated `d=1` connectivity-to-overlap bridge (likely via a
   complex anchor/open-anchor route rather than real Jost anchors).
