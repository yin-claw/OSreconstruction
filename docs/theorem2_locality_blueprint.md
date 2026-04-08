# Theorem 2 Locality Blueprint

Purpose: this note is the theorem-specific implementation blueprint for the
live `E -> R` locality frontier

- `OSToWightmanBoundaryValues.lean`, private theorem
  `bvt_F_swapCanonical_pairing`.

This is the current theorem-2 `main` route. It supersedes older gap notes that
were written before `edge_of_the_wedge` was proved as a theorem.

This note should be read together with:
- `docs/os1_detailed_proof_audit.md`, Section 9,
- `docs/theorem3_os_route_blueprint.md` only for route discipline,
- `docs/edge_of_the_wedge_proof_plan.md` and
  `docs/edge_of_the_wedge_gap_analysis.md` only as historical reference.

### 0.1. Checked production file inventory for theorem 2

This blueprint now records the exact repo-relative production paths that were
checked against the current tree, because theorem-2 work spans Wick-rotation,
BHW, SCV, and CLG files and shortened filenames easily blur the implementation
locus.

A second contract is now explicit too: this blueprint distinguishes
**checked-present production theorem surfaces** from **planned theorem-package
names introduced only by this doc**. Later Lean work should not waste time
searching for the planned package names as if they were already available
helpers in the current tree.

Checked-present theorem-2 production files:

- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean`
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesComparison.lean`
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean`
- `OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean`
- `OSReconstruction/Wightman/Reconstruction/WickRotation/BHWExtension.lean`
- `OSReconstruction/Wightman/Reconstruction/AnalyticContinuation.lean`
- `OSReconstruction/ComplexLieGroups/JostPoints.lean`
- `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation.lean`
- `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/Adjacency.lean`
- `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/AdjacencyDistributional.lean`

Checked-tree path correction:

Earlier drafts of this blueprint sometimes shortened these to paths like
`OSReconstruction/Wightman/Reconstruction/OSToWightmanBoundaryValueLimits.lean`
or `OSReconstruction/WickRotation/BHWPermutation/Adjacency.lean`. Those paths
are **not** the checked tree in this clone. The exact repo-relative paths above
are the ones later Lean work should open.

Checked-present theorem surfaces already in the current tree:

- `Wightman/Reconstruction/WickRotation/BHWExtension.lean ::
  W_analytic_swap_boundary_pairing_eq`
- `ComplexLieGroups/Connectedness/BHWPermutation/AdjacencyDistributional.lean ::
  extendF_adjSwap_pairing_eq_of_distributional_local_commutativity`
- `ComplexLieGroups/Connectedness/BHWPermutation/Adjacency.lean ::
  exists_real_open_nhds_adjSwap`
- `ComplexLieGroups/Connectedness/BHWPermutation/Adjacency.lean ::
  extendF_adjSwap_eq_on_realOpen`
- `ComplexLieGroups/Connectedness/BHWPermutation/AdjacencyDistributional.lean ::
  extendF_adjSwap_eq_on_realOpen_of_distributional_local_commutativity`
- `Wightman/Reconstruction/WickRotation/BHWExtension.lean ::
  analytic_boundary_local_commutativity_of_boundary_continuous`
- `Wightman/Reconstruction/ForwardTubeDistributions.lean ::
  boundary_function_continuous_forwardTube_of_flatRegular`
- `Wightman/Reconstruction/ForwardTubeDistributions.lean ::
  boundary_value_recovery_forwardTube_of_flatRegular`
- `Wightman/Reconstruction/ForwardTubeDistributions.lean ::
  boundary_value_recovery_forwardTube_of_flatRegular_from_bv`
- `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesComparison.lean ::
  bv_local_commutativity_transfer_of_swap_pairing`

Checked-missing planned theorem-package names introduced by this blueprint:

- `choose_real_open_edge_for_adjacent_swap`
- `swapped_support_lies_in_swapped_open_edge`
- `swapped_open_edge_embeds_in_extendedTube`
- `flatRegular_of_boundary_distribution_and_polyGrowth`
- `bvt_F_hasFlatRegularRepr`
- `bvt_F_boundary_continuous_at_real_support`
- `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`
- `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery`
- `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`
- `bvt_F_swapCanonical_pairing_of_adjacent_chain`

Checked-missing *pseudocode-only* helper names appearing later in this blueprint:

- `adjacentSwapFactorization`
- `AdjacentCanonicalSwapPairingStepHolds`

These two names are **not** currently checked-present repo objects and are also
**not** contract-level theorem-slot names. They are schematic placeholders for
whatever finite adjacent-transposition factorization data and per-step predicate
Lean eventually uses inside the proof of
`bvt_F_swapCanonical_pairing_of_adjacent_chain`. The contract-level obligation
is only that a separate general-swap reduction theorem exists and visibly
factors the general `swap i j` frontier through adjacent canonical steps; later
implementation work must not waste time searching the current tree for these
exact helper names or treat them as frozen theorem surfaces.

Important checked-tree clarification:

1. `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation.lean` is the
   umbrella/barrel for the permutation-connectedness lane.
2. The checked adjacent-swap support stack already has a two-subfile split:
   `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/Adjacency.lean`
   for the pointwise/open-edge adjacent-swap route and
   `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/AdjacencyDistributional.lean`
   for the distributional pairing route.
3. The actual theorem-2 Route-B ET-support consumer theorem
   `extendF_adjSwap_pairing_eq_of_distributional_local_commutativity` lives in
   the checked distributional subfile
   `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/AdjacencyDistributional.lean`.
4. So theorem-2 geometry work should be attached to that checked adjacent-swap
   support layer — `AdjacencyDistributional.lean` when it feeds the
   distributional pairing theorem surface directly, or `Adjacency.lean` for a
   lower pointwise/open-edge supplier that closes back onto the same checked
   distributional theorem surface — not dumped into the umbrella
   `BHWPermutation.lean` just because that shorter path is easier to notice in
   the tree.

Implementation rule for this blueprint:

0. the checked-present theorem surfaces listed above are the actual current
   repo hooks the theorem-2 closure must consume;
0a. the checked-missing theorem-package names listed above are documentation
   contract names only; unless and until they are implemented, they should be
   treated as the missing theorem packages rather than searched for under the
   assumption that they already exist somewhere in the tree;

1. theorem-2 production work lands in
   `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`
   unless this document is rewritten first;
2. geometry suppliers belong in the checked BHW / Jost / adjacency-support
   files above, not in ad hoc new locality wrappers under unrelated filenames;
3. the canonical-shift closure layer lives in the checked
   `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean`
   support file and the flattened-continuity supplier lives in the checked
   `OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean`
   support file; theorem-2 documentation must keep those two support loci
   distinct from the frontier theorem file itself;
4. file ownership of the still-missing theorem packages is part of the route
   contract:
   - Route-B open-edge / ET-support theorems such as
     `choose_real_open_edge_for_adjacent_swap`,
     `swapped_support_lies_in_swapped_open_edge`, and
     `swapped_open_edge_embeds_in_extendedTube` belong on the checked
     adjacent-swap support layer, with the default split now explicit:
     pointwise/open-edge suppliers may live in `Adjacency.lean`, while any
     theorem packaged specifically to feed the checked distributional pairing
     surface should live in `AdjacencyDistributional.lean`; in either case,
     the package must close back onto
     `extendF_adjSwap_pairing_eq_of_distributional_local_commutativity` rather
     than creating a competing theorem-2 endgame under the umbrella barrel.
     More sharply, the checked tree already fixes the **lower** Route-B local
     transcript in `Adjacency.lean`: `exists_real_open_nhds_adjSwap` is the
     existing compactness/open-neighborhood package that builds an open real
     edge carrying (i) adjacent spacelike persistence, (ii) ET membership of
     the edge itself, and (iii) ET membership of the swapped edge. So later
     Lean work should not rediscover the local cover argument from scratch
     inside theorem 2. The documentation-level top package
     `choose_real_open_edge_for_adjacent_swap` should be implemented as the
     theorem-2-facing wrapper that consumes that checked helper plus support
     inclusion for `tsupport f`; the compactness/open-neighborhood proof is
     already assigned to `Adjacency.lean`.
   - `BHWPermutation.lean` itself should be treated only as the umbrella entry
     point for that CLG lane unless a later doc pass explicitly rewrites the
     file-locus contract;
   - the raw-boundary wrapper theorem
     `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` belongs on the
     `BHWExtension.lean` / Wick-rotation boundary-pairing side, because it is
     an instantiation layer for `W_analytic_swap_boundary_pairing_eq` rather
     than a new CLG geometry theorem;
   - the theorem-2-specific canonical pairing recovery specialization
     `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` belongs in
     `OSToWightmanBoundaryValueLimits.lean`, because it is the explicit
     specialization of the checked recovery theorem to the theorem-2 boundary
     functional package;
   - the final adjacent canonical-shift gluing theorem
     `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality` also
     belongs in `OSToWightmanBoundaryValueLimits.lean`, because it combines
     that specialization with the adjacent raw-boundary equality below the
     frontier theorem;
   - the general-swap adjacent-chain reducer
     `bvt_F_swapCanonical_pairing_of_adjacent_chain` also belongs in
     `OSToWightmanBoundaryValueLimits.lean`, because it still lives entirely on
     the canonical-shift side of theorem 2: it composes adjacent canonical
     equalities into the general `swap i j` canonical pairing statement, but
     it does not add new BHW geometry or new frontier-consumer logic;
   - checked-file caution: `OSToWightmanBoundaryValueLimits.lean` is a real
     checked production file, but the current tree still uses it only for the
     theorem-3 / positivity-side `singleSplit_xiShift` limit machinery. No
     theorem-2-specific subsection for
     `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery`,
     `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`, or
     `bvt_F_swapCanonical_pairing_of_adjacent_chain` exists there yet. So the
     theorem-2 package assigned to that file is **planned support work in an
     existing file**, and it must be added as a separate canonical-direction
     subsection over `canonicalForwardConeDirection`, not by overloading or
     reinterpreting the existing `singleSplit_xiShift` shell as if it already
     supplied theorem-2 raw-boundary-to-canonical recovery;
   - the frontier theorem `bvt_F_swapCanonical_pairing` in
     `OSToWightmanBoundaryValues.lean` should stay a thin consumer of those
     named packages rather than absorbing any of them;
5. short names like `BHWExtension.lean`, `BoundaryValuesComparison.lean`, or
   `BoundaryValueLimits.lean` are allowed below only as shorthand for the
   exact checked paths above.

### 0.2. Route-contract ledger for the still-missing theorem-2 package

The current blueprint had the right theorem-slot names but still left one
implementation ambiguity: later Lean work had to reconstruct for itself which
slot consumes which exact checked surface, and which later slot is allowed to
consume the result. The ledger below is now part of the theorem-2 contract.
It is the shortest allowed execution transcript for the live Route-B theorem-2
lane.

| Slot | File ownership | Must consume exactly | Must prove / export exactly | Next allowed consumer |
| --- | --- | --- | --- | --- |
| `choose_real_open_edge_for_adjacent_swap` | `ComplexLieGroups/Connectedness/BHWPermutation/Adjacency.lean` (or theorem-2-facing wrapper beside that checked helper layer) | checked `exists_real_open_nhds_adjSwap` plus theorem-2 support inclusion for `tsupport f` | one theorem-2-facing open real edge `V` with adjacent-swap compatibility on `V`, `tsupport f ⊆ V`, and the swapped edge data needed downstream | `swapped_support_lies_in_swapped_open_edge`, `swapped_open_edge_embeds_in_extendedTube` |
| `swapped_support_lies_in_swapped_open_edge` | same Route-B geometry layer as above | output of `choose_real_open_edge_for_adjacent_swap` plus the checked swap identity on real points | support transport only: the swapped test-function support lies in the swapped real open edge | `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` |
| `swapped_open_edge_embeds_in_extendedTube` | same Route-B geometry layer as above | output of `choose_real_open_edge_for_adjacent_swap` | ET transport only: both the chosen edge and its swapped image lie in the required extended-tube domain | `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`, `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` |
| `bvt_F_hasFlatRegularRepr` | `Wightman/Reconstruction/ForwardTubeDistributions.lean` | checked unflattened suppliers `bvt_F_holomorphic`, `bvt_boundary_values`, and the explicit growth field extracted from `full_analytic_continuation_boundaryValueData` / `full_analytic_continuation_with_symmetry_growth` | a theorem-2-specific flat-regular witness package for `bvt_F` | `bvt_F_boundary_continuous_at_real_support`, `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` |
| `bvt_F_boundary_continuous_at_real_support` | `Wightman/Reconstruction/ForwardTubeDistributions.lean` | `bvt_F_hasFlatRegularRepr` plus checked `boundary_function_continuous_forwardTube_of_flatRegular` | boundary continuity of `bvt_F` on the real support/edge data used by theorem 2 | `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` |
| `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` | statement home `Wightman/Reconstruction/WickRotation/BHWExtension.lean`; lower helper lemmas in `ComplexLieGroups/Connectedness/BHWPermutation/AdjacencyDistributional.lean` | Route-B open-edge package (`choose_real_open_edge_for_adjacent_swap`, `swapped_support_lies_in_swapped_open_edge`, `swapped_open_edge_embeds_in_extendedTube`) plus `bvt_F_boundary_continuous_at_real_support` and checked `analytic_boundary_local_commutativity_of_boundary_continuous` | the actual adjacent-only non-circular raw-boundary pairing equality for theorem 2 | `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` |
| `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` | `Wightman/Reconstruction/WickRotation/BHWExtension.lean` / theorem-2 boundary-pairing layer | `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` plus the checked ET-support wrapper format expected by the Wick-rotation boundary side | theorem-2-facing adjacent raw-boundary equality in the exported boundary-pairing format | `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality` |
| `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean` | `bvt_F_hasFlatRegularRepr` plus checked `boundary_value_recovery_forwardTube_of_flatRegular_from_bv`, instantiated with checked `bvt_W`, `bvt_W_continuous`, `bvt_boundary_values`, and `canonicalForwardConeDirection` | the theorem-2-specific canonical-direction pairing recovery equality | `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality` |
| `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality` | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean` | `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` plus two uses of `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` | adjacent canonical pairing equality for one adjacent transposition | `bvt_F_swapCanonical_pairing_of_adjacent_chain` |
| `bvt_F_swapCanonical_pairing_of_adjacent_chain` | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean` | explicit adjacent-transposition factorization data for `swap i j` plus repeated `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality` | general `swap i j` canonical pairing equality, still below the frontier file | `bvt_F_swapCanonical_pairing` |
| `bvt_F_swapCanonical_pairing` | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean` | checked `bv_local_commutativity_transfer_of_swap_pairing` plus `bvt_F_swapCanonical_pairing_of_adjacent_chain` | the final theorem-2 frontier statement consumed by the transfer layer | downstream transfer / public locality consumers only |

Two negative ownership rules are now explicit in the ledger too:

1. no slot above `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`
   is allowed to consume global `IsLocallyCommutativeWeak d (bvt_W OS lgc)`;
2. nothing in `OSToWightmanBoundaryValueLimits.lean` is allowed to reopen the
   raw-boundary closure theorem after the `BHWExtension.lean` seam has closed
   it.

## 1. The live theorem and its consumers

The live frontier theorem is:

```lean
private theorem bvt_F_swapCanonical_pairing
```

in `OSToWightmanBoundaryValues.lean`.

Its immediate consumers are:

1. `bv_local_commutativity_transfer_of_swap_pairing`
   in `OSToWightmanBoundaryValuesComparison.lean`,
2. `bvt_locally_commutative`
   in `OSToWightmanBoundaryValues.lean`,
3. the public Wightman axiom field `locally_commutative` in
   `os_to_wightman_full`.

So theorem 2 is the unique boundary-value bridge from the analytic permutation
package to the public locality axiom.

## 2. OS-paper reading of theorem 2

OS I Section 4.5 proves locality by:

1. Euclidean symmetry on the real side,
2. analytic continuation to overlapping permuted tube domains,
3. a uniqueness / edge-of-the-wedge step,
4. passage to boundary values.

This means theorem 2 belongs to the BHW / PET / Jost / edge-of-the-wedge lane.
It is not part of the theorem-3 positivity / semigroup lane.

### 2.1. OS I error / OS II correction note

The standard OS caution still matters here, but in a specific way.

1. OS I Lemma 8.8 is the broken step: it tried to pass from separate
   one-variable continuation to a joint many-variable Fourier-Laplace
   statement.
2. Theorem 2 should **not** use that step or any theorem surface that quietly
   presupposes it.
3. Theorem 2 itself is not the positivity/semigroup repair lane. Its analytic
   input is the already-built many-variable continuation object `bvt_F`, plus
   the BHW / edge-of-the-wedge / boundary-value uniqueness package.
4. So the local discipline is:
   - use OS I only for the conceptual locality pattern
     (symmetry -> common analytic continuation -> uniqueness -> boundary
     values),
   - use the already-repaired production continuation object rather than any
     direct appeal to the broken OS I many-variable argument.

In short: theorem 2 is allowed to consume the repaired many-variable analytic
object, but it must not pretend to prove locality by reviving the original OS I
Lemma-8.8 route.

## 3. Exact production hooks already available

The current code already contains the major analytic ingredients.

Checked-present versus planned-package rule for this section:

1. theorem names listed here as already present are actual checked repo
   surfaces;
2. later names introduced below in theorem-slot inventories are planned package
   names, not currently existing helpers, unless this blueprint says
   otherwise explicitly.

In `OSToWightmanBoundaryValuesBase.lean`:

1. `bvt_F_perm`
   gives permutation invariance of the analytic boundary-value continuation
   `bvt_F`.

In `BHWExtension.lean`:

1. `W_analytic_swap_boundary_pairing_eq`
   gives adjacent-swap equality of boundary pairings for compactly supported
   tests whose real support already lies in the extended tube.
2. `analytic_extended_local_commutativity`
   gives pointwise adjacent-swap equality on real ET overlap points for the BHW
   extension.
3. `analytic_boundary_local_commutativity_of_boundary_continuous`
   descends that pointwise equality from `BHW.extendF W_analytic` to raw
   boundary values of `W_analytic`, provided the needed boundary continuity is
   available at the two real ET points.
4. `W_analytic_BHW`
   packages the BHW extension used by the reverse-direction side and by any
   later uniqueness comparison.

In `AnalyticContinuation.lean` and `SCV/TubeDomainExtension.lean`:

1. `edge_of_the_wedge`
   is a proved theorem, not an axiom.
2. `SCV.edge_of_the_wedge_theorem`
   is the underlying multi-dimensional theorem.
3. `jost_lemma`
   packages the real-point spacelike geometry on the extended tube.

In `OSToWightmanBoundaryValuesComparison.lean`:

1. `bv_local_commutativity_transfer_of_swap_pairing`
   is already the public transfer theorem from the canonical BV swap pairing to
   locality of the reconstructed Wightman distribution.

So theorem 2 does not lack edge-of-the-wedge infrastructure any more. The live
gap is the last boundary-pairing adapter that feeds the existing transfer
theorem.

## 4. Honest remaining gap

The current frontier theorem asks directly for equality of the two canonical BV
pairings

```lean
∫ bvt_F(... canonical shift ...) * g
=
∫ bvt_F(... canonical shift ...) * f
```

under:

1. adjacent spacelike separation on the support of `f`,
2. `g = f ∘ swap(i,j)`.

The BHW package already proves the analogous adjacent-swap statement in a
fixed order, but the theorem-surface story is sharper than older drafts
claimed.

The checked theorem `W_analytic_swap_boundary_pairing_eq` already packages the
final raw-boundary pairing equality on the real trace, and it already sits on
top of the ET-support distributional theorem
`extendF_adjSwap_pairing_eq_of_distributional_local_commutativity`.
However, its checked theorem surface also asks for an input
`hLC : IsLocallyCommutativeWeak d W` for the boundary functional `W`.
That is fine when this BHW theorem is used downstream on a Wightman package
whose locality is already known, but it is a real theorem-2 surface issue if
one tries to instantiate it naively with `W := bvt_W OS lgc`: theorem 2 is
precisely the step that is supposed to prove local commutativity of `bvt_W`, so
feeding `bvt_locally_commutative` back into that theorem would be circular.

So the current theorem-2 production route must distinguish **three** layers,
not two:

1. the checked ET-support / distributional pairing consumer theorem
   `extendF_adjSwap_pairing_eq_of_distributional_local_commutativity` in
   `AdjacencyDistributional.lean`;
2. the checked public wrapper
   `W_analytic_swap_boundary_pairing_eq`, which repackages that same theorem
   surface on the BHW-extension side;
3. the still-missing theorem-2-specific **non-circular supplier** for the input
   `IsLocallyCommutativeWeak d (bvt_W OS lgc)` that both checked theorems still
   demand.

That third layer is the important correction. A direct source check shows that
`extendF_adjSwap_pairing_eq_of_distributional_local_commutativity` itself still
has an explicit hypothesis
`hF_local_dist : IsLocallyCommutativeWeak d W`.
So it is lower than `W_analytic_swap_boundary_pairing_eq` with respect to the
ET-support geometry packaging, but it is **not by itself** the missing
non-circular theorem-2 closure theorem.

A second theorem-surface correction is now explicit too: the old doc slot name
`bvt_W_adjacent_distributional_local_commutativity_input` was narrower in name
than in statement. If that slot is written as a full theorem
`IsLocallyCommutativeWeak d (bvt_W OS lgc)`, then theorem 2 is being asked to
prove a much stronger global surface than its actual adjacent-step frontier
needs.

After checking the surrounding live theorem surfaces, this blueprint now fixes
one unique closure choice:

1. theorem 2 does **not** endorse a preliminary full theorem
   `IsLocallyCommutativeWeak d (bvt_W OS lgc)` as part of its main route;
2. instead, theorem 2 must introduce a **new adjacent-only substitute consumer
   theorem** on the `AdjacencyDistributional.lean` / `BHWExtension.lean` seam;
3. the documentation now freezes the contract-level name and locus of that
   substitute consumer theorem:
   `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`, with the
   implementation home in
   `OSReconstruction/Wightman/Reconstruction/WickRotation/BHWExtension.lean`
   and any lower distributional helper lemmas it needs living in
   `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/AdjacencyDistributional.lean`;
4. that substitute consumer theorem should package only the fixed adjacent
   `(n,i,i+1,f,g)` raw-boundary pairing equality needed by theorem 2, using the
   already-assembled ET-support, swap, and boundary-continuity inputs, without
   changing theorem 2 into a global Wightman-locality theorem upstream of its
   own frontier.

Why this choice is now frozen:

1. the checked public wrapper `W_analytic_swap_boundary_pairing_eq` is already
   adjacent-only in its geometric data but still asks for the full global input
   `hLC : IsLocallyCommutativeWeak d W`;
2. the lower theorem
   `extendF_adjSwap_pairing_eq_of_distributional_local_commutativity` keeps the
   same mismatch: adjacent ET-support geometry plus a global `hF_local_dist`
   hypothesis;
3. the live theorem-2 frontier below
   `bvt_F_swapCanonical_pairing_of_adjacent_chain` is itself only an
   adjacent-step package;
4. therefore choosing the full-input route would force theorem 2 to overshoot
   its own local frontier and bury a much stronger global theorem inside a lane
   that is otherwise explicitly stepwise.

So the current theorem-2 production route is:

1. produce the ET-support package for `f` and its swapped partner `g`,
2. produce the flattened-regular boundary-continuity package for `bvt_F`,
3. identify the analytic representative with the `bvt_F` / `bvt_W` boundary
   package,
4. build the theorem-2-specific adjacent-only substitute consumer theorem
   `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` at the
   `AdjacencyDistributional.lean` / `BHWExtension.lean` seam; its exact
   contract is now:
   - inputs: `W_analytic`, `hW_hol`, `hW_real_inv`, the theorem-2 boundary
     package `W := bvt_W OS lgc`, the checked boundary-value theorem `hBV`, an
     adjacent index pair `(i, i+1)`, compact support for `f` and `g`, the swap
     identity `hswap`, ET support for `f` and `g`, and the two boundary
     continuity witnesses at real support points;
   - output: the adjacent raw-boundary pairing equality on
     `∫ extendF W_analytic (realEmbed x) * g x = ∫ extendF W_analytic (realEmbed x) * f x`;
   - forbidden input: no hypothesis of the form
     `IsLocallyCommutativeWeak d (bvt_W OS lgc)`.
   Its proof transcript is also frozen:
   (a) use the checked Route-B edge package to supply ET support;
   (b) use `analytic_boundary_local_commutativity_of_boundary_continuous` pointwise on the chosen open edge;
   (c) feed that pointwise equality into the already-checked integral/Schwartz transport machinery to close the compact-support pairing equality;
   (d) export the result as the single adjacent-only consumer theorem used by theorem 2.
5. feed that adjacent raw-boundary equality into the canonical-shift adapter.

At the production surface, the remaining hypotheses to supply are therefore no
longer just ET support plus continuity. There is also one sharpened closure
obligation:

1. the support points lie in the extended tube,
2. the swapped support points also lie in the extended tube,
3. the relevant boundary values of the analytic representative are continuous
   from the forward tube,
4. the raw-boundary theorem must be closed by the new theorem-2-specific
   adjacent-only substitute consumer theorem, rather than by silently feeding
   theorem 2 back into `W_analytic_swap_boundary_pairing_eq` or by first
   proving the stronger full-global theorem surface.

So the remaining theorem-2 task is not "prove locality from scratch." It is:

1. identify the exact analytic representative behind `bvt_F`,
2. prove the support-to-ET geometry needed by the checked adjacent-swap
   distributional theorem,
3. prove the boundary continuity hypotheses on the raw real support,
4. close the raw-boundary adjacent-swap pairing equality through the new
   adjacent-only substitute consumer theorem on the theorem-2 lane,
5. only then transport that equality to the canonical shifted BV pairing
   consumed by `bv_local_commutativity_transfer_of_swap_pairing`.

Route contract clarification:

1. the primary route is now the explicit real-open-edge / ET-support package
   consumed at the public theorem surface by
   `OSReconstruction/Wightman/Reconstruction/WickRotation/BHWExtension.lean ::
   W_analytic_swap_boundary_pairing_eq`, whose implementation already reduces
   to
   `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/AdjacencyDistributional.lean ::
   extendF_adjSwap_pairing_eq_of_distributional_local_commutativity`;
2. the direct pointwise theorem
   `analytic_boundary_local_commutativity_of_boundary_continuous` is a lower
   supplier theorem, not a second co-primary theorem-2 endgame;
3. the forward-Jost upgrade route is fallback-only and must not be treated as
   the default geometry entry point unless an exact production theorem first
   closes that stronger implication;
4. theorem 2 therefore has exactly one endorsed package order, but with an
   explicit adjacent-only core because the checked raw-boundary theorem surface
   `W_analytic_swap_boundary_pairing_eq` is adjacent-swap only (`i`, `i+1`),
   while the live frontier theorem in `OSToWightmanBoundaryValues.lean` is
   still stated for a general transposition `Equiv.swap i j`:
   `choose_real_open_edge_for_adjacent_swap`
   -> `swapped_support_lies_in_swapped_open_edge`
   -> `swapped_open_edge_embeds_in_extendedTube`
   -> `bvt_F_hasFlatRegularRepr`
   -> `bvt_F_boundary_continuous_at_real_support`
   -> `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`
   -> `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery`
   -> `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`
   -> `bvt_F_swapCanonical_pairing_of_adjacent_chain`
   -> `bvt_F_swapCanonical_pairing`;
5. the docs must therefore keep the adjacent-only raw-boundary layer distinct
   from the final general-swap frontier theorem. Later Lean work must not hide
   the reduction from arbitrary `swap i j` to an adjacent-transposition chain
   inside the closing frontier `sorry`.
6. in particular, `bvt_F_swapCanonical_pairing_of_adjacent_chain` is part of
   the checked-missing theorem-package inventory above, not an optional helper
   to be rediscovered ad hoc inside the frontier theorem.
7. the auxiliary names `adjacentSwapFactorization` and
   `AdjacentCanonicalSwapPairingStepHolds` that appear later in pseudocode are
   intentionally schematic only: they indicate that the general-swap proof must
   pass through explicit adjacent-step data, but they are not fixed theorem or
   definition names that already exist in the repo or that later Lean work must
   preserve literally.
8. if later work cannot supply one of those named packages at its assigned
   file locus, the docs must record that package as the blocker explicitly
   rather than collapsing geometry, raw-boundary locality, adjacent-chain
   reduction, and canonical-shift transport back into one closing `sorry`.

## 5. Exact theorem-slot inventory still needed

The documentation-standard theorem slots are:

```lean
lemma choose_real_open_edge_for_adjacent_swap
    (f : SchwartzNPoint d n) (i : Fin n) (hi : i.val + 1 < n)
    (hsep : ∀ x, f.toFun x ≠ 0 ->
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) :
    ∃ V : Set (NPointDomain d n),
      IsOpen V ∧
      tsupport (f : NPointDomain d n → ℂ) ⊆ V ∧
      (∀ x ∈ V, BHW.realEmbed x ∈ BHWCore.ExtendedTube d n) := by
  -- primary Route-B geometry package on an explicit real open edge

lemma swapped_support_lies_in_swapped_open_edge
    {V : Set (NPointDomain d n)}
    (f g : SchwartzNPoint d n) (i : Fin n) (hi : i.val + 1 < n)
    (hswap : ∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)))
    (hsupp : tsupport (f : NPointDomain d n → ℂ) ⊆ V) :
    tsupport (g : NPointDomain d n → ℂ) ⊆
      {x | (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ V} := by
  -- swap the chosen real open edge along the checked adjacent transposition

lemma swapped_open_edge_embeds_in_extendedTube
    {V : Set (NPointDomain d n)}
    (i : Fin n) (hi : i.val + 1 < n)
    (hV : ∀ x ∈ V, BHW.realEmbed x ∈ BHWCore.ExtendedTube d n) :
    ∀ x ∈ {x | (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ V},
      BHW.realEmbed x ∈ BHWCore.ExtendedTube d n := by
  -- ET-support for the swapped adjacent edge

lemma bvt_F_boundary_continuous_at_real_support
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ x,
      ContinuousWithinAt
        (bvt_F OS lgc n)
        (ForwardTube d n)
        (fun k μ => (x k μ : ℂ)) := by
  -- boundary continuity of the analytic representative at the real support

-- theorem-slot correction:
-- the endorsed theorem-2 route is now frozen at an adjacent-only substitute
-- consumer theorem on the `AdjacencyDistributional.lean` /
-- `BHWExtension.lean` seam. Do **not** expand theorem 2 into a preliminary
-- global theorem `IsLocallyCommutativeWeak d (bvt_W OS lgc)` just to reuse the
-- checked distributional consumer literally; that would overshoot the actual
-- adjacent-step frontier and blur the stepwise theorem-2 package structure.
--
-- So `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` should be read as
-- consuming the frozen adjacent-only substitute theorem
-- `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility` beneath it,
-- whose theorem surface is tailored to the fixed adjacent `(i,i+1,f,g)`
-- theorem-2 instance.

lemma adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility
    (W_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hW_hol : DifferentiableOn ℂ W_analytic (ForwardTube d n))
    (hW_real_inv : ∀ (Λ : LorentzLieGroup.LorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      W_analytic (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = W_analytic z)
    (W : (m : ℕ) → SchwartzNPoint d m → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          W_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (W n f)))
    (i : Fin n) (hi : i.val + 1 < n)
    (f g : SchwartzNPoint d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g : NPointDomain d n → ℂ))
    (hswap : ∀ x : NPointDomain d n,
      g x = f (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)))
    (hf_ET : ∀ x ∈ tsupport (f : NPointDomain d n → ℂ),
      BHW.realEmbed x ∈ BHWCore.ExtendedTube d n)
    (hg_ET : ∀ x ∈ tsupport (g : NPointDomain d n → ℂ),
      BHW.realEmbed x ∈ BHWCore.ExtendedTube d n)
    (hcont_f : ∀ x ∈ tsupport (f : NPointDomain d n → ℂ),
      ContinuousWithinAt W_analytic (ForwardTube d n) (fun k μ => (x k μ : ℂ)))
    (hcont_g : ∀ x ∈ tsupport (g : NPointDomain d n → ℂ),
      ContinuousWithinAt W_analytic (ForwardTube d n)
        (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ))) :
    (∫ x : NPointDomain d n,
      BHW.extendF W_analytic (BHW.realEmbed x) * (g x)) =
    (∫ x : NPointDomain d n,
      BHW.extendF W_analytic (BHW.realEmbed x) * (f x)) := by
  -- File ownership contract:
  -- * statement/export site: `BHWExtension.lean`
  -- * any lower integral/edge helper extracted from the proof: `AdjacencyDistributional.lean`
  -- Proof transcript contract:
  -- 1. instantiate `analytic_boundary_local_commutativity_of_boundary_continuous`
  --    pointwise on the chosen open edge for each real support point;
  -- 2. convert that pointwise raw-boundary equality into equality of the
  --    `extendF` integrands on the compactly supported supports of `f` and `g`;
  -- 3. close the pairing equality by integral congruence / support restriction;
  -- 4. do not call `W_analytic_swap_boundary_pairing_eq` or
  --    `extendF_adjSwap_pairing_eq_of_distributional_local_commutativity` with a
  --    global `IsLocallyCommutativeWeak` hypothesis on `W := bvt_W OS lgc`.

theorem bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    ∀ (f g : SchwartzNPoint d n),
      HasCompactSupport (f : NPointDomain d n → ℂ) →
      HasCompactSupport (g : NPointDomain d n → ℂ) →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ => (x k μ : ℂ)) * (g x)
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ => (x k μ : ℂ)) * (f x) := by
  -- close the theorem-2 adjacent raw-boundary equality by calling the frozen
  -- adjacent-only consumer theorem
  -- `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`.
  -- The checked public wrapper `W_analytic_swap_boundary_pairing_eq` remains
  -- only the downstream/public comparison shape, but it is not directly
  -- callable here on `W := bvt_W OS lgc` because that would reintroduce the
  -- forbidden global `IsLocallyCommutativeWeak` input.
```

The checked raw-boundary theorem surface is therefore *not yet* the live
frontier theorem surface: it closes only the adjacent-swap case on the raw real
trace, whereas the public consumer theorem and the private frontier theorem are
still stated for a general transposition `swap i j` on the canonical shifted
pairing. So two downstream adapters are still needed.

Primary-route consumption order:

1. `choose_real_open_edge_for_adjacent_swap`,
2. `swapped_support_lies_in_swapped_open_edge`,
3. `swapped_open_edge_embeds_in_extendedTube`,
4. `bvt_F_hasFlatRegularRepr`,
5. `bvt_F_boundary_continuous_at_real_support`,
6. the explicitly named adjacent-only substitute consumer theorem
   `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`
   (implemented in `BHWExtension.lean`, with any lower helper lemmas in
   `AdjacencyDistributional.lean`),
7. `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`,
8. `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery`,
9. `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`,
10. `bvt_F_swapCanonical_pairing_of_adjacent_chain`,
11. `bvt_F_swapCanonical_pairing`.

### 5.1. Concrete proof strategy for the boundary-continuity slot

The continuity theorem above should not remain an underspecified theorem slot. The
continuity route is now fixed in the documentation: the later Lean
implementation should go through the flattened regular Fourier-Laplace package,
not through ad hoc pointwise epsilon-delta continuity arguments.

The exact endorsed route in the current repo is:

1. `boundary_function_continuous_forwardTube_of_flatRegular` in
   `OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean`
   proves continuity of the real trace of a forward-tube holomorphic function,
   provided one has a regular flattened Fourier-Laplace package
   `SCV.HasFourierLaplaceReprRegular`.
2. The later theorem-2 implementation should therefore aim first for a regular
   flattened package for `bvt_F OS lgc n`, not for pointwise continuity by raw
   epsilon-delta arguments.

Repo note:

1. the source file is now referenced repo-relatively as
   `OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean`;
2. the earlier absolute `/Users/xiyin/...` path was a stale local path and is
   not part of the implementation contract.

So the preferred theorem-slot inventory is:

```lean
lemma bvt_F_flattened_holomorphic
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    HolomorphicOn
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
      (SCV.tubeDomain (ForwardConeFlat d n))

lemma bvt_F_flattened_distribution_boundary
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasBoundaryValueDistribution
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
      ((bvt_W OS lgc n).toContinuousLinearMap)

lemma bvt_F_flattened_growth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasPolynomialTubeGrowth
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)

lemma flatRegular_of_boundary_distribution_and_polyGrowth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)

lemma bvt_F_hasFlatRegularRepr
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm) := by
  exact
    flatRegular_of_boundary_distribution_and_polyGrowth
      (d := d) OS lgc n

lemma bvt_F_boundary_continuous_on_real_trace
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    Continuous (fun x : NPointDomain d n => bvt_F OS lgc n (fun k μ => (x k μ : ℂ))) := by
  exact
    boundary_function_continuous_forwardTube_of_flatRegular
      (d := d) (n := n)
      (bvt_F_holomorphic OS lgc n)
      (bvt_F_hasFlatRegularRepr (d := d) OS lgc n)

lemma bvt_F_boundary_continuous_at_real_support
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∀ x,
      ContinuousWithinAt
        (bvt_F OS lgc n)
        (ForwardTube d n)
        (fun k μ => (x k μ : ℂ)) := by
  -- derive `ContinuousWithinAt` from the global real-trace continuity theorem,
  -- together with the forward-tube approach geometry at real points
```

Canonical naming correction for the continuity subpackage:

1. the flattened-input theorem names used below are now fixed at
   `bvt_F_flattened_holomorphic`,
   `bvt_F_flattened_distribution_boundary`, and
   `bvt_F_flattened_growth`;
2. the older flipped names `flattened_bvt_F_*` should be treated as withdrawn
   draft vocabulary, not as a second valid theorem-slot family.

Checked-present source objects behind that theorem-shape inventory:

1. `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean :: bvt_F_holomorphic`
   already supplies the public unflattened holomorphic input for `bvt_F`.
2. `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean :: bvt_boundary_values`
   already supplies the public unflattened distributional boundary-value
   package for `bvt_F`.
3. The checked tree also contains two **private in-file packaging theorems** in
   `OSToWightmanBoundaryValuesBase.lean`:
   `forwardTube_boundaryValueData_of_polyGrowth` and
   `full_analytic_continuation_boundaryValueData`.
   Those are real checked supplier steps, but they are not public cross-file
   theorem surfaces. Later Lean work should treat them as the current internal
   packaging route inside `OSToWightmanBoundaryValuesBase.lean`, not as public
   helper names to consume from elsewhere in the tree.
4. `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightman.lean ::
   full_analytic_continuation_with_symmetry_growth`
   is the checked upstream public source of the unflattened polynomial-growth
   witness that the boundary-value packaging consumes on the OS side.
5. More sharply, the checked growth data is not just a vague provenance claim:
   in the current tree, the witness returned by
   `full_analytic_continuation_with_symmetry_growth` has the exact nested
   structure
   `choose_spec.1` = holomorphy,
   `choose_spec.2.1` = Euclidean restriction,
   `choose_spec.2.2.1` = permutation invariance,
   `choose_spec.2.2.2.1` = translation invariance,
   `choose_spec.2.2.2.2.1` = canonical-star symmetry,
   `choose_spec.2.2.2.2.2` = the polynomial-growth package.
   So the checked growth theorem surface consumed by theorem 2 is literally the
   tail field
   `∃ C_bd N, 0 < C_bd ∧ ∀ z ∈ ForwardTube d n,
      ‖bvt_F OS lgc n z‖ ≤ C_bd * (1 + ‖z‖) ^ N`
   living at
   `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightman.lean ::
   (full_analytic_continuation_with_symmetry_growth OS lgc n).choose_spec.2.2.2.2.2`.
   `OSToWightmanBoundaryValuesBase.lean` already destructures that exact field
   inside the private theorem `full_analytic_continuation_boundaryValueData`,
   so the remaining theorem-2 continuity work must treat the OS-side growth
   package as **checked-present unflattened input**, not as another theorem-
   family still to be discovered.
6. `OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean ::
   boundary_function_continuous_forwardTube_of_flatRegular`
   is already the checked continuity consumer once a flattened regular package
   is available.
7. `OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean ::
   boundary_value_recovery_forwardTube_of_flatRegular` and
   `boundary_value_recovery_forwardTube_of_flatRegular_from_bv`
   are already the checked boundary-recovery surfaces for turning canonical
   positive-imaginary-axis limits back into raw boundary pairings. Theorem-2
   docs should therefore not speak as if the raw-boundary-to-canonical bridge
   starts from a blank page.

So the theorem-2 continuity blocker is now narrower than the older blueprint
language suggested. The missing work is **not** to invent all three inputs from
scratch. The checked-present holomorphic input, the checked-present unflattened
boundary-distribution package, and the checked-present unflattened polynomial-
growth package already exist; the open gap is to transport those checked inputs
into flattened `ForwardConeFlat` form and combine them into a new regular
constructor.

This is the right current route because it uses already-proved transport
results in `ForwardTubeDistributions.lean` rather than inventing a new local
boundary continuity argument.

If `bvt_F_hasFlatRegularRepr` turns out not to be obtainable from the current
production growth package, then that regular package itself is the honest
theorem-2 blocker and should be documented under that exact name before any
locality proof resumes.

The checked source-to-slot map for the flattened continuity package is now part
of the theorem-2 contract:

1. `bvt_F_flattened_holomorphic` is the flattened transport of the checked
   public theorem `bvt_F_holomorphic`.
2. `bvt_F_flattened_distribution_boundary` is the flattened transport of the
   checked public theorem `bvt_boundary_values`; it is not to be sourced from
   the broader public existence theorem `boundary_values_tempered`, and it is
   not to treat the checked-private packaging theorems
   `forwardTube_boundaryValueData_of_polyGrowth` or
   `full_analytic_continuation_boundaryValueData` as cross-file dependency
   surfaces.
3. `bvt_F_flattened_growth` is the flattened transport of the explicit
   polynomial-growth field exported by the checked public theorem
   `full_analytic_continuation_with_symmetry_growth` for the chosen `bvt_F`
   witness — concretely, the field reached in the current tree by peeling the
   exact projection chain
   `choose_spec.2.2.2.2.2` after the holomorphy / Euclidean / permutation /
   translation / canonical-star components.
4. `flatRegular_of_boundary_distribution_and_polyGrowth` is the constructor
   that must combine exactly those three flattened transports on the checked
   `ForwardTubeDistributions.lean` side of the stack.

The key documentation correction is:

1. there is no current repo theorem named
   `SCV.hasFourierLaplaceReprRegular_of_boundary_and_growth`,
2. the actual missing theorem package is the constructor
   `flatRegular_of_boundary_distribution_and_polyGrowth`,
3. the checked-present `bvt_F` supplier names are now fixed at
   `bvt_F_holomorphic` and `bvt_boundary_values`,
4. the checked growth source for those suppliers is
   `full_analytic_continuation_with_symmetry_growth`, with
   `forwardTube_boundaryValueData_of_polyGrowth` /
   `full_analytic_continuation_boundaryValueData` serving as the checked-private
   in-file unflattened packaging layer and `bvt_boundary_values` serving as the
   checked public boundary-distribution surface,
5. the remaining theorem-shape ambiguity is therefore concentrated in the
   flattened growth transport plus the new regular constructor, not in the
   holomorphic or boundary-distribution inputs themselves.

### 5.2. Exact subpackages behind `bvt_F_hasFlatRegularRepr`

The regular flattened package should itself be documented as a small theorem
suite, not as one unexplained miracle theorem.

The later Lean port should split it into:

```lean
lemma bvt_F_flattened_holomorphic
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    HolomorphicOn
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
      (SCV.tubeDomain (ForwardConeFlat d n)) := by
  -- transport `bvt_F_holomorphic` through the flattening equivalence

lemma bvt_F_flattened_distribution_boundary
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasBoundaryValueDistribution
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
      ((bvt_W OS lgc n).toContinuousLinearMap) := by
  -- flattened form of the checked theorem `bvt_boundary_values`

lemma bvt_F_flattened_growth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasPolynomialTubeGrowth
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm) := by
  -- transport the checked forward-tube growth field exported by
  -- `full_analytic_continuation_with_symmetry_growth` (the same field already
  -- unpacked internally by `full_analytic_continuation_boundaryValueData`)
  -- into flattened coordinates; this is now the honest open subpackage

lemma bvt_F_hasFlatRegularRepr
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm) := by
  exact
    flatRegular_of_boundary_distribution_and_polyGrowth
      (d := d) OS lgc n
```

This is the correct level of explicitness for theorem 2 because the
`ForwardTubeDistributions` package already proves the final transport theorems.
What remains open is the *flattened regular input package* for `bvt_F`, not the
continuity conclusion itself.

The constructor theorem should be read as an actual future file target:

1. transport the checked theorem `bvt_F_holomorphic` to flattened coordinates,
2. transport the checked public theorem `bvt_boundary_values` to flattened
   coordinates as the source for `bvt_F_flattened_distribution_boundary`,
3. transport the checked forward-tube polynomial-growth field from the exact
   growth field exported by
   `OSToWightman.lean :: full_analytic_continuation_with_symmetry_growth`
   into flattened coordinates,
4. combine those three checked inputs in a new SCV/forward-tube regularity
   constructor,
5. only then specialize to `bvt_F_hasFlatRegularRepr`.

Exact file-ownership contract for this continuity subpackage:

1. the checked-present unflattened source objects in
   `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean`
   split into:
   - public theorem surfaces: `boundary_values_tempered`,
     `bvt_F_holomorphic`, and `bvt_boundary_values`;
     for the theorem-2 continuity lane, the designated source theorems are
     `bvt_F_holomorphic` for the flattened holomorphic slot and
     `bvt_boundary_values` for the flattened boundary-distribution slot, while
     `boundary_values_tempered` remains the broader public existence theorem
     rather than the designated source object for that flattened transport;
   - private in-file packaging theorems: `forwardTube_boundaryValueData_of_polyGrowth`
     and `full_analytic_continuation_boundaryValueData`;
   the docs should keep that visibility split explicit so later implementation
   work does not mistake a private packaging lemma for an exported cross-file
   dependency surface;
2. the checked upstream growth witness still originates in
   `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightman.lean ::
   full_analytic_continuation_with_symmetry_growth`, and the current checked
   field access pattern is now part of the contract: the unflattened growth
   package is obtained from the exact tail projection
   `(full_analytic_continuation_with_symmetry_growth OS lgc n).choose_spec.2.2.2.2.2`;
3. the new flattened growth transport theorem
   `bvt_F_flattened_growth` should be documented literally as the transport of
   the checked growth field exported by
   `full_analytic_continuation_with_symmetry_growth` (the same field already
   unpacked in `OSToWightmanBoundaryValuesBase.lean ::
   full_analytic_continuation_boundaryValueData`), and together with the new
   constructor `flatRegular_of_boundary_distribution_and_polyGrowth` it belongs
   on the checked
   `OSReconstruction/Wightman/Reconstruction/ForwardTubeDistributions.lean`
   side of the stack, because that file already owns the flat-regular
   representation interface and the continuity consumer
   `boundary_function_continuous_forwardTube_of_flatRegular`;
4. `OSToWightmanBoundaryValues.lean` should consume the finished theorem
   `bvt_F_hasFlatRegularRepr`, not absorb the flattened-growth transport or the
   regular constructor into the frontier locality proof.

So the theorem-2 continuity lane now has an explicit supplier/constructor split:
`OSToWightmanBoundaryValuesBase.lean` supplies the checked unflattened
boundary-data package, `OSToWightman.lean` supplies the upstream growth
witness, `ForwardTubeDistributions.lean` owns the missing flattened-growth /
flat-regular constructor work, and only then does
`OSToWightmanBoundaryValues.lean` consume the resulting continuity theorem.

### 5.3. Exact route from continuity to the raw-boundary swap pairing

Once the regular flattened package is in place, the later proof should not jump
straight to the canonical shifted pairing. There is an intermediate raw-boundary
theorem surface:

```lean
theorem bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    ∀ (f g : SchwartzNPoint d n),
      HasCompactSupport (f : NPointDomain d n → ℂ) →
      HasCompactSupport (g : NPointDomain d n → ℂ) →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      ∫ x, bvt_F OS lgc n (fun k μ => (x k μ : ℂ)) * g x
        =
      ∫ x, bvt_F OS lgc n (fun k μ => (x k μ : ℂ)) * f x := by
  intro f g hf_compact hg_compact hsep hswap
  obtain ⟨V, hV_open, hf_support, hV_ET⟩ :=
    choose_real_open_edge_for_adjacent_swap (d := d) (n := n) f i hi hsep
  have hg_support :
      tsupport (g : NPointDomain d n → ℂ) ⊆
        {x | (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ V} := by
    exact
      swapped_support_lies_in_swapped_open_edge
        (d := d) (n := n) (V := V) f g i hi hswap hf_support
  have hg_ET :=
    swapped_open_edge_embeds_in_extendedTube
      (d := d) (n := n) (V := V) i hi hV_ET
  have hflat := bvt_F_hasFlatRegularRepr (d := d) OS lgc n
  have hcont := bvt_F_boundary_continuous_at_real_support (d := d) OS lgc n
  -- Important checked-surface warning:
  -- `W_analytic_swap_boundary_pairing_eq` also asks for
  -- `hLC : IsLocallyCommutativeWeak d W`. For `W := bvt_W OS lgc`, that would
  -- be circular here. So the raw-boundary closure must descend to
  -- `extendF_adjSwap_pairing_eq_of_distributional_local_commutativity` or use
  -- another explicitly documented non-circular substitute for that `hLC`
  -- input before the public wrapper is reused.
  exact
    adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility
      (d := d) (OS := OS) (lgc := lgc) (n := n) (i := i) (hi := hi)
      f g hf_compact hg_compact hsep hswap
      (by intro x hx; exact hV_ET x (hf_support hx))
      (by intro x hx; exact hg_ET x (hg_support hx))
      hflat hcont
```

Only after this raw-boundary theorem is in place should the later file prove
the canonical-shift adapter. That final adapter should be documented as a
separate wrapper theorem because it changes the evaluation surface from
`x ↦ x` to `x ↦ x + i ε η_can`, and that change is not part of the BHW
locality theorem itself.

Documentation correction: the raw-boundary theorem slot is not a request to
reprove the BHW/distributional locality package under a new theorem name, but
it is also not yet a one-line instantiation of
`W_analytic_swap_boundary_pairing_eq`. The checked public wrapper has an extra
`hLC` hypothesis that becomes circular on `bvt_W`. So the live implementation
standard is: close the raw-boundary equality by an explicitly non-circular
consumer of the checked distributional theorem surface, and only then compare
that theorem to `W_analytic_swap_boundary_pairing_eq` as the downstream/public
shape. The lower pointwise theorem
`analytic_boundary_local_commutativity_of_boundary_continuous` stays only as a
supplier-level fallback inside `BHWExtension.lean`, not as the theorem-2 proof
surface.

### 5.4. Exact support-to-ET geometry route

The ET-support lemmas should also not remain black boxes. The current repo
already contains the geometric package that should drive them, but the primary
documentation contract remains the explicit open-edge Route B rather than an
undocumented jump straight to global forward-Jost membership.

Checked-source clarification for the Route-B geometry package:

1. `Adjacency.lean :: exists_real_open_nhds_adjSwap` already proves the local
   open-neighborhood theorem with three output layers at once: local adjacent
   spacelike persistence, ET membership of the edge itself, and ET membership
   of the swapped edge.
2. Therefore the theorem-2 wrappers should not try to manufacture a fresh
   swapped-ET argument from bare openness again. The only missing work above
   that theorem is:
   - compact-support packaging of those local neighborhoods into one open edge
     covering `tsupport f`,
   - pure support transport from `f` to `g`,
   - and then pure ET transport from `V` to the swapped preimage edge.
3. In particular, `swapped_open_edge_embeds_in_extendedTube` should be read as
   consuming the swapped-ET clause already produced at the `Adjacency.lean`
   layer, not as a request to rediscover a new BHW geometry theorem.
4. `ComplexLieGroups/JostPoints.lean` remains relevant only as a checked
   fallback supplier file on theorem 2: it contains `JostSet`,
   `ForwardJostSet`, `realEmbed`, and the theorem
   `forwardJostSet_subset_extendedTube`, but those are **not** the primary
   theorem-2 geometry entry point under the current contract.
5. The checked Route-B consumer surface is still the adjacent-swap
   distributional package in
   `ComplexLieGroups/Connectedness/BHWPermutation/AdjacencyDistributional.lean`,
   especially
   `extendF_adjSwap_pairing_eq_of_distributional_local_commutativity`.

The intended primary theorem-2 support route should therefore be:

```lean
lemma choose_real_open_edge_for_adjacent_swap
    (f : SchwartzNPoint d n) (i : Fin n) (hi : i.val + 1 < n)
    (hsep : ∀ x, f.toFun x ≠ 0 ->
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) :
    ∃ V : Set (NPointDomain d n),
      IsOpen V ∧
      tsupport (f : NPointDomain d n → ℂ) ⊆ V ∧
      (∀ x ∈ V, BHW.realEmbed x ∈ BHWCore.ExtendedTube d n)

lemma swapped_support_lies_in_swapped_open_edge
    {V : Set (NPointDomain d n)}
    (f g : SchwartzNPoint d n) (i : Fin n) (hi : i.val + 1 < n)
    (hswap : ∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)))
    (hsupp : tsupport (f : NPointDomain d n → ℂ) ⊆ V) :
    tsupport (g : NPointDomain d n → ℂ) ⊆
      {x | (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ V}

lemma swapped_open_edge_embeds_in_extendedTube
    {V : Set (NPointDomain d n)}
    (i : Fin n) (hi : i.val + 1 < n)
    (hV : ∀ x ∈ V, BHW.realEmbed x ∈ BHWCore.ExtendedTube d n) :
    ∀ x ∈ {x | (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ V},
      BHW.realEmbed x ∈ BHWCore.ExtendedTube d n
```

The route decision is now frozen more sharply than older drafts suggested.

1. theorem 2 is **not** currently waiting on a preliminary global support
   theorem such as `canonical_support_mem_forwardJost_of_adjacent_spacelike`;
2. theorem 2 is documented to run directly through the checked adjacent-swap
   ET-support consumer surface in `AdjacencyDistributional.lean`, whose inputs
   are exactly the Route-B open-edge / ET-support packages above;
3. any future forward-Jost strengthening theorem belongs to blocked-only
   fallback analysis, not to the primary theorem-2 execution transcript;
4. therefore later Lean work should start by building the three named Route-B
   wrappers above `exists_real_open_nhds_adjSwap`, not by trying first to
   upgrade the support hypothesis to global `ForwardJostSet` membership.

### 5.5. Lean-style endgame script with all remaining theorem slots visible

```lean
private theorem bvt_F_swapCanonical_pairing
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i j : Fin n) (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * g x
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * f x := by
  intro n i j f g ε hε hsep hswap
  have hchain :
      ∀ᵃ step ∈ adjacentSwapFactorization i j,
        AdjacentCanonicalSwapPairingStepHolds d (bvt_F OS lgc n) f g ε step := by
    intro step hstep
    rcases step with ⟨k, hk_next, f_step, g_step, hswap_step, hsep_step⟩
    have hraw_step :=
      bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support
        (d := d) (OS := OS) (lgc := lgc) n k hk_next f_step g_step
        (schwartz_compactSupport_if_needed ...)
        (schwartz_compactSupport_if_needed ...)
        hsep_step hswap_step
    exact
      bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality
        (d := d) (OS := OS) (lgc := lgc)
        n k hk_next f_step g_step ε hε hsep_step hswap_step hraw_step
  exact
    bvt_F_swapCanonical_pairing_of_adjacent_chain
      (d := d) (OS := OS) (lgc := lgc) n i j f g ε hε hsep hswap hchain
```

The key theorem-surface correction is that the adjacent raw-boundary theorem and
adjacent canonical-shift adapter may only be called on actual adjacent steps
`(k, k+1)`. The general-transposition frontier theorem must therefore consume
those stepwise results through the separate theorem
`bvt_F_swapCanonical_pairing_of_adjacent_chain`; it must not call an
adjacent-only theorem surface directly on arbitrary `i j` data.

This is the closure standard the docs should now enforce:

1. ET support geometry named and assigned to the BHW-permutation / adjacency
   layer,
2. boundary continuity package named and assigned to the forward-tube
   distribution layer,
3. raw-boundary swap theorem named and assigned to the BHW-extension layer,
4. canonical-shift adapter named and assigned to
   `OSToWightmanBoundaryValueLimits.lean`.

If any one of those four is missing in a later Lean proof, then theorem 2 is
still underdocumented.

## 6. Canonical-shift adapter required by the frontier theorem

The consumer
`bv_local_commutativity_transfer_of_swap_pairing`
expects the canonical shifted pairing, not the raw real-support pairing.

Important checked-tree correction:

1. the active adapter package should now be written as a specialization layer
   above the checked forward-tube boundary-recovery surface
   `boundary_value_recovery_forwardTube_of_flatRegular_from_bv`, not as a
   completely free-floating pair of new rewrite lemmas;
2.5 the docs should therefore name the exact checked supplier package for that
   specialization: `OSToWightmanBoundaryValuesBase.lean :: bvt_W`,
   `bvt_W_continuous`, and `bvt_boundary_values`.
2. in other words, once the theorem-2 lane has built
   `bvt_F_hasFlatRegularRepr`, the remaining raw-boundary-to-canonical step is
   to package the canonical direction
   `η = canonicalForwardConeDirection (d := d) n`, the checked theorem-2
   boundary functional `T := bvt_W OS lgc n`, its continuity witness
   `bvt_W_continuous OS lgc n`, the canonical boundary-value input
   `bvt_boundary_values OS lgc n`, and the adjacent raw-boundary theorem into a
   boundary-value recovery specialization that can be consumed by
   `bv_local_commutativity_transfer_of_swap_pairing`;
2a. checked-file caution: `OSToWightmanBoundaryValueLimits.lean` already
   contains theorem-3-side `singleSplit_xiShift` / positive-time limit results.
   The theorem-2 specialization above must therefore be described as a new
   canonical-boundary package in the same file, not as a reuse of the
   `singleSplit_xiShift` shell with renamed notation;
3. the still-missing theorem package is therefore narrower than the older docs
   suggested: it is an adjacent-step boundary-value specialization layer for
   theorem 2, not a generic request to invent raw/canonical rewrite lemmas
   from scratch;
4. equivalently, the theorem-2 adapter is **not** waiting on a new mysterious
   boundary functional. The only open work is to specialize the checked
   recovery theorem to the already-exported `bvt_W` / `bvt_boundary_values`
   package and combine that specialization with the adjacent raw-boundary
   equality.

So the canonical-shift endgame should be documented as two theorem slots:

```lean
theorem bvt_F_canonical_boundary_pairing_eq_from_bv_recovery
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (f : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x)
      =
      (bvt_W OS lgc n) f := by
  -- specialize the checked recovery theorem
  -- `boundary_value_recovery_forwardTube_of_flatRegular_from_bv`
  -- with `T := bvt_W OS lgc n`, continuity witness
  -- `bvt_W_continuous OS lgc n`, boundary-value witness
  -- `bvt_boundary_values OS lgc n`, and the canonical direction
  -- `canonicalForwardConeDirection (d := d) n`

theorem bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
      (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k))) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
  -- combine the adjacent raw-boundary equality
  -- `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` with the
  -- theorem-2-specific canonical pairing specialization
  -- `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` applied on both
  -- sides

lemma bvt_F_swapCanonical_pairing_of_adjacent_chain
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i j : Fin n) (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      (∀ᵃ step ∈ adjacentSwapFactorization i j,
        AdjacentCanonicalSwapPairingStepHolds d (bvt_F OS lgc n) f g ε step) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
  -- reduce a general transposition to the adjacent-swap canonical package;
  -- exact helper names for the factorization data may change, but this
  -- theorem-layer obligation must stay explicit in the docs.
```

At the current repo state, the general adjacent-chain reducer is still only a
planned theorem package, and the theorem-2 canonical-shift endgame above
`boundary_value_recovery_forwardTube_of_flatRegular_from_bv` is still missing
as two separate packages: the explicit canonical pairing recovery
specialization `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` and the
gluing theorem `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`.
The docs should therefore keep all three layers visible rather than hiding the
adjacent-only/raw-boundary mismatch inside the closing frontier `sorry`.

### 6.1. Exact `OSToWightmanBoundaryValueLimits.lean` sibling-subsection contract

The checked file
`OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean`
already has a very specific internal role in the live tree: it imports
`OSToWightmanBoundaryValuesComparison.lean` and packages theorem-3-side
`singleSplit_xiShift` / `t → 0+` boundary-limit statements for the positivity
route. That checked file reality creates a concrete documentation obligation for
later theorem-2 Lean work:

1. theorem-2 support added to this file must be a **new sibling subsection**,
   not a silent extension of the existing theorem-3 positive-time shell;
2. the theorem-2 subsection must start from checked forward-tube recovery
   surfaces and end at checked theorem-2 canonical pairing equalities, with the
   positivity-only `singleSplit_xiShift` material treated as a neighboring lane
   rather than as a reusable theorem-2 wrapper;
3. the file-local order of the new theorem-2 subsection is part of the route
   contract, because later Lean work should be able to open this file and prove
   the theorem-2 closure package top-to-bottom without deciding again what the
   subsection is trying to own.

The required theorem-2 subsection order in
`OSToWightmanBoundaryValueLimits.lean` is therefore:

1. `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery`
2. `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`
3. `bvt_F_swapCanonical_pairing_of_adjacent_chain`

The exact internal proof transcript of the first theorem is now also part of the
doc contract.

`bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` must proceed in this
order:

1. consume the checked flat-regular package `bvt_F_hasFlatRegularRepr`;
2. instantiate the checked recovery theorem
   `boundary_value_recovery_forwardTube_of_flatRegular_from_bv` with:
   - holomorphic function `bvt_F OS lgc n`,
   - boundary functional `bvt_W OS lgc n`,
   - continuity witness `bvt_W_continuous OS lgc n`,
   - boundary-value witness `bvt_boundary_values OS lgc n`,
   - direction `canonicalForwardConeDirection (d := d) n`;
3. rewrite the resulting recovery statement into the exact pairing equality
   consumed later by theorem 2.

`bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality` must then
proceed in this order:

1. call the adjacent raw-boundary theorem
   `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`;
2. apply `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` on the `g`
   side;
3. apply `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` on the `f`
   side;
4. close by transitivity/symmetry of the resulting equalities.

Finally, `bvt_F_swapCanonical_pairing_of_adjacent_chain` must remain a separate
finite-composition theorem in the same subsection:

1. input: explicit adjacent-step data realizing general `swap i j` as an
   adjacent chain;
2. per-step consumer: the adjacent canonical theorem
   `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`;
3. output: the general `swap i j` canonical pairing equality consumed by the
   frontier theorem.

This sharper sibling-subsection contract eliminates a real implementation
ambiguity that remained after the earlier file-locus fix: later Lean work is no
longer left to guess whether `OSToWightmanBoundaryValueLimits.lean` should own a
recovery specialization, a canonical gluing theorem, or only theorem-3
positivity limits. It must own all three theorem-2 canonical-direction layers,
in that order, as a sibling package below the theorem-2 frontier and beside the
existing theorem-3 lane.

The pseudocode names `adjacentSwapFactorization` and
`AdjacentCanonicalSwapPairingStepHolds` in the displayed scripts should be read
in that same light: they are explanatory placeholders for the internal data
passed to `bvt_F_swapCanonical_pairing_of_adjacent_chain`, not additional
contract-level theorem slots.

## 7. Exact proof decomposition for theorem 2

The later Lean proof should run in this order.

1. Use the primary Route-B open-edge package to place the real support of `f`
   in an explicit real open edge whose image lies in the extended tube.
2. Transport that open edge through the adjacent swap and obtain ET support for
   the swapped test function `g`.
3. Build the flattened regular Fourier-Laplace package
   `bvt_F_hasFlatRegularRepr` and then derive
   `bvt_F_boundary_continuous_at_real_support` from it.
4. Prove the new theorem-2-specific adjacent-only substitute consumer theorem
   on the chosen adjacent ET-support package, and use it to obtain
   `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` without first
   expanding theorem 2 into the stronger global theorem
   `IsLocallyCommutativeWeak d (bvt_W OS lgc)`.
5. Prove the theorem-2-specific canonical pairing recovery theorem
   `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery` that specializes
   `boundary_value_recovery_forwardTube_of_flatRegular_from_bv` to
   `T := bvt_W OS lgc n` using `bvt_W_continuous OS lgc n`,
   `bvt_boundary_values OS lgc n`, and the canonical direction.
6. Prove the separate adjacent canonical-shift gluing theorem
   `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality` that
   combines that canonical pairing formula with the adjacent raw-boundary
   equality from `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`.
7. Prove the general-swap reduction theorem
   `bvt_F_swapCanonical_pairing_of_adjacent_chain` that composes those adjacent
   canonical equalities into the frontier theorem surface for `swap i j`.
8. Feed that theorem into
   `bv_local_commutativity_transfer_of_swap_pairing`.

The theorem should not be attacked by re-proving edge-of-the-wedge or by
opening a new permutation-continuation front in the middle of
`OSToWightmanBoundaryValues.lean`.

File-locus enforcement for that proof transcript:

1. the Route-B support/ET package should be introduced under the checked
   BHW-permutation support locus, not as local lemmas inside
   `OSToWightmanBoundaryValues.lean`;
2. the flattened-regular constructor / continuity package should stay under
   `ForwardTubeDistributions.lean`;
3. the theorem-2-specific non-circular local-commutativity supplier and the
   raw-boundary instantiation layer should sit with the BHW-extension /
   adjacent-distributional consumer boundary, so later Lean work can see
   explicitly where the `IsLocallyCommutativeWeak` input is supplied before the
   checked pairing theorem is called;
4. the canonical-shift recovery/rewriting layer should sit in
   `OSToWightmanBoundaryValueLimits.lean`;
5. the general-swap adjacent-chain reducer
   `bvt_F_swapCanonical_pairing_of_adjacent_chain` should also sit in
   `OSToWightmanBoundaryValueLimits.lean`, because it is still part of the
   canonical-shift closure package below the frontier consumer;
6. only the final frontier theorem should remain in
   `OSToWightmanBoundaryValues.lean`.

## 8. Historical docs that are no longer frontier guidance

The following docs are historical and should not be used as primary route
guidance for theorem 2:

1. `docs/edge_of_the_wedge_proof_plan.md`
2. `docs/edge_of_the_wedge_gap_analysis.md`

Both were written before the theorem

```lean
SCV.edge_of_the_wedge_theorem
```

was proved. They are still useful for mathematical context, but they do not
describe the current production frontier on `main`.

## 9. Exact theorem-name dictionary for theorem 2

The later proof should visibly use the following names, but with the theorem
surfaces separated by role rather than collapsed into one fake closure point:

### 9.1. Checked-present comparison / lower supplier surfaces

1. `bvt_F_perm`
2. `bv_local_commutativity_transfer_of_swap_pairing`
3. `W_analytic_swap_boundary_pairing_eq`
4. `extendF_adjSwap_pairing_eq_of_distributional_local_commutativity`
5. `analytic_boundary_local_commutativity_of_boundary_continuous`
6. `edge_of_the_wedge`
7. `SCV.edge_of_the_wedge_theorem`
8. `jost_lemma`

### 9.2. Planned theorem-2 closure slots that the docs fix explicitly

1. `choose_real_open_edge_for_adjacent_swap`
2. `swapped_support_lies_in_swapped_open_edge`
3. `swapped_open_edge_embeds_in_extendedTube`
4. `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`
5. `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support`
6. `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery`
7. `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`
8. `bvt_F_swapCanonical_pairing_of_adjacent_chain`
9. `bvt_F_swapCanonical_pairing`

The name-level discipline here is intentional:
- `W_analytic_swap_boundary_pairing_eq` is a checked public comparison wrapper,
  not the theorem-2 raw-boundary closure theorem on `W := bvt_W OS lgc`;
- `extendF_adjSwap_pairing_eq_of_distributional_local_commutativity` is the
  checked lower supplier surface for the same seam, but it still asks for the
  global locality hypothesis `IsLocallyCommutativeWeak d W` and therefore is
  not itself the non-circular theorem-2 closure theorem either;
- `analytic_boundary_local_commutativity_of_boundary_continuous` remains the
  lower pointwise ingredient used inside the planned adjacent-only substitute
  consumer `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`;
- the actual theorem-2 implementation route must therefore pass visibly through
  the planned closure slots in §9.2 before reaching the frontier theorem
  `bvt_F_swapCanonical_pairing`.

If later pseudocode skips the §9.2 theorem slots and jumps straight from the
checked BHW/distributional theorems to the frontier, the implementation is
again drifting toward the stale circular locality plan.

## 10. Do not do this

1. Do not reintroduce edge-of-the-wedge as an axiom or a missing theorem.
2. Do not mix theorem 2 with theorem 3 positivity reductions.
3. Do not claim locality directly from permutation invariance of `bvt_F` alone;
   the real issue is boundary pairing and ET/Jost support geometry.
4. Do not use the historical edge-of-the-wedge gap notes as if they still
   described `main`.
5. Do not hide the raw-boundary-to-canonical adapter inside the closing
   `sorry`.

## 11. Minimal Lean pseudocode for the full closure

```lean
private theorem bvt_F_swapCanonical_pairing
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (i j : Fin n) (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
      =
      ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
  -- Step A: prove the raw-boundary swap theorem from the BHW package
  have hraw :=
    bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support
      (d := d) (OS := OS) (lgc := lgc)
  -- Step B: transport raw-boundary locality to the canonical shifted BV pairing
  exact
    bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality
      (d := d) (OS := OS) (lgc := lgc)
```

## 12. The regular-input constructor theorem that is actually missing

The current blueprint should now be explicit about one important fact:

```lean
SCV.hasFourierLaplaceReprRegular_of_boundary_and_growth
```

does **not** exist anywhere in the current repo.

What *does* exist is the downstream package that *consumes*
`HasFourierLaplaceReprRegular`:

1. `boundary_function_continuous_forwardTube_of_flatRegular`,
2. `boundary_value_recovery_forwardTube_of_flatRegular`,
3. `distributional_uniqueness_forwardTube_of_flatRegular`,
4. `polynomial_growth_forwardTube_of_flatRegular`.

So the theorem-2 route should be documented as requiring a new constructor
package, not as a one-line application of an already-existing helper.

The honest theorem-slot inventory is:

```lean
lemma bvt_F_flattened_distribution_boundary
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasBoundaryValueDistribution
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
      ((bvt_W OS lgc n).toContinuousLinearMap)

lemma bvt_F_flattened_growth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasPolynomialTubeGrowth
      (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)

lemma flatRegular_of_boundary_distribution_and_polyGrowth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)

lemma bvt_F_hasFlatRegularRepr
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (bvt_F OS lgc n ∘ (flattenCLEquiv n (d + 1)).symm)
```

The first two are already the theorem shapes the blueprint was using. The third
is the real missing theorem. Only the fourth is an adapter name specialized to
`bvt_F`.

### 12.1. What the constructor proof must look like

The later Lean proof should be documented as:

1. prove holomorphy of the flattened function from `bvt_F_holomorphic`,
2. prove distributional boundary values of the flattened function using the
   existing `bvt_W` boundary package,
3. prove polynomial growth on the flattened tube from the already-constructed
   growth package for `bvt_F`,
4. package those three inputs into a new regular constructor theorem,
5. only then call the forward-tube continuity/recovery theorems.

The critical point is that Step 4 is a real theorem package, not a missing
`simpa`.

### 12.2. Estimated Lean line counts for the regular package

1. flattened boundary-value adapter:
   roughly `25-60` lines.
2. flattened growth adapter:
   roughly `20-50` lines.
3. regular constructor theorem
   `flatRegular_of_boundary_distribution_and_polyGrowth`:
   roughly `60-120` lines if done directly in the flattened SCV language.
4. specialization to `bvt_F_hasFlatRegularRepr`:
   roughly `10-25` lines.

So the honest continuity package here is roughly `115-255` lines, and the
central missing theorem is the regular constructor, not the continuity theorem
itself.

## 13. Exact support-to-ET geometry proof sketch

The theorem-2 docs should also write the **primary Route-B** support route at
 theorem-script level, because that is the geometry package the current repo
already nearly supports.

The later proof should proceed as follows.

1. Start from the support hypothesis
   `∀ x, f.toFun x ≠ 0 -> AreSpacelikeSeparated d (x i) (x j)`.
2. For each support point, call the checked supplier
   `Adjacency.lean :: exists_real_open_nhds_adjSwap` to obtain a local open
   real edge carrying adjacent spacelike persistence, ET membership of the
   edge, and ET membership of the swapped edge.
3. Use compactness of `tsupport f` to pass from that local family to one open
   edge `V` covering the whole support of `f`.
4. Transport support from `f` to `g` along the checked swap identity.
5. Transport ET membership from `V` to the swapped preimage edge.
6. Feed those two ET-support statements to the adjacent raw-boundary lane.

In Lean-style pseudocode, the wrapper package should look like:

```lean
lemma choose_real_open_edge_for_adjacent_swap
    (f : SchwartzNPoint d n) (i : Fin n) (hi : i.val + 1 < n)
    (hsep : ∀ x, f.toFun x ≠ 0 ->
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) :
    ∃ V : Set (NPointDomain d n),
      IsOpen V ∧
      tsupport (f : NPointDomain d n → ℂ) ⊆ V ∧
      (∀ x ∈ V, BHW.realEmbed x ∈ BHWCore.ExtendedTube d n) := by
  -- proof transcript contract:
  -- 1. fix x ∈ tsupport f;
  -- 2. apply `exists_real_open_nhds_adjSwap` at x using hsep;
  -- 3. extract the local open edge and ET clauses;
  -- 4. use compactness of tsupport f to choose a finite subcover;
  -- 5. take the finite union as V.

lemma swapped_support_lies_in_swapped_open_edge
    {V : Set (NPointDomain d n)}
    (f g : SchwartzNPoint d n) (i : Fin n) (hi : i.val + 1 < n)
    (hswap : ∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)))
    (hsupp : tsupport (f : NPointDomain d n → ℂ) ⊆ V) :
    tsupport (g : NPointDomain d n → ℂ) ⊆
      {x | (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ V} := by
  -- support transport only; no new geometry theorem here.

lemma swapped_open_edge_embeds_in_extendedTube
    {V : Set (NPointDomain d n)}
    (i : Fin n) (hi : i.val + 1 < n)
    (hV : ∀ x ∈ V, BHW.realEmbed x ∈ BHWCore.ExtendedTube d n) :
    ∀ x ∈ {x | (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ V},
      BHW.realEmbed x ∈ BHWCore.ExtendedTube d n := by
  -- ET transport only; consume the swapped-edge ET clause already built
  -- into the chosen Route-B neighborhood package.
```

Estimated Lean size for the Route-B wrapper package:

1. `choose_real_open_edge_for_adjacent_swap`: roughly `35-80` lines,
   depending on the compact-support finite-cover packaging;
2. `swapped_support_lies_in_swapped_open_edge`: roughly `15-35` lines;
3. `swapped_open_edge_embeds_in_extendedTube`: roughly `10-25` lines.

Fallback-only note:

1. a separate forward-Jost theorem such as
   `support_mem_forwardJost_of_adjacent_spacelike` may still be mathematically
   interesting;
2. if it is ever proved under an exact production name, it can shorten the
   geometry lane by composing with `forwardJostSet_subset_extendedTube` from
   `ComplexLieGroups/JostPoints.lean`;
3. but that is **not** the primary theorem-2 route, and later Lean work should
   not start from that fallback theorem unless the docs are rewritten first.

## 14. Exact proof sketch for the raw-boundary-to-canonical adapter

The theorem-2 canonical-shift endgame should not be left as a slogan. In the
checked repo tree this adapter package belongs in the theorem-2 closure layer around
`OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean`,
not inside the raw-boundary BHW file and not as an unnamed local rewrite at the
end of `OSToWightmanBoundaryValues.lean`. The later Lean proof should be a
named two-theorem package with a three-step internal transcript.

1. apply the raw-boundary theorem to the underlying real-edge test functions;
2. rewrite the canonical shifted pairing as the raw pairing against the
   boundary trace by the boundary-value recovery theorem;
3. use the same rewrite on both `f` and `g` and conclude by transitivity.

The theorem-slot inventory should therefore be read as:

```lean
theorem bvt_F_canonical_boundary_pairing_eq_from_bv_recovery
theorem bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality
```

with the internal proof transcript explicitly split into:

1. the checked recovery theorem
   `boundary_value_recovery_forwardTube_of_flatRegular_from_bv` specialized at
   the canonical forward-cone direction and the theorem-2 boundary-functional
   package, producing
   `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery`;
2. the adjacent raw-boundary equality from
   `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` glued to that
   specialization, producing
   `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`.

Estimated Lean size:

1. theorem-2-specific boundary-value recovery specialization:
   `20-50` lines;
2. final adjacent canonical adapter/gluing theorem:
   `15-35` lines.

So the theorem-2 endgame above the raw-boundary theorem is now only a
`35-85` line specialization/adapter package, and that should stay explicit in
the docs.

## 15. The `d = 1` / forward-Jost subtlety must stay explicit

The locality blueprint should now record one genuine geometry subtlety that is
easy to lose sight of in pseudocode:

1. `ForwardJostSet d n hd` is defined by a condition on **every consecutive
   difference**,
2. the theorem-2 locality hypothesis only names one adjacent pair of indices,
3. so the implication
   "adjacent spacelike support hypothesis ⇒ support lies in `ForwardJostSet`"
   is **not** automatic at the theorem surface as currently written.

This matters most in `d = 1`, but the documentation should treat it as a
general theorem-shape issue, not as a one-dimensional anomaly.

### 15.1. What is safe to claim

The docs may safely claim:

1. if the support is already known to lie in an open edge `V` with
   `realEmbed '' V ⊆ ExtendedTube`,
   then the BHW pairing theorem can be applied directly;
2. if a stronger support theorem is proved that upgrades the locality support
   hypothesis to `ForwardJostSet` membership, then
   `forwardJostSet_subset_extendedTube` closes the geometry step;
3. the current theorem-2 route does **not** require us to prove the stronger
   forward-Jost statement first, because the pairing theorem
   `extendF_adjSwap_pairing_eq_of_distributional_local_commutativity`
   already accepts ET-support hypotheses as inputs.

### 15.2. What is *not* safe to claim

The docs should not claim, without a new theorem:

1. one adjacent spacelike-separation hypothesis automatically implies
   `ForwardJostSet` membership on the whole support;
2. the theorem-2 geometry step is already reduced to
   `forwardJostSet_subset_extendedTube` alone;
3. the `d = 1` case is a cosmetic special case of the same argument.

### 15.3. Honest theorem-slot split for the geometry step

So the later Lean port should separate the geometry package into two possible
routes.

#### Route A: stronger forward-Jost support theorem

```lean
lemma support_mem_forwardJost_of_adjacent_spacelike
    (f : SchwartzNPoint d n) (i : Fin n) (hi : i.val + 1 < n)
    (hsep : ∀ x, f.toFun x ≠ 0 ->
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) :
    ∀ x ∈ tsupport (f : NPointDomain d n → ℂ),
      x ∈ ForwardJostSet d n hd
```

This route is strongest but also most delicate, because the conclusion is a
statement about all consecutive differences.

#### Route B: direct ET-support theorem on the actual open edge

Important contract correction: Route B should **not** introduce a second
competing top-level theorem-slot vocabulary here. The endorsed Route-B package
names are still exactly
`choose_real_open_edge_for_adjacent_swap`,
`swapped_support_lies_in_swapped_open_edge`, and
`swapped_open_edge_embeds_in_extendedTube`.

So the direct-open-edge content should be read only as the mathematical shape
of those already-endorsed theorem slots:

```lean
lemma choose_real_open_edge_for_adjacent_swap
    (f : SchwartzNPoint d n) (i : Fin n) (hi : i.val + 1 < n)
    (hsep : ∀ x, f.toFun x ≠ 0 ->
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) :
    ∃ V : Set (NPointDomain d n),
      IsOpen V ∧
      tsupport (f : NPointDomain d n → ℂ) ⊆ V ∧
      (∀ x ∈ V, BHW.realEmbed x ∈ BHWCore.ExtendedTube d n)

lemma swapped_support_lies_in_swapped_open_edge
    ...

lemma swapped_open_edge_embeds_in_extendedTube
    ...
```

Route B is closer to the already-proved theorem surface in
`AdjacencyDistributional.lean`, because that file works directly with an open
real edge `V` and ET-support hypotheses.

### 15.4. Recommended route

The later implementation should prefer Route B unless a clean forward-Jost
support theorem is already available under an exact production name. That keeps
the locality proof closer to the actual existing BHW package:

1. choose/open an appropriate real edge `V`,
2. prove the support of `f` and the swapped support of `g` lie in `V`,
3. use the existing ET hypotheses accepted by the pairing theorem,
4. avoid overclaiming global `ForwardJostSet` membership.

This preference is now part of the theorem-2 contract, not a soft suggestion:

1. **Primary route**: Route B through an explicit real open edge `V` and ET
   support, because that is the theorem surface already consumed by
   `AdjacencyDistributional.lean`.
2. **Fallback route only**: Route A through `ForwardJostSet`, to be used only
   if a clean theorem upgrading the current hypothesis to global forward-Jost
   membership is actually proved under an exact production name.
3. the frontier theorem `bvt_F_swapCanonical_pairing` must be read as a thin
   consumer of the Route-B package order listed above; it is not allowed to
   absorb a raw geometry proof, a raw-boundary locality proof, and the
   canonical-shift adapter into one local endgame.

So if the later Lean port begins without any new geometric breakthrough, it
should start on Route B immediately. It should not spend time trying to rescue
Route A first.

### 15.4.1. Exact Route-B theorem package on the real open edge

Route B should itself be written as a small theorem package, not as the vague
instruction "pick a convenient open edge." The canonical top-level theorem-slot
vocabulary is the same one fixed earlier in this blueprint; do **not** rename it
again in this section.

So the later Lean file should target:

```lean
lemma choose_real_open_edge_for_adjacent_swap
    (f : SchwartzNPoint d n) (i : Fin n) (hi : i.val + 1 < n)
    (hsep : ∀ x, f.toFun x ≠ 0 ->
      MinkowskiSpace.AreSpacelikeSeparated d (x i) (x ⟨i.val + 1, hi⟩)) :
    ∃ V : Set (NPointDomain d n),
      IsOpen V ∧
      tsupport (f : NPointDomain d n → ℂ) ⊆ V ∧
      (∀ x ∈ V, BHW.realEmbed x ∈ BHWCore.ExtendedTube d n)

lemma swapped_support_lies_in_swapped_open_edge
    {V : Set (NPointDomain d n)}
    (f g : SchwartzNPoint d n) (i : Fin n) (hi : i.val + 1 < n)
    (hswap : ∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)))
    (hsupp : tsupport (f : NPointDomain d n → ℂ) ⊆ V) :
    tsupport (g : NPointDomain d n → ℂ) ⊆
      {x | (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ V}

lemma swapped_open_edge_embeds_in_extendedTube
    {V : Set (NPointDomain d n)}
    (i : Fin n) (hi : i.val + 1 < n)
    (hV : ∀ x ∈ V, BHW.realEmbed x ∈ BHWCore.ExtendedTube d n) :
    ∀ x ∈ {x | (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ V},
      BHW.realEmbed x ∈ BHWCore.ExtendedTube d n
```

Any finer-grained local cover lemmas used to prove those statements are
subordinate implementation helpers, not new contract-level Route-B theorem
surfaces.

This is the safest geometry route because it matches the current production
pairing theorem surface in `AdjacencyDistributional.lean` directly:

1. actual open real edge,
2. actual ET embedding of that edge,
3. support inclusion of both test functions into that edge.

### 15.4.2. Exact proof transcript for the primary Route-B geometry package

The later Lean file should implement Route B in the following explicit order.

1. Start from the support hypothesis on the adjacent pair.
2. Use the already-checked `Adjacency.lean :: exists_real_open_nhds_adjSwap`
   as the local compactness/open-neighborhood engine. That theorem already
   packages the local proof transcript:
   - openness of the adjacent spacelike region,
   - openness of ET membership under real embedding,
   - openness of swapped-ET membership,
   - and intersection of those three open conditions around a real witness.
3. Build the theorem-2-facing wrapper
   `choose_real_open_edge_for_adjacent_swap` by adding the missing theorem-2
   support-inclusion layer: cover `tsupport f` by such local neighborhoods and
   package the resulting open set `V` together with `tsupport f ⊆ V`.
4. Prove `swapped_support_lies_in_swapped_open_edge` as the pure support-transport
   step from the checked swap identity `g x = f (x ∘ swap)`.
5. Prove `swapped_open_edge_embeds_in_extendedTube` as the explicit transport of
   the ET witness on `V` to the swapped preimage edge.
6. Only then feed those ET-support statements to the checked distributional
   theorem `AdjacencyDistributional.lean ::
   extendF_adjSwap_pairing_eq_of_distributional_local_commutativity`.

The internal transcript of those three theorem-2-facing wrappers is now fixed
more sharply.

`choose_real_open_edge_for_adjacent_swap` should prove its conclusion in this
order:

1. take `x ∈ tsupport f`;
2. use `hsep x` together with `f.toFun x ≠ 0` to obtain the adjacent spacelike
   inequality at that support point;
3. apply the checked supplier `exists_real_open_nhds_adjSwap` to that specific
   support point, obtaining a local neighborhood `V_x` with all three local
   outputs already packaged:
   - `IsOpen V_x`,
   - adjacent spacelike persistence on `V_x`,
   - `realEmbed '' V_x ⊆ ExtendedTube`,
   - swapped `realEmbed '' (swap⁻¹(V_x)) ⊆ ExtendedTube`;
4. convert that pointwise family into a theorem-2 support neighborhood by the
   compactness of `tsupport f`: choose finitely many support points, take the
   union of the resulting `V_x`, and record that finite union as the theorem-2
   open edge `V`;
5. discharge the theorem conclusion fields in the order
   `IsOpen V` -> `tsupport f ⊆ V` -> `∀ x ∈ V, realEmbed x ∈ ExtendedTube`.

`swapped_support_lies_in_swapped_open_edge` is **only** a support theorem; it
must not re-prove ET geometry. Its proof transcript should be:

1. fix `x ∈ tsupport g`;
2. show `(x ∘ swap) ∈ tsupport f` by contradiction, using the checked pointwise
   swap identity `hswap` to transfer vanishing of `f` near `(x ∘ swap)` back to
   vanishing of `g` near `x`;
3. apply the already-proved support inclusion `hsupp` to conclude
   `(x ∘ swap) ∈ V`;
4. rewrite that as membership of `x` in the swapped preimage edge
   `{x | (x ∘ swap) ∈ V}`.

`swapped_open_edge_embeds_in_extendedTube` is then **only** the ET-transport
wrapper above `hV`; its transcript should be:

1. fix `x` in the swapped preimage edge;
2. unpack the preimage-edge hypothesis as `(x ∘ swap) ∈ V`;
3. apply the already-available ET witness `hV` at the point `(x ∘ swap)`;
4. rewrite the resulting statement back to the displayed target
   `realEmbed x ∈ ExtendedTube` using the checked swapped-ET clause already
   built into `exists_real_open_nhds_adjSwap` / the chosen theorem-2 edge.

This extra split matters because only the first wrapper uses compactness of the
support; the second is support transport only; the third is ET transport only.
Later Lean work should not blur those three tasks back into one opaque
`choose/open/swap` helper.

So the Route-B implementation skeleton should be read operationally as:

```lean
-- checked-present lower geometry helper already in Adjacency.lean
exists_real_open_nhds_adjSwap

-- still-missing theorem-2-facing wrappers to be built on top of it
choose_real_open_edge_for_adjacent_swap
swapped_support_lies_in_swapped_open_edge
swapped_open_edge_embeds_in_extendedTube
```

The older pseudocode helper names

```lean
local_spacelike_open_edge_around_support_point
compact_support_finite_open_edge_cover
finite_open_edge_union_embeds_in_extendedTube
```

should now be read only as possible *internal* proof fragments inside
`choose_real_open_edge_for_adjacent_swap`, not as a second competing theorem-slot
family. The checked tree already exposes `exists_real_open_nhds_adjSwap` as the
actual lower file-local supplier on `Adjacency.lean`, and the theorem-2 docs
should freeze that fact.

This is the actual proof mechanism that makes Route B preferable: it is local,
compact-support-based, and uses openness of the spacelike relation, rather
than a global combinatorial Jost-set upgrade.

### 15.5. Estimated Lean size for the subtlety-aware geometry package

1. Route-A forward-Jost theorem:
   `30-70` lines if true on the current theorem surface,
   possibly more if the theorem surface itself must be strengthened.
2. Route-B open-edge support package:
   `35-80` lines total across the two support lemmas.

The docs should therefore treat Route B as the safer implementation target
until Route A is proved honestly.
