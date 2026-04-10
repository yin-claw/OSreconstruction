# Route 1 Translation Invariance: Axiom and Sorry Status

**Date**: 2026-03-16
**Branch**: `main` (merged Route 1 state)

## Summary

The Route 1 refactor replaces the logically false `D(c)` overlap-connectivity
approach to BHW translation invariance with an algebraically clean proof via
reduced difference coordinates. The main theorem `bhw_translation_invariant`
is now proved (no sorry) using the Identity Theorem: the Route 1 extension
agrees with the standard BHW extension on the forward tube, both are
holomorphic on the permuted extended tube, therefore they agree everywhere,
and translation invariance transfers algebraically.

On the merged path, this means `isPreconnected_baseFiber` is no longer needed
to prove `bhw_translation_invariant`. The remaining trust surface is the single
reduced-BHW axiom recorded below.

Global repository note: this file is Route-1-local, but the live tracked
production tree is no longer the older 3-axiom snapshot. The checked repo-wide
census used by `README.md` and the active proof-doc stack is now **6 explicit
axioms** on the tracked production tree, of which only **1** belongs to Route 1:
`BHWReducedExtension.lean :: reduced_bargmann_hall_wightman_of_input`.

The other tracked axioms are outside the Route-1 lane and should not be folded
back into its status accounting:
- the two functional-analysis axioms in `Wightman/WightmanAxioms.lean`
  (`schwartz_nuclear_extension`,
  `exists_continuousMultilinear_ofSeparatelyContinuous`),
- the remaining tracked axioms recorded in the live repo-wide census in
  `README.md` / `docs/openclaw_comprehensive_reading_note.md`.

So the operational meaning of this note is narrower: it certifies that the
Route-1 translation-invariance route still has exactly one Route-1 axiom, not
that the whole repository has only one or three axioms left.

### Current inventory

| File | Item | Type | Status |
|------|------|------|--------|
| `BHWReducedExtension.lean:932` | `reduced_bargmann_hall_wightman_of_input` | axiom | **Open** |
| `BHWReduced.lean` | `schwartzTranslationClassification` | ~~axiom~~ theorem | **Closed** (wired to `TranslationInvariantSchwartz.lean`) |
| `BHWTranslation.lean:1124` | `isPreconnected_baseFiber` | sorry | **Open** (pre-existing old-route residual; not needed on merged path) |

### What was eliminated in this session

| Item | Was | Now |
|------|-----|-----|
| `integral_realDiffCoord_change_variables` | axiom | **theorem** (Fubini + CLE measure-preservation) |
| `realDiffCoordCLE_symm_measurePreserving` | sorry | **theorem** (det = 1 via nilpotent charpoly) |
| integrability in `route1ReducedBoundaryIntegral_eq_absoluteBoundaryIntegral` | sorry | **proved** (`forward_tube_bv_integrable`) |
| `schwartzTranslationClassification` | axiom | **theorem** (wired to `TranslationInvariantSchwartz.lean` zero-mean decomposition) |

---

## Axiom 1: `reduced_bargmann_hall_wightman_of_input`

**File**: `BHWReducedExtension.lean:932`

**Statement**: Given a `Route1ReducedAnalyticInput` (holomorphic on the reduced
forward tube, Lorentz-covariant, with distributional boundary values), produce
a full reduced BHW extension: holomorphic on the reduced permuted extended tube,
agreeing on the reduced forward tube, Lorentz-invariant, permutation-invariant,
and unique by the identity theorem.

**Mathematical content**: This is the **Bargmann-Hall-Wightman theorem executed
natively in `(n-1)` reduced difference coordinates**, where permutations act
via `permOnReducedDiff` (the `A_{n-1}` root system reflection) rather than by
naive coordinate reordering.

### Why the absolute-to-reduced bridge is not yet formalized

The natural idea is: lift the reduced function to absolute coordinates, apply
the existing absolute BHW theorem, then project back. In this codebase, that
bridge is not yet available for two concrete reasons:

1. **The safe section fails geometrically.** The safe section
   `safeSection(eta) = (i*e_0, eta_1 + i*e_0, ...)` maps the reduced forward
   tube into the absolute forward tube. But it does NOT map the reduced PET
   into the absolute PET. Complex Lorentz boosts mix real and imaginary parts;
   the fixed basepoint `i*e_0` will be transformed into `Lambda^{-1}(i*e_0)`
   whose imaginary part generically points outside the forward cone. The safe
   section violently ejects points from the absolute domain of holomorphy.

2. **Arbitrary sections require translation invariance.** If you pick any
   `z in PET_abs` projecting to a given `eta in PET_red`, well-definedness of
   `F_ext_red(eta) := F_ext_abs(z)` requires `F_ext_abs(z + c) = F_ext_abs(z)`
   for all uniform translations `c`. But **this is exactly the theorem Route 1
   was built to prove**. You cannot use absolute translation invariance to
   construct the reduced BHW theorem, because you need the reduced BHW theorem
   to prove absolute translation invariance. Perfect logical ouroboros.

**Current verdict**: a direct converse-lift proof is not yet available in Lean.
The present implementation therefore axiomatizes the reduced theorem natively.
An absolute-to-reduced bridge remains a plausible future route once the PET
translation-descent machinery is formalized.

### Why Option 1 (native porting) is correct and feasible

The Edge of the Wedge theorem and the envelope of holomorphy must be executed
natively in the quotient space. This is exactly what Jost and Streater-Wightman
do mathematically. The existing absolute BHW proof in `BHWExtension.lean`
already contains the heaviest Lean machinery (abstract EotW, analytic
continuation along tubes, Lorentz sweeping).

Implementation-facing correction (2026-04-08): this Route-1 axiom note must not
be read as saying theorem 2 later closes by a generic “now do Jost/BHW” step.
On the live proof-doc route, the reduced BHW axiom is only the upstream reduced
permutation/continuation supplier. The theorem-2 locality lane downstream of
that axiom is frozen much more sharply in `docs/theorem2_locality_blueprint.md`:

1. Route-B adjacent-swap real-open-edge geometry on the checked
   `Adjacency.lean` package, anchored at
   `exists_real_open_nhds_adjSwap`;
2. an adjacent-only raw-boundary closure on the
   `AdjacencyDistributional.lean` / `BHWExtension.lean` seam, at the planned
   theorem slot
   `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`;
3. only then the theorem-2 canonical-shift sibling subsection in
   `OSToWightmanBoundaryValueLimits.lean`, in the explicit order
   `bvt_F_canonical_boundary_pairing_eq_from_bv_recovery`
   -> `bvt_F_adjacentSwapCanonical_pairing_from_raw_boundary_locality`
   -> `bvt_F_swapCanonical_pairing_of_adjacent_chain`; and the middle theorem's
   local proof transcript is frozen more sharply than this older note used to
   say: raw-boundary wrapper
   `bvt_F_adjacentSwap_boundary_pairing_eq_of_ET_support` first, recovery on the
   swapped (`g`) side second, recovery on the unswapped (`f`) side third,
   transitivity/symmetry closure fourth. The final adjacent-chain reducer may
   then consume only that adjacent canonical theorem plus explicit adjacent
   factorization data for `swap i j`; it may not reopen raw-boundary or
   recovery theorems.
4. only after that the thin frontier consumer
   `OSToWightmanBoundaryValues.lean :: bvt_F_swapCanonical_pairing`.

Two non-circularity cautions belong here too, because this older status note is
otherwise easy to misread as an instruction to jump straight to a checked public
BHW wrapper:
- theorem 2 must **not** be documented as a direct use of
  `WickRotation/BHWExtension.lean :: W_analytic_swap_boundary_pairing_eq`,
  because at `W := bvt_W OS lgc` that theorem still asks for the global input
  `IsLocallyCommutativeWeak d W`;
- theorem 2 also must **not** stop at the lower checked theorem
  `AdjacencyDistributional.lean ::
  extendF_adjSwap_pairing_eq_of_distributional_local_commutativity`, because
  that lower theorem still asks for the same global locality input.

So the operational role of the Route-1 reduced BHW axiom is narrower than a
historical Jost/BHW slogan: it supplies the reduced continuation side, but it
does not erase the later theorem-2 open-edge / raw-boundary / canonical-shift
split that Lean still has to implement explicitly.

Porting the permutation flow to reduced coordinates is geometrically cleaner
than the absolute version:

- **Locality is scalar**: In reduced coordinates, physical locality for adjacent
  points `k, k+1` is just `xi_k^2 < 0` (spacelike separation), a single
  scalar condition.

- **Clean swap action**: The adjacent transposition `sigma_k` acts on differences
  via `permOnReducedDiff`: `xi_k -> -xi_k` and `xi_{k+1} -> xi_{k+1} + xi_k`.
  This is the `A_{n-1}` root system reflection.

- **Spectator tubes survive**: When crossing the real Jost boundary
  `Im(xi_k) -> 0`, the neighboring variables transform to
  `Im(xi_{k+1}) + 0 = Im(xi_{k+1})`. They perfectly maintain
  `Im(xi_{j != k}) in V+`. The tubes glue together flawlessly across the
  boundary without knocking spectator variables out of the forward light cone.

### Concrete steps to eliminate this axiom

1. **Reduced open-edge geometry package**: define the reduced adjacent-swap real
   boundary region and its open neighborhoods in the reduced coordinates, in a
   way that matches the later theorem-2 Route-B geometry contract rather than a
   vague “Jost points somewhere” description.

2. **Reduced raw-boundary agreement on that edge**: prove the reduced boundary
   values agree across this specific adjacent spacelike seam, so the reduced
   analogue of the later theorem-2 raw-boundary package is explicit before any
   envelope/gluing step.

3. **Reduced Edge of the Wedge**: apply the existing abstract EotW theorem
   across that chosen edge to glue `FT_red` and `sigma_k(FT_red)`.

4. **Sweep and induct**: apply the complex Lorentz group to sweep the glued
   domain, and induct over `S_n` (the permutation group).

5. **Document the handoff boundary explicitly**: when this axiom is eventually
   replaced by a theorem, its downstream consumer docs must still preserve the
   theorem-2 execution split
   `Adjacency.lean` Route-B geometry
   -> `adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`
   -> canonical-shift package in `OSToWightmanBoundaryValueLimits.lean`
   -> `bvt_F_swapCanonical_pairing`; and that middle package must keep its
   internal ownership/transcript boundary explicit: `BHWExtension.lean` owns the
   adjacent raw-boundary wrapper, `OSToWightmanBoundaryValueLimits.lean` owns
   the canonical-direction recovery wrapper plus the adjacent-canonical and
   adjacent-chain theorems, and `OSToWightmanBoundaryValues.lean` owns only the
   final thin frontier consumer. Eliminating the Route-1 axiom does not license
   collapsing those later theorem-2 layers into one opaque “BHW done” step.

**Estimated difficulty**: Substantial but bounded. The abstract EotW and
Lorentz-sweeping machinery already exists; the new work is defining the reduced
open-edge geometry and wiring the boundary-value argument without blurring the
later theorem-2 file/layer split.

See also `docs/reduced_bhw_bridge_and_numerics.md` for the intended bridge and
for the numerical diagnostics that support the reduced-coordinate geometry.

---

## ~~Axiom 2~~ (CLOSED): `schwartzTranslationClassification`

**File**: `BHWReduced.lean:51`
**Status**: **Eliminated** — now a theorem, wired to `TranslationInvariantSchwartz.lean`.

**Statement**: Every translation-invariant continuous linear functional on
spacetime Schwartz space `S(R^{d+1})` is a scalar multiple of the Lebesgue
integral.

**How it was proved**: The proof in `TranslationInvariantSchwartz.lean` (~2350
lines) uses a zero-mean decomposition approach rather than the Fourier route
originally anticipated. The key insight is that any Schwartz function can be
decomposed into a zero-mean part (in the range of a line-derivative operator)
plus a multiple of a fixed reference function with integral 1. A
translation-invariant functional vanishes on the zero-mean part, leaving only
the scalar multiple of the integral.

**Role in Route 1**: Ensures the reduced Wightman functional is independent of
the choice of normalized basepoint cutoff `chi`. The theorem
`reducedWightman_eq_of_cutoff` uses it to show that any two cutoffs with
integral 1 produce the same reduced functional.

---

## Residual Sorry: `isPreconnected_baseFiber`

**File**: `BHWTranslation.lean:1124`

**Statement**: The base fiber `{z_0 in C^{d+1} : Im(z_0) in V+ and
(z_0, zeta_1, ..., zeta_m) in PET}` is preconnected.

**Status**: Pre-existing sorry, not introduced by Route 1. On the merged path
it is no longer needed for translation invariance and is not part of the active
`R -> E` proof route. It remains as a geometric cleanup target for the old
base-fiber argument.

---

## Strategic Assessment

The Route 1 refactor has achieved its structural goal: **translation invariance
is now proved on the merged path without using any `sorry` theorem**, using a
clean algebraic argument via reduced difference coordinates and the identity
theorem. The remaining technical debt on that path is quarantined into exactly
**one axiom**:

1. **`reduced_bargmann_hall_wightman_of_input`**: The correct reduced-coordinate
   BHW theorem. This is the *only* path forward (the converse-lift alternative
   is logically circular). It requires porting the permutation flow to reduced
   coordinates, which is geometrically cleaner than the absolute version but
   still substantial SCV work.

~~2. **`schwartzTranslationClassification`**: Eliminated — now proved via
zero-mean decomposition in `TranslationInvariantSchwartz.lean`.~~

The sole remaining axiom is mathematically a textbook-level reduced-coordinate
Bargmann-Hall-Wightman statement. It has been successfully isolated from the
downstream theory, with the intended future bridge documented separately. But
this should now be read with the live theorem-2 proof-doc contract in mind:
removing the Route-1 axiom would unblock only the **reduced continuation /
permutation supplier lane**, not the entire theorem-2 locality closure in one
shot.

More explicitly, the project is unblocked to proceed with the reduced BHW /
permutation geometry side, but the later locality implementation still must run
through the frozen Route-B adjacent-swap package, the planned adjacent-only
raw-boundary theorem slot
`adjacent_boundary_pairing_eq_of_openEdgeBoundaryCompatibility`, and the
canonical-shift / adjacent-chain layer before it reaches the frontier theorem
`bvt_F_swapCanonical_pairing`. So this note should not be cited as evidence
that theorem 2 becomes a generic “Jost's theorem is available, therefore
locality follows” step.

The Route 1 architecture correctly maps the boundary between what can be proved
algebraically (translation invariance, via difference coordinates and the
identity theorem) and what requires native SCV geometry (the reduced BHW
envelope of holomorphy). The further theorem-2 documentation work now makes the
next boundary explicit as well: reduced BHW support belongs upstream of, not in
place of, the later open-edge / raw-boundary / canonical-shift locality stack.
