# OSreconstruction — status report and current sorry frontiers

Date: 2026-04-01
Repo state studied:
- local `main = origin/main = upstream/main = 078edde`
- working branch reset to the same tracked state before this review

## Executive summary

The project has made real progress since the earlier March blocker picture, especially on the `k = 2` VI.1 frontier and on the boundary-values interface. But the core E→R theorem is still not close to being finished.

The current shape is:

- the old `k = 2` frontiers that consumed a lot of local work in late March have now been compressed away upstream;
- the active E→R route is now dominated by
  1. the general-`k` continuation theorem(s) in `OSToWightman.lean`, and
  2. the boundary-value transfer layer in `OSToWightmanBoundaryValues.lean`;
- the generic SCV `uniform_bound` concern no longer blocks the active OS boundary-value path because the interface was refactored to a weaker boundary-value datum theorem;
- the `k = 2` VI.1 frontier now has only one remaining `sorry`, and it is explicitly marked as a legacy probe-route theorem rather than the active shortest path.

So the project is in a better state architecturally, but the two most serious remaining fronts are still:

1. **general-`k` OS→Wightman continuation**
2. **transport of the Wightman axioms through the boundary-value package**

A concise way to state the current status is:

> The project has successfully eliminated many local and intermediate analytic seams, but what remains are now the central structural theorems rather than peripheral infrastructure gaps.

---

## 0. One-page frontier table

### Active shortest-path frontiers

| Priority | File | Current live content | Why it matters |
|---|---|---|---|
| 1 | `WickRotation/OSToWightman.lean` | general-`k` continuation witness / kernel package / extension | Root E→R continuation content |
| 2 | `WickRotation/OSToWightmanBoundaryValues.lean` | boundary-value datum + Wightman axiom transfer (`bv_*`, `bvt_cluster`) | Converts continuation into an honest Wightman package |

### Important but not first-on-path

| File | Current content | Status judgment |
|---|---|---|
| `WickRotation/SchwingerAxioms.lean` | Euclidean reality / cluster-side remaining theorems | important downstream, not first E→R blocker |
| `WickRotation/ForwardTubeLorentz.lean` | `wickRotation_not_in_PET_null` | significant geometric theorem, but not first current target |
| `WickRotation/BHWTranslation.lean` | `isPreconnected_baseFiber` | old-route residual theorem, de-prioritized |
| `Reconstruction/GNSHilbertSpace.lean` | 3 GNS/operator sorrys | secondary to analyticity lane |
| `Reconstruction/Main.lean` | `wightman_uniqueness` | secondary / operator-theoretic lane |
| `Wightman/NuclearSpaces/*` | 7 sorrys total | not on shortest current OS reconstruction path |

---

## 0.5. Dependency graph (project-wide and lane-specific)

This section is intentionally schematic rather than pretending to be a complete import DAG dump. The goal is to show the **mathematical** dependency graph and the current **critical paths**.

### A. High-level project graph

```text
WightmanFunctions / WightmanAxioms
    ├── Analytic continuation / forward-tube infrastructure
    │     ├── ForwardTubeLorentz
    │     ├── BHWReduced / BHWReducedExtension / BHWTranslationCore
    │     ├── WickRotationBridge / BaseFiberInflation / HermitianBoundaryPairing
    │     └── SchwingerTemperedness / SchwingerAxioms
    │
    ├── OS → Wightman lane (E→R)
    │     ├── OSToWightmanBase
    │     ├── OSToWightmanK2Density
    │     ├── OSToWightmanK2BaseStep
    │     ├── K2VI1.Frontier
    │     ├── OSToWightman
    │     └── OSToWightmanBoundaryValues
    │
    └── Reconstruction / GNS lane
          ├── GNSConstruction
          ├── GNSHilbertSpace
          ├── PoincareAction / PoincareRep
          └── Reconstruction.Main
```

### B. Import-level WickRotation spine

The import spine recorded in `WickRotation.lean` is:

```text
OSToWightmanBase
OSToWightmanSpatialMomentum
OSToWightmanK2Density
OSToWightmanK2BaseStep
K2VI1.Frontier
OSToWightman
OSToWightmanBoundaryValues
BHWReduced
BHWTranslationCore
BHWReducedExtension
HermitianBoundaryPairing
BaseFiberInflation
WickRotationBridge
```

Interpretation:
- the `k = 2` density/base-step/frontier files are now support layers feeding `OSToWightman.lean`;
- `OSToWightmanBoundaryValues.lean` is the active conversion of continuation data into Wightman data;
- the BHW / translation / bridge files remain part of the larger Wick-rotation ecosystem but are no longer the shortest active front.

### C. E→R critical path (current best reconstruction)

```text
OS axioms + linear growth
    ↓
OSToWightmanBase
    ↓
OSToWightmanK2Density + OSToWightmanK2BaseStep + K2VI1.Frontier
    ↓
OSToWightman.lean
    ├── exists_acrOne_productTensor_witness        (root blocker)
    ├── acrOne_productTensor_witness_euclidKernelPackage
    └── dense extension to ZeroDiagonalSchwartz
    ↓
full_analytic_continuation / boundary-value datum
    ↓
OSToWightmanBoundaryValues.lean
    ├── boundary_values_tempered
    ├── bvt_lorentz_covariant
    ├── bvt_locally_commutative
    ├── bvt_positive_definite
    ├── bvt_hermitian
    └── bvt_cluster
    ↓
os_to_wightman_full
```

Current live blockers on this path:
- `OSToWightman.lean` — 3 sorrys, especially `exists_acrOne_productTensor_witness`
- `OSToWightmanBoundaryValues.lean` — 5 sorrys (`bv_*`, `bvt_cluster` front)

### D. R→E critical path

```text
WightmanFunctions
    ↓
Forward-tube/BHW analytic continuation infrastructure
    ↓
SchwingerTemperedness
    ↓
SchwingerAxioms.lean
    ├── translation / rotation / reflection / permutation side
    ├── Euclidean reality
    └── cluster-related Euclidean statements
    ↓
constructZeroDiagonalSchwingerFunctions / constructed OS family
    ↓
wightman_to_os / wightman_to_os_full
```

Current visible blockers most relevant to this lane:
- `SchwingerAxioms.lean` — 2 sorrys
- `ForwardTubeLorentz.lean` — 1 sorry
- some BHW/translation-route residuals remain, but are not currently the shortest active seam

### E. GNS / operator-theoretic critical path

```text
WightmanFunctions
    ↓
GNSConstruction
    ↓
PreHilbertSpace quotient / algebraic lifting
    ↓
GNSHilbertSpace.lean
    ├── inner-product / normed-space completion details
    ├── vacuum / field operators on completion
    └── Hilbert-space representation package
    ↓
Reconstruction.Main
    ├── wightman_reconstruction
    └── wightman_uniqueness
```

Current visible blockers most relevant to this lane:
- `GNSHilbertSpace.lean` — 3 sorrys
- `Reconstruction/Main.lean` — `wightman_uniqueness`

### F. How the three lanes interact

```text
R→E lane:   Wightman → Euclidean Schwinger family
E→R lane:   OS axioms + growth → Wightman family
GNS lane:   Wightman family → Hilbert-space QFT reconstruction
```

These are not interchangeable tasks.

- R→E is about analytic continuation and Euclidean-side axioms.
- E→R is about continuation from OS data and boundary-value reconstruction.
- GNS is about operator/Hilbert-space realization after Wightman data exist.

The current repo is healthiest when these are kept conceptually separate.

---

## 1. Current sorry census

Direct tactic-hole count (`^[[:space:]]*sorry([[:space:]]|$)`):

- `OSReconstruction/Wightman`: **26**
- `OSReconstruction/SCV`: **3**
- `OSReconstruction/ComplexLieGroups`: **2**
- `OSReconstruction/vNA`: **36**
- **whole project**: **67**

Compared to the older March note, this is a real reduction.

### Immediate interpretation

- The Wightman/Reconstruction lane is still the main mathematical pressure point.
- The SCV side is now small enough that it is not the dominant sorry surface by count.
- The vNA side still has many sorrys, but this is not the active critical path for the OS analyticity work.

### Sorry surface inside `OSReconstruction/Wightman`

By file, the current direct sorry surface is:

- `WickRotation/OSToWightmanBoundaryValues.lean` — **5**
- `NuclearSpaces/BochnerMinlos.lean` — **5**
- `WickRotation/OSToWightman.lean` — **3**
- `Reconstruction/GNSHilbertSpace.lean` — **3**
- `WickRotation/SchwingerAxioms.lean` — **2**
- `NuclearSpaces/NuclearSpace.lean` — **2**
- `WickRotation/K2VI1/Frontier.lean` — **1**
- `WickRotation/ForwardTubeLorentz.lean` — **1**
- `WickRotation/BHWTranslation.lean` — **1**
- `Reconstruction/Main.lean` — **1**

This breakdown matters because the raw count alone hides the fact that the active shortest path is now concentrated in a very small number of files.

---

## 2. Main split in the project

The split in `Wightman/Reconstruction/Main.lean` is still the correct way to think about the project.

There are two qualitatively different lanes:

### A. Analyticity / Wick-rotation lane
This is the active OS reconstruction lane.

Main theorem surfaces:
- `wightman_to_os`
- `os_to_wightman`

Critical files:
- `WickRotation/OSToWightman.lean`
- `WickRotation/OSToWightmanBoundaryValues.lean`
- `WickRotation/ForwardTubeLorentz.lean`
- `WickRotation/SchwingerAxioms.lean`
- `WickRotation/BHWTranslation.lean`
- plus smaller SCV support

### B. Operator / GNS lane
Main theorem surfaces:
- `wightman_reconstruction`
- `wightman_uniqueness`

Critical files:
- `Reconstruction/GNSHilbertSpace.lean`
- `Reconstruction/Main.lean`
- later vNA/Stone-theorem-type infrastructure

This split matters because not all remaining sorrys are equally important.

---

## 3. Current active frontiers on the OS analyticity lane

## 3.1. `OSToWightman.lean` — general-`k` continuation remains a root blocker

Current direct sorrys in this file:
- line `56`
- line `199`
- line `366`

From the source, these are still the real continuation block:

### `exists_acrOne_productTensor_witness`
This is the first serious root theorem.

It asks for a scalar holomorphic witness on `AnalyticContinuationRegion d k 1` with:
- Euclidean pairing reproducing `OS.S k` on admissible product tensors,
- permutation invariance,
- translation invariance,
- polynomial growth.

This is still exactly the “OS II one-slice / Osgood” type theorem.

### `acrOne_productTensor_witness_euclidKernelPackage`
This is the measurable polynomial-kernel package extracted from the witness.

### A density step / extension step
The file now has a fairly refined decomposition:
- product-tensor witness
- Euclidean kernel package
- density-based extension to all `ZeroDiagonalSchwartz`

This is conceptually good. But the hard continuation content is still concentrated in this file.

### Assessment
This remains a **root blocker**, not a downstream formality.

The `k = 2` machinery is now more of a proof-of-concept / support layer. The real unclosed general theorem is back in full view here.

---

## 3.2. `OSToWightmanBoundaryValues.lean` — the active boundary-value surface

Current direct sorrys in this file:
- `1070`
- `1096`
- `1110`
- `1133`
- `1151`

These are now the current Phase-4 blockers on the boundary-value side.

### Important architectural update
The old blocker
- `full_analytic_continuation_flat_tempered_package`

is gone from the active path.

It has been replaced by the weaker theorem:
- `full_analytic_continuation_boundaryValueData`

and the helper
- `forwardTube_boundaryValueData_of_polyGrowth`

So the boundary-values lane no longer tries to route through the stronger generic SCV tempered FL package.

That is a good change.

### Current sorry front
The remaining sorrys are now exactly the transfer layer:

- `bvt_lorentz_covariant`
- `bvt_locally_commutative`
- `bvt_positive_definite`
- `bvt_hermitian`
- `bvt_cluster`

(with helper pairing theorems embedded just above them)

So once `boundary_values_tempered` exists, the remaining active tasks are the symmetry / positivity / cluster transport theorems.

### Exact interpretation
This file is no longer blocked by the old generic tempered-package mismatch. It is now blocked by a better question:

> given the continuous boundary-value datum for the chosen continuation, can one transport the Wightman axioms through the boundary-value limit?

That is a more central and more mathematically honest frontier than the earlier `hunif`-style package seam.

### Assessment
This file is now much more honest than before:
- it is no longer blocked by a dubious generic `hunif` style package;
- it is blocked by the actual Wightman-axiom transport layer.

That is progress.

---

## 3.3. `K2VI1/Frontier.lean` — no longer an active main blocker

Current direct sorrys in the file:
- line `133`

This theorem is explicitly commented as a legacy probe-route seam.

The practical meaning is:
- the long sequence of late-March local/frontier blockers has now largely been resolved or compressed away upstream;
- the `k = 2` VI.1 support program is no longer the main active bottleneck of the OS path.

### Assessment
This is one of the strongest signs of progress in the repo.

What was previously a whole frontier of live blocking sorrys has now been reduced to a single residual theorem that is not on the shortest active route.

---

## 3.4. `ForwardTubeLorentz.lean`

Current direct sorry:
- `wickRotation_not_in_PET_null` at line `942`

This is the measure-zero statement that almost every Euclidean Wick-rotated configuration lands in the permuted extended tube.

This is mathematically important, but it is not the first thing I would attack next unless it is shown to block a concrete active theorem immediately.

---

## 3.5. `BHWTranslation.lean`

Current direct sorry:
- `isPreconnected_baseFiber` at line `1127`

This remains the old-route geometric connectedness theorem for base fibers.

However, by the repo’s own comments and the merged Route 1 logic, this is no longer the preferred active route.

### Assessment
This should remain de-prioritized unless some new upstream theorem revives it as necessary.

---

## 3.6. `SchwingerAxioms.lean`

Current direct sorrys:
- line `2363`
- line `3578`

This is still part of the R→E / Euclidean-side downstream picture:
- Euclidean reality / reflection,
- cluster-related boundary identities.

This remains important, but it is not the first E→R blocker.

---

## 4. Current GNS / operator-theoretic surface

Current direct sorrys outside the analytic lane:

### `Reconstruction/Main.lean`
- `wightman_uniqueness` at line `82`

### `Reconstruction/GNSHilbertSpace.lean`
- lines `840`, `901`, `993`

These are real remaining gaps, but they are not the current shortest path to advancing `os_to_wightman`.

### Assessment
These should still stay secondary to the analyticity lane.

---

## 4.5. Nuclear-space side branch

The nuclear-space files still have a visible sorry surface:

- `Wightman/NuclearSpaces/BochnerMinlos.lean` — **5**
- `Wightman/NuclearSpaces/NuclearSpace.lean` — **2**

These are mathematically serious in their own right, but based on the current theorem wiring they do **not** appear on the shortest active `os_to_wightman` path.

So the correct status is:
- important side-development,
- not immediate critical-path work for the OS analyticity route.

---

## 5. Current critical path assessment

Given the current source state, the active shortest OS reconstruction path looks like this:

1. **General-`k` continuation theorem in `OSToWightman.lean`**
   - especially `exists_acrOne_productTensor_witness`

2. **Boundary-value datum / transfer layer in `OSToWightmanBoundaryValues.lean`**
   - `boundary_values_tempered` now has the right shape
   - the remaining real work is the transport of the Wightman axioms

3. Downstream Euclidean/Schwinger-side theorems
   - `SchwingerAxioms.lean`
   - `ForwardTubeLorentz.lean`
   - Route 1 geometry only if revived

The key shift from late March is:

> the `k = 2` frontier is no longer the main active blocker;
> the project has returned to the more conceptually central general-`k` continuation and transfer theorems.

---

## 6. Current status of the issue-48 line

This is important enough to record explicitly.

The earlier issue about
- `HasFourierLaplaceReprTempered.uniform_bound`

is **no longer the active OS boundary-values blocker**.

Why:
- the repo now routes `boundary_values_tempered` through a weaker boundary-value datum theorem,
- not through the old full tempered FL package.

So the generic SCV concern remains a library-design issue, but it is no longer the main reason the OS reconstruction path is blocked.

### Assessment
This is a healthy architectural improvement.

---

## 7. How close is the project?

## Good news
Compared to the earlier March picture:
- the sorry count is down,
- the `k = 2` frontier has been dramatically reduced,
- the boundary-values interface is cleaner and more honest,
- the old fake/improper detours have been reduced.

## Bad news
The project is still **not especially close** to completing `os_to_wightman`.

Why:
- the remaining blockers are now fewer, but more conceptually central;
- the general-`k` continuation theorem is still a real theorem, not a bookkeeping task;
- the remaining boundary-value transfer theorems encode genuine structure, not just wrappers.

So the right assessment is:

> **architecturally much healthier, mathematically still some distance from completion.**

---

## 8. Recommendations for next steps

## Recommendation 1 — prioritize `OSToWightman.lean`

If local work resumes, the correct theorem to attack is no longer a `k = 2` frontier micro-seam.

It is:
- `exists_acrOne_productTensor_witness`

Reason:
- it is back to being the first real root continuation theorem,
- and the rest of the OS path depends on getting such a witness in general `k`.

## Recommendation 2 — treat `OSToWightmanBoundaryValues.lean` as the second main front

Once the continuation witness data are in hand, the next active work should be:
- the remaining `bv_*` transfer theorems,
- then `bvt_cluster`.

This file now has the right interface shape; local work here would not be wasted in the same way as some of the late-March frontier work was.

## Recommendation 3 — keep `K2VI1/Frontier.lean` de-prioritized

Unless the proof of `exists_acrOne_productTensor_witness` explicitly requires a resurrection of the probe route, there is little reason to return active effort to the `k = 2` frontier now.

## Recommendation 4 — continue to separate:
- proof progress,
- theorem-graph refactor,
- and upstream supersession

This remains crucial. The repo has moved quickly enough that local work on the wrong seam can become stale fast.

---

## 9. Final verdict

The project is in a better state than it was a few days ago.

### Strong positive signs
- `k = 2` VI.1 frontier largely compressed away
- cleaner boundary-value interface
- smaller overall sorry surface
- more honest separation between active and legacy routes

### Current real frontiers
The current active sorry frontiers are now concentrated in:

1. `OSToWightman.lean`
   - general-`k` continuation witness / kernel package / extension

2. `OSToWightmanBoundaryValues.lean`
   - boundary-value transfer of the Wightman axioms

3. secondary but still real:
   - `SchwingerAxioms.lean`
   - `ForwardTubeLorentz.lean`
   - `wightman_uniqueness`
   - GNS operator-theoretic sorrys

So the concise summary is:

> **The project has advanced from “many local frontiers” to “fewer, more central theorems.”**
> 
> **That is progress — but the remaining theorems are exactly the hard conceptual ones.**
