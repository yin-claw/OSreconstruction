# Systematic Development Plan (OS Reconstruction Critical Path)

Last updated: 2026-03-11

This is the active execution plan for closing `sorry`s on the OS reconstruction path.
It supersedes the earlier BHW-first ordering.

## 1. Proof-Quality Policy (Hard Constraints)

1. No wrappers, no useless lemmas, no code bloat.
2. Every new lemma must either:
   - close a blocker directly, or
   - carry nontrivial reusable mathematical content needed downstream.
3. Do not add forwarding/repackaging lemmas that only rename existing statements.
4. Close `sorry`s with substantial proofs (not assumption padding or existential hiding).
5. Numerical checks are optional diagnostics; they are not required workflow gates.

## 2. Live Sorry Census

Counts verified with:
`rg -n '^\s*sorry\b' OSReconstruction --glob '*.lean'`

| Scope | Sorrys |
|---|---:|
| `OSReconstruction/Wightman` | 30 |
| `OSReconstruction/SCV` | 2 |
| `OSReconstruction/ComplexLieGroups` | 2 |
| `OSReconstruction/vNA` | 39 |
| **Total** | **73** |

## 3. Primary Priority Stack

### A) E -> R direction (`OSToWightman.lean`, 8 sorrys)

Clusters:
1. Root continuation blocker:
   - `schwinger_continuation_base_step`
2. Boundary-value existence:
   - `boundary_values_tempered`
3. Axiom transfer chain:
   - transfer of W0-W5-style properties through holomorphic extension + boundary values
4. Cluster property:
   - `bvt_cluster` and companion transport lemma

Live status:
- the OS quotient/Hilbert semigroup infrastructure is already built
- `OSLinearGrowthCondition` is already used upstream in proved production lemmas to get polynomial growth of Euclidean time-shift matrix elements and hence contraction
- rational-time identification with positive functional-calculus powers is in place
- positive-time continuity of `t ↦ CFC.nnrpow A t` is now in `vNA/Bochner/SemigroupRoots.lean`
- the remaining hard content is no longer generic semigroup packaging; it is the theorem-level bridge into analytic continuation and tempered boundary values

### B) R -> E wick-rotation submodules (10 sorrys total on the active path)

1. `SchwingerAxioms.lean`:
   - coincidence-singularity / zero-diagonal integrability
   - Euclidean reality / reflection
   - downstream cluster / OS=W term
2. `BHWTranslation.lean`:
   - PET overlap connectivity
3. `ForwardTubeLorentz.lean`:
   - slice polynomial growth
   - null exceptional set for PET entry

### C) Shared SCV infrastructure (2 sorrys total, but still load-bearing)

1. `LaplaceSchwartz.lean` is now sorry-free and contains the generic tempered
   boundary-value lemmas needed for `boundary_values_tempered`.
2. `PaleyWiener.lean` is sorry-free; no live multivariable Paley-Wiener theorem is
   on the immediate critical path.
3. `BochnerTubeTheorem.lean` (2) remains open, but it is no longer the first
   blocker to attack.

The honest remaining SCV-facing gap in the E -> R lane is not generic DCT or
integrability anymore; it is deriving the growth hypotheses (`hpoly`, `hunif`)
from the OS data.

## 4. Secondary / Standalone Blockers

1. `Wightman/Reconstruction/Main.lean`: `wightman_uniqueness` (1)
2. `Wightman/Reconstruction/GNSHilbertSpace.lean`: vacuum-uniqueness chain (1)
3. `Wightman/WightmanAxioms.lean`: 4 infrastructural sorrys
4. `Wightman/NuclearSpaces/*`: 7 sorrys (important but not critical-path)
5. `ComplexLieGroups/*`: 2 remaining BHW-permutation blockers (maintained, not current top lane)

## 5. Execution Order

1. Close `schwinger_continuation_base_step` in `OSToWightman.lean`.
2. Use the extracted SCV boundary-distribution lemmas to reduce
   `boundary_values_tempered` to the genuine OS-side growth inputs.
3. Extract the next reusable translation-growth lemma
   (`seminorm_translateSchwartz_le`) into SCV.
4. Close the transfer and cluster chain in `OSToWightman.lean`.
5. In parallel or next, attack the two independent R -> E roots in
   `SchwingerAxioms.lean`: coincidence-singularity control and Euclidean reality.
6. Finish final wiring (`wightman_uniqueness`, remaining `GNSHilbertSpace`, residual `WightmanAxioms` blockers).

## 6. Deprioritized Work (Unless It Unblocks the Above)

1. Most of `vNA/*`
2. Non-critical NuclearSpaces side development
3. Additional CLG refactors not required by active OS reconstruction blockers

## 7. Verification Commands

```bash
# module builds
lake build OSReconstruction.SCV
lake build OSReconstruction.Wightman

# blocker census
rg -n '^\s*sorry\b' OSReconstruction --glob '*.lean'
rg -n '^axiom\\s+' OSReconstruction --glob '*.lean'
```
