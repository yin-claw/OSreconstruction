# Sorries and Axioms in the GNS Pipeline

This document catalogs every `sorry` and `axiom` that the Wightman reconstruction
theorem depends on through the GNS construction, evaluates their importance, and
estimates their difficulty.

## Scope

The **GNS pipeline** is the chain:

```
Core.lean  (WightmanFunctions, BorchersSequence, WightmanInnerProduct, PreHilbertSpace)
  -> PoincareAction.lean  (Poincare action on Borchers sequences)
  -> PoincareRep.lean      (inner product preservation)
  -> GNSConstruction.lean  (gns_reproduces_wightman, vacuum_normalized)
  -> GNSHilbertSpace.lean  (algebraic instances, completion, gnsQFT, wightman_reconstruction')
  -> Main.lean             (wightman_reconstruction, wightman_uniqueness)
```

The upstream dependency `WightmanAxioms.lean` defines `WightmanQFT` and contains
two axioms that the GNS output type depends on, so those are included too.

Checked-tree ownership clarification for this clone:

1. the repo contains a live checked `OSReconstruction/Wightman/NuclearSpaces/`
   subtree (`NuclearSpace.lean`, `SchwartzNuclear.lean`,
   `GaussianFieldBridge.lean`, `BochnerMinlos.lean`, `EuclideanMeasure.lean`,
   `ComplexSchwartz.lean`, `Helpers/PositiveDefiniteKernels.lean`,
   `NuclearOperator.lean`);
2. the reconstruction-critical downstream consumer surface is nevertheless still
   the pair of axioms exported from `Wightman/WightmanAxioms.lean`
   (`schwartz_nuclear_extension`,
   `exists_continuousMultilinear_ofSeparatelyContinuous`);
3. the honest open documentation problem is therefore an **integration split**,
   not the absence of any checked nuclear-support lane. Later Lean work must
   keep separate:
   - checked local support files under `Wightman/NuclearSpaces/*`,
   - downstream axiom/theorem surfaces already consumed by the GNS pipeline,
   - and any remaining import / wrapper / bridge work needed to connect them;
4. a direct checked-tree scan currently finds **7** local `sorry`s in the
   checked `Wightman/NuclearSpaces/*` subtree (`NuclearSpace.lean`: 2,
   `BochnerMinlos.lean`: 5), and those support-lane holes are already included
   in the headline repo-wide **60**-sorry whole-project census. The live
   proof-doc stack still tracks the NuclearSpaces lane separately, but only as
   an ownership/readout distinction rather than as an exception to the
   whole-project count; any narrower auxiliary census must be labeled
   explicitly;
5. the GNS implementation order is now frozen more sharply: local theorem work
   closes first in the checked `NuclearSpaces/*` files, then an explicit
   bridge/re-export layer replaces the downstream `WightmanAxioms.lean` axiom
   surfaces, and only then may `gns_cyclicity` or other GNS consumers use the
   repaired exported theorem surface. No GNS proof step may bypass that bridge
   by importing local support theorems ad hoc.

For the GNS lane, that means the implementation contract is:

1. local theorem work may happen in the checked `Wightman/NuclearSpaces/*`
   files;
2. reconstruction-facing consumers still read the theorem surface from
   `Wightman/WightmanAxioms.lean`;
3. any import/re-export replacement of those axioms is bridge work and should
   be tracked explicitly as such, not hidden as if `gns_cyclicity` already had
   direct local NuclearSpaces ownership;
4. `gns_cyclicity` itself is a downstream consumer only, not an owner of the
   nuclearity/separate-continuity bridge package.

---

## Summary

| ID | Name | Kind | File | Status |
|----|------|------|------|--------|
| A1 | `schwartz_nuclear_extension` | axiom | WightmanAxioms.lean:342 | On critical path (transitive) |
| A2 | `exists_continuousMultilinear_ofSeparatelyContinuous` | axiom | WightmanAxioms.lean:504 | On critical path (transitive) |
| S1a | `continuous_translate_npoint_schwartz` | theorem (implemented) | GNSHilbertSpace.lean:1005 | First translation-continuity owner slot |
| S1b | `gns_stronglyContinuous_preHilbert` | theorem (implemented) | GNSHilbertSpace.lean:1062 | Second strong-continuity owner slot |
| S1c | `gns_matrix_coefficient_holomorphic_axiom` | sorry | GNSHilbertSpace.lean:1249 | Only remaining spectrum-bridge hole |
| S2 | `gns_cyclicity` | sorry | GNSHilbertSpace.lean:1643 | First direct GNS consumer of the downstream nuclear surfaces |
| S4 | `wightman_uniqueness` | sorry | Main.lean:74 | Pure downstream consumer only: `gnsQFT` + cyclicity in, then the fixed Main-file queue `cyclicWordVector/cyclicWordSpan -> cyclicWordVector_inner_cyclicWordVector -> uniquenessPreMap -> uniquenessPreMap_inner_formula -> uniquenessPreMap_null_of_null -> uniquenessDenseMap -> uniquenessDenseMap_inner_preserving -> uniquenessDenseMap_norm_preserving -> uniquenessDenseMap_isometry -> cyclicWord_in_range_of_uniquenessDenseMap -> cyclicWordSpan_le_range_uniquenessDenseMap -> uniquenessDenseMap_denseRange -> uniquenessDenseMap_extends_to_unitary -> uniquenessUnitary_maps_vacuum -> uniquenessUnitary_intertwines_field_on_cyclic_core -> cyclicWordSpan_is_field_core -> uniquenessUnitary_intertwines_field -> wightman_uniqueness` out; source-check literal ownership too: in the current repo there is no separate checked uniqueness-helper Lean module under `Wightman/Reconstruction/`, so this helper queue is documentation-owned until a real support file is created. Physical insertion contract is frozen too: either create the queue directly in `Main.lean` above `:74`, or create one explicitly named new helper module under `Wightman/Reconstruction/` and move one contiguous theorem block there with synchronized imports/docs; scattering the queue across unrelated existing reconstruction files is out of contract |

**Formerly open, now proved:**

| ID | Name | Resolution |
|----|------|------------|
| S1 | `gns_spectrum_condition` | Decomposed into `MatrixElementSpectralCondition`; proved modulo S1a, S1b, S1c |
| S3 | `gns_vacuum_unique_of_poincare_invariant` | **Fully proved** via cluster decomposition |

**Core.lean, PoincareAction.lean, PoincareRep.lean, GNSConstruction.lean**: all clean (no sorries or axioms).

---

## Axioms (declared with `axiom`, no proof)

### A1. `schwartz_nuclear_extension`

**Current downstream consumer surface:** `WightmanAxioms.lean:342`

**Checked support lane cross-reference:**
- `Wightman/NuclearSpaces/NuclearSpace.lean`
- `Wightman/NuclearSpaces/SchwartzNuclear.lean`
- `Wightman/NuclearSpaces/GaussianFieldBridge.lean`
- `Wightman/NuclearSpaces/BochnerMinlos.lean`

```lean
axiom schwartz_nuclear_extension (d n : ℕ)
    (Phi : ContinuousMultilinearMap ℂ
      (fun _ : Fin n => SchwartzMap (Fin (d + 1) -> ℝ) ℂ) ℂ) :
    ∃! (W : SchwartzMap (Fin n -> Fin (d + 1) -> ℝ) ℂ →L[ℂ] ℂ),
      ∀ fs, W (SchwartzMap.productTensor fs) = Phi fs
```

**What it says:** The Schwartz nuclear (kernel) theorem: any jointly continuous
multilinear functional on a product of Schwartz spaces extends uniquely to a
continuous linear functional on the joint Schwartz space S(R^{nd}).

**How it enters the GNS pipeline:** Used in the proof of
`wightmanFunction_linear` in `Wightman/WightmanAxioms.lean`, which shows that
`qft.wightmanFunction n` is a continuous linear functional on the joint
Schwartz space. On the GNS side the consumer chain is explicit and should stay
explicit:

1. local NuclearSpaces support and/or gaussian-field import work produces the
   theorem package;
2. the reconstruction-facing export surface remains
   `Wightman/WightmanAxioms.lean :: schwartz_nuclear_extension`;
3. `Wightman/Reconstruction/GNSHilbertSpace.lean :: gns_cyclicity` and the
   `gnsQFT` packaging consume that downstream surface rather than reaching
   directly into a local support file.

This is needed to state `wightman_reconstruction` properly: the theorem says
`qft.wightmanFunction n fs = W_n(productTensor fs)`, and `wightmanFunction` is
defined using this axiom.

**Importance: Medium-High.**
The axiom is mathematically uncontroversial (standard functional analysis,
Gel'fand-Vilenkin IV, Reed-Simon Thm V.13). It does not carry any QFT content.
If it were removed, the reconstruction theorem's *statement* would need to be
reformulated (e.g. only asserting the identity on product test functions rather
than invoking the extended functional). The GNS *construction* itself
(gns_reproduces_wightman) does not use this axiom -- it works directly with
product test functions. The axiom only matters for packaging the result into
`WightmanQFT.wightmanFunction`.

**Difficulty to prove: Hard (but feasible).**
Nuclearity of Schwartz space has been formally proved in the `gaussian-field`
Lean 4 library. The remaining gap is importing that instance and deriving the
kernel theorem from it. This is a significant but well-understood formalization
effort -- perhaps 2-4 weeks of focused work by someone familiar with Mathlib's
functional analysis.

---

### A2. `exists_continuousMultilinear_ofSeparatelyContinuous`

**Current downstream consumer surface:** `WightmanAxioms.lean:504`

**Checked support lane cross-reference:**
- `Wightman/NuclearSpaces/NuclearSpace.lean`
- `Wightman/NuclearSpaces/SchwartzNuclear.lean`
- downstream bridge still exported as an axiom rather than imported from the
  local checked support lane

```lean
axiom exists_continuousMultilinear_ofSeparatelyContinuous {n : ℕ}
    (Phi : MultilinearMap ℂ (fun _ : Fin n => SchwartzSpacetime d) ℂ)
    (hPhi : ∀ (i : Fin n) (fs : Fin n -> SchwartzSpacetime d),
      Continuous (fun f => Phi (Function.update fs i f))) :
    ∃ PhiCont : ContinuousMultilinearMap ℂ
        (fun _ : Fin n => SchwartzSpacetime d) ℂ,
      ∀ fs, PhiCont fs = Phi fs
```

**What it says:** Separately continuous multilinear maps on products of Schwartz
spaces are jointly continuous (Banach-Steinhaus for Frechet spaces).

**How it enters the GNS pipeline:** Used in
`Wightman/WightmanAxioms.lean :: wightmanFunction_linear` to upgrade the
separately continuous n-point function to a jointly continuous one, so that A1
can be applied. The ownership split matters here too:

1. Package-B work may live in the checked `Wightman/NuclearSpaces/*` lane or
   arrive by gaussian-field import;
2. until that bridge is actually implemented, the GNS lane should treat
   `Wightman/WightmanAxioms.lean ::
   exists_continuousMultilinear_ofSeparatelyContinuous` as the frozen consumer
   surface;
3. `gns_cyclicity` is downstream of that exported surface, not a place to
   create a parallel local continuity theorem surface ad hoc.

**Importance: Medium.**
This is a stepping stone to A1. Like A1, it is pure functional analysis with
no QFT content. It could be bypassed if A1 were stated with weaker hypotheses
or if the Wightman function were directly shown to be jointly continuous.

**Difficulty to prove: Moderate.**
The Banach-Steinhaus theorem for Frechet spaces is standard but Mathlib's
coverage of Frechet spaces (as opposed to Banach spaces) is limited. The main
work is establishing that Schwartz space is a Frechet space (metrizable,
complete, locally convex) and applying the appropriate multilinear
generalization of Banach-Steinhaus. Likely 1-3 weeks of formalization effort.

---

## Sorries in the spectrum condition lane

The old monolithic `spectrum_condition = sorry` has been decomposed into
`MatrixElementSpectralCondition`, and the live owner queue is now source-checked
more sharply:

1. `GNSHilbertSpace.lean:1005 :: continuous_translate_npoint_schwartz`,
2. `GNSHilbertSpace.lean:1062 :: gns_stronglyContinuous_preHilbert`,
3. `GNSHilbertSpace.lean:1249 :: gns_matrix_coefficient_holomorphic_axiom`,
4. `GNSHilbertSpace.lean:1643 :: gns_cyclicity`,
5. `GNSHilbertSpace.lean:2114 :: gnsQFT`,
6. `Main.lean:63 :: wightman_reconstruction`,
7. `Main.lean:74 :: wightman_uniqueness`.

So in the current clone the first two translation/strong-continuity slots are
no longer open helper sorries. The only remaining spectrum-condition hole is
`matrix_coefficient_holomorphic`, and later Lean work should treat it as the
sole theorem allowed to consume the one-point forward-tube SCV package on the
GNS side.

### S1a. `continuous_translate_npoint_schwartz` — CLOSED

**File:** `GNSHilbertSpace.lean:1005`

The theorem is now implemented in the checked tree by flattening an n-point
Schwartz function to the ambient Schwartz space, applying
`continuous_translateSchwartz_smul`, and transporting continuity back through
`unflattenSchwartzNPointLocal`.

**Why this matters for the docs:** later GNS notes should no longer budget a
separate seminorm-proof work package here unless they are explicitly planning a
refactor away from the current flatten/unflatten proof. The active ambiguity is
not “how to prove translation continuity”; it is only which later theorem first
consumes it.

Its first consumer remains exactly:
- `GNSHilbertSpace.lean:1062 :: gns_stronglyContinuous_preHilbert`.

---

### S1b. `gns_stronglyContinuous_preHilbert` — CLOSED

**File:** `GNSHilbertSpace.lean:1062`

The theorem is now implemented in the checked tree via the norm-square route
already described in the blueprint: rewrite the translated inner product through
`continuous_wip_translate`, prove continuity at `0`, then transport to general
`t₀` using the translation group law.

**Why this matters for the docs:** the remaining GNS spectrum-condition work is
not a two-helper package plus a bridge axiom anymore. The helper lane is
already closed, so `gns_matrix_coefficient_holomorphic_axiom` is now the first
open spectrum-condition owner slot.

Its next consumer remains exactly:
- `GNSHilbertSpace.lean :: gns_translationStronglyContinuous`, then
- `GNSHilbertSpace.lean :: gns_spectrum_condition`.

---

### S1c. `gns_matrix_coefficient_holomorphic_axiom`

**File:** `GNSHilbertSpace.lean:1249`

```lean
theorem gns_matrix_coefficient_holomorphic_axiom
    (χ ψ : GNSHilbertSpace Wfn) :
    ∃ F : ComplexSpacetime d → ℂ,
      DifferentiableOn ℂ F (TranslationForwardTube d) ∧
      ∀ (a η : MinkowskiSpace d), η ∈ MinkowskiSpace.OpenForwardLightCone d →
        Filter.Tendsto
          (fun ε : ℝ => F (fun μ => ↑(a μ) + ε * ↑(η μ) * Complex.I))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (⟪χ, (gnsPoincareRep Wfn).U (PoincareGroup.translation' a) ψ⟫_ℂ)) := by
  sorry
```

**What it says:** Translation matrix coefficients `a ↦ ⟨χ, U(a) ψ⟩` extend
holomorphically to the one-point forward tube, with boundary values recovering
the real-translation matrix coefficient.

**Importance: High.**
This is the core analytical content of the spectrum condition. It encapsulates
the "partial boundary value" theorem: smearing an n-point Wightman function
against test functions in all but one translation variable produces a
holomorphic function of the remaining complex translation parameter.

**Difficulty to prove: Hard.**
Requires Fourier-Laplace theory and distributional boundary value machinery
not yet formalized in Lean/Mathlib. See
`communication/gns_spectrum_condition_strategy.md` for the proof roadmap.

---

## Other sorries on the critical path

### S2. `gns_cyclicity`

Checked owner/consumer boundary for this clone:

1. `GNSHilbertSpace.lean:1643 :: gns_cyclicity` is the **first** direct GNS
   consumer of the downstream nuclear theorem surfaces;
2. those downstream surfaces remain
   `Wightman/WightmanAxioms.lean :: schwartz_nuclear_extension` and
   `exists_continuousMultilinear_ofSeparatelyContinuous` until an explicit
   bridge/re-export layer replaces them;
3. `Main.lean:74 :: wightman_uniqueness` is downstream of `gnsQFT` and
   cyclicity, so it is not an admissible second home for quotient-density or
   nuclear-support work.


**File:** `GNSHilbertSpace.lean:1643`

```lean
theorem gns_cyclicity :
    Dense ((gnsOVD Wfn).algebraicSpan (gnsVacuum Wfn)).carrier := by
  sorry
```

**What it needs:** The algebraic span of `{phi(f1)...phi(fn)Omega : fi in S(R^{d+1}), n >= 0}`
is dense in the GNS Hilbert space.

**Proof strategy (from comments):**
1. By construction, vectors `phi(f1)...phi(fn)Omega` correspond to Borchers
   sequences whose n-th component is `productTensor [f1,...,fn]`.
2. So cyclicity reduces to: product tensors `f1(x1)...fn(xn)` are dense in
   `S(R^{n(d+1)})` in the topology induced by the Wightman inner product.
3. This follows from the Schwartz nuclear theorem: product test functions are
   dense in the joint Schwartz space.
4. In this clone the ownership order for that last step is part of the contract:
   local NuclearSpaces support -> optional bridge/import layer -> downstream
   `Wightman/WightmanAxioms.lean` theorem surfaces ->
   `GNSHilbertSpace.lean :: gns_cyclicity`.

So the GNS blocker is not merely “prove nuclearity somewhere”; it is “make the
nuclear-support route explicit enough that `gns_cyclicity` knows exactly which
exported theorem surface it consumes.”

**Importance: High.**
Cyclicity is a Wightman axiom (implicit in W2) and is essential for the
uniqueness theorem.

**Difficulty to prove: Hard.**
Directly blocked by A1 (Schwartz nuclear theorem). Once A1 is available, the
cyclicity proof should be relatively short. Estimated additional work beyond
A1: 1-2 weeks.

---

## Proved (formerly sorry)

### S3. `gns_vacuum_unique_of_poincare_invariant` — PROVED

**File:** `GNSHilbertSpace.lean` (theorem at line ~1403)

**What it proves:** Any Poincare-invariant vector in the GNS Hilbert space is
proportional to the vacuum.

**Proof method:** Cluster decomposition (Streater-Wightman, Theorem 3-5),
without Stone's theorem or spectral theory. The argument:
1. Lift `Wfn.cluster` to the GNS inner product level (`gns_cluster_preHilbert`)
2. Extend to the completion by density + unitarity (`gns_cluster_completion`)
3. For Poincare-invariant ψ: the function `r ↦ ⟨Φ, U(r·a)ψ⟩` is constant by
   invariance, and converges to `⟨Φ, Ω⟩ · ⟨Ω, ψ⟩` by clustering. Uniqueness
   of limits gives `ψ = ⟨Ω, ψ⟩ · Ω`.

**Note on W4 surface:** The `VacuumUnique` definition was corrected from
`IsTimeTranslationInvariant` to `IsPoincareInvariant`, matching the standard
Streater-Wightman formulation (W4: the vacuum is the unique Poincare-invariant
vector up to phase). The old time-translation-only version was non-standard.

**Helper lemmas (all proved):**
- `W_conjTP_vacuum_right`, `W_conjTP_vacuum_zero` — vacuum simplification
- `poincareActNPoint_translation_shift` — translation acts as pointwise shift
- `spatial_norm_smul_large` — spatial norm grows for large translations
- `cluster_term_tendsto` — per-term cluster convergence
- `WIP_F_vacuum_eq_sum`, `WIP_vacuum_G_eq_sum` — vacuum inner product decomposition
- `gns_cluster_preHilbert` — cluster property on pre-Hilbert space
- `gns_cluster_completion` — extension to completion

---

## Standalone Sorry (not on the reconstruction critical path)

### S4. `wightman_uniqueness`

**File:** `Main.lean:74`

```lean
theorem wightman_uniqueness (qft₁ qft₂ : WightmanQFT d)
    (h : ∀ n : ℕ, ∀ fs : Fin n → SchwartzSpacetime d,
      qft₁.wightmanFunction n fs = qft₂.wightmanFunction n fs) :
    ∃ U : qft₁.HilbertSpace →ₗᵢ[ℂ] qft₂.HilbertSpace,
      U qft₁.vacuum = qft₂.vacuum ∧
      (∀ (f : SchwartzSpacetime d) (ψ : qft₁.HilbertSpace),
        ψ ∈ qft₁.field.domain →
        U (qft₁.field.operator f ψ) = qft₂.field.operator f (U ψ)) := by
  sorry
```

**What it says:** Two Wightman QFTs with identical smeared n-point functions are
unitarily equivalent.

**Implementation boundary (source-checked):**
This is a pure downstream consumer at the checked frontier
`GNSHilbertSpace.lean:1005 -> :1062 -> :1249 -> :1643 -> :2114`, then
`Main.lean:74`. It may consume only the finished `WightmanQFT` structure plus
honest cyclicity facts. It is **not** an admissible second home for the
spectrum bridge, nuclear bridge, quotient-density work, or cyclicity
packaging.

**Checked-tree ownership clarification:**
A direct repo-tree scan now fixes the file boundary more sharply than the older
high-level slogan “Main theorem plus standard helper lemmas”:
1. the checked support lane that really exists under `Wightman/` is the
   `NuclearSpaces/*` subtree (including `Helpers/PositiveDefiniteKernels.lean`
   and `NuclearOperator.lean`), which is upstream of GNS;
2. the GNS production lane that really exists under `Wightman/Reconstruction/`
   is `.../GNSHilbertSpace.lean` ending at `:2114 :: gnsQFT`;
3. after that, the current tree has `Main.lean:74 :: wightman_uniqueness`, but
   **no separate checked Main-side uniqueness helper file** such as a
   `UniquenessCore.lean` / `UniquenessHelpers.lean` module;
4. therefore every intermediate name in the uniqueness queue below is a
   documentation-owned theorem slot, not a hidden checked theorem surface to be
   rediscovered later.

That ownership fact matters operationally: later Lean implementation should not
burn time grepping for a nonexistent support module before starting the Main
lane, and no doc should describe the helper package as if it already lives in
an unmentioned checked file.

Physical insertion rule, now fixed against the live tree:
1. either the whole helper queue is created directly in
   `Wightman/Reconstruction/Main.lean` above `Main.lean:74`, in the documented
   theorem order;
2. or one explicitly named new helper file under
   `Wightman/Reconstruction/` is created first, and then one contiguous prefix
   or block of the queue is moved there with imports/docs updated in the same
   pass;
3. later Lean work may not scatter the queue across unrelated existing files
   such as `Core.lean`, `GNSConstruction.lean`, or random Wick-rotation files
   just because those files already exist.

**Exact helper / proof order to execute in Lean:**
1. build the dense cyclic-word core explicitly via `cyclicWordVector` / `cyclicWordSpan`;
2. prove the exact core inner-product formula `cyclicWordVector_inner_cyclicWordVector`;
3. define the pre-quotient map `uniquenessPreMap` on cyclic words;
4. prove the transferred inner-product identity `uniquenessPreMap_inner_formula`;
5. close the only quotient-descent slot `uniquenessPreMap_null_of_null`;
6. only then package the descended map as `uniquenessDenseMap`, then separately prove `uniquenessDenseMap_inner_preserving`, `uniquenessDenseMap_norm_preserving`, and only then `uniquenessDenseMap_isometry`;
7. prove dense range in the fixed two-step order `cyclicWord_in_range_of_uniquenessDenseMap` -> `cyclicWordSpan_le_range_uniquenessDenseMap` -> `uniquenessDenseMap_denseRange`;
8. extend to the unitary by `uniquenessDenseMap_extends_to_unitary`, with the
   local transcript frozen as `uniquenessDenseMap_isometry`
   + `uniquenessDenseMap_denseRange` -> standard completion-extension theorem
   -> surjectivity/unitary packaging -> exported extension identity on the
   dense cyclic subspace;
9. prove `U Ω₁ = Ω₂`;
10. prove field intertwining first on the cyclic core via `uniquenessUnitary_intertwines_field_on_cyclic_core`;
11. close the separate core theorem `cyclicWordSpan_is_field_core` in the
    literal order `cyclicWordVector_mem_domain` -> span-level domain inclusion
    -> checked `WightmanQFT` field-core/graph-closure facts;
12. export the domain-level statement only after that core theorem, yielding
    `uniquenessUnitary_intertwines_field` and finally
    `wightman_uniqueness`.

**Non-negotiable first-consumer boundaries:**
1. `uniquenessPreMap_inner_formula` is the first row allowed to consume `cyclicWordVector_inner_cyclicWordVector` together with the hypothesis `h`; no later slot may recreate the cyclic-word matrix-element transfer from scratch.
2. `uniquenessPreMap_null_of_null` is the only row allowed to do quotient/null-vector descent.
3. `uniquenessDenseMap_inner_preserving` and `uniquenessDenseMap_norm_preserving` begin only after `uniquenessDenseMap` exists; they may consume only the descended map, not reopen cyclic-word expansion or quotient descent.
4. `uniquenessDenseMap_isometry` does **not** start dense-range work; dense range begins only at `cyclicWord_in_range_of_uniquenessDenseMap` and closes only at `uniquenessDenseMap_denseRange`.
5. `uniquenessUnitary_intertwines_field_on_cyclic_core` is core-only and may not hide a graph-closure/domain-extension argument.
6. `cyclicWordSpan_is_field_core` is the first row allowed to invoke field-core closure machinery.
7. `uniquenessDenseMap_extends_to_unitary` is the only row allowed to finish
   completion-extension / surjectivity packaging; later rows may only consume
   its exported unitary plus extension identity.
8. `Main.lean:74 :: wightman_uniqueness` is assembly-only: it may consume `uniquenessUnitary_maps_vacuum` and `uniquenessUnitary_intertwines_field`, but it may not silently reopen quotient descent, dense range, unitary extension, or domain closure.

**Importance: Low-Medium for the reconstruction theorem.**
This theorem is not used by any other proof in the codebase, but the docs now
fix it as a downstream execution target rather than a vague “standard GNS
uniqueness” tail item.

---

## Dependency and Criticality Summary

```
wightman_reconstruction  (PROVED, modulo sorries in gnsQFT)
  └── wightman_reconstruction'  (PROVED)
       └── gnsQFT : WightmanQFT d
            ├── spectrum_condition  = MatrixElementSpectralCondition
            │    ├── strongly_continuous
            │    │    ├── gns_stronglyContinuous_completion     ✓ (proved)
            │    │    ├── gns_stronglyContinuous_preHilbert     ✓ (checked closed at `GNSHilbertSpace.lean:1062`)
            │    │    └── continuous_translate_npoint_schwartz  ✓ (checked closed at `GNSHilbertSpace.lean:1005`)
            │    └── matrix_coefficient_holomorphic  sorry [S1c]
            │
            ├── cyclicity           = sorry  [S2]  ← downstream consumer of the nuclear bridge surface (A1/A2 route)
            │
            ├── vacuum_unique       ✓ PROVED via cluster decomposition
            │    ├── .1 (Ω is Poincaré-invariant)  ✓
            │    └── .2 (uniqueness)                ✓ gns_vacuum_unique_of_poincare_invariant
            │
            ├── vacuum_normalized        ✓ (proved in GNSConstruction.lean)
            ├── vacuum_invariant         ✓ (proved in GNSHilbertSpace.lean)
            ├── covariance               ✓ (proved in GNSHilbertSpace.lean)
            ├── locality                 ✓ (proved in GNSHilbertSpace.lean)
            ├── field_hermitian          ✓ (proved in GNSHilbertSpace.lean)
            ├── field (all subfields)    ✓ (proved in GNSHilbertSpace.lean)
            └── poincare_rep (all)       ✓ (proved in GNSHilbertSpace.lean)

wightman_uniqueness  = sorry  [S4]
  (pure downstream consumer after `gnsQFT` + cyclicity;
   fixed execution queue =
   `cyclicWordVector/cyclicWordSpan`
   -> `cyclicWordVector_inner_cyclicWordVector`
   -> `uniquenessPreMap`
   -> `uniquenessPreMap_inner_formula`
   -> `uniquenessPreMap_null_of_null`
   -> `uniquenessDenseMap`
   -> `uniquenessDenseMap_inner_preserving`
   -> `uniquenessDenseMap_norm_preserving`
   -> `uniquenessDenseMap_isometry`
   -> `cyclicWord_in_range_of_uniquenessDenseMap`
   -> `cyclicWordSpan_le_range_uniquenessDenseMap`
   -> `uniquenessDenseMap_denseRange`
   -> `uniquenessDenseMap_extends_to_unitary`
   -> `uniquenessUnitary_maps_vacuum`
   -> `uniquenessUnitary_intertwines_field_on_cyclic_core`
   -> `cyclicWordSpan_is_field_core`
   -> `uniquenessUnitary_intertwines_field`
   -> `wightman_uniqueness`)

Transitive axiom dependencies:
  WightmanQFT.wightmanFunction  uses  A1, A2
```

### What is fully proved (no sorries, no axioms)

The mathematical heart of the GNS construction is completely clean:

- **`gns_reproduces_wightman`**: `<Omega, phi(f1)...phi(fn)Omega> = W_n(f1 x...x fn)` -- fully proved
- **`vacuum_normalized`**: `<Omega, Omega> = 1` -- fully proved
- **`vacuum_unique`**: Poincare-invariant vectors are proportional to Omega -- **fully proved** via cluster decomposition
- **Poincare representation**: unitary, group law, vacuum invariance -- fully proved
- **Locality**: field operators commute at spacelike separation -- fully proved
- **Covariance**: `phi(f)(U(g)psi) = U(g)(phi(g^{-1}f)psi)` -- fully proved
- **Field hermiticity**: `<phi(f)x, y> = <x, phi(f*)y>` -- fully proved
- **All algebraic instances** (AddCommGroup, Module, InnerProductSpace.Core, completion) -- fully proved
- **Strong continuity on the completion** (`gns_stronglyContinuous_completion`): proved (modulo the pre-Hilbert sorry)
- **Cluster decomposition on the completion** (`gns_cluster_completion`): fully proved

### What remains

| Blocker | Sorries / axioms it blocks | Mathematical area |
|---------|----------------------------|-------------------|
| Fourier-Laplace / boundary values | S1c | Complex analysis / distribution theory |
| NuclearSpaces support -> bridge -> downstream reconstruction integration | S2 and transitively the downstream axiom surfaces A1, A2 | Functional analysis / nuclear spaces |
| GNS uniqueness dense-core / quotient-descent / dense-range / field-core package | S4 | Operator algebras |

The third row is deliberately phrased as an **integration** blocker rather than
"there is no nuclear-space lane". In this clone the local NuclearSpaces files
already exist and contain real checked support; what remains open is pinning an
exact ownership-respecting route
`Wightman/NuclearSpaces/*` -> bridge/import layer ->
`Wightman/WightmanAxioms.lean` -> `GNSHilbertSpace.lean`
for the theorem surfaces used by the GNS pipeline.

### Difficulty ranking (hardest first)

1. **S1c (holomorphic bridge axiom)** -- Hard. Requires Fourier-Laplace theory and distributional boundary value machinery not yet in Mathlib.

2. **S2 (cyclicity)** -- Hard. Blocked by the nuclear theorem (A1). Once A1 is available, the proof is relatively straightforward.

3. **A1 / A2 downstream integration route** -- Hard. The mathematical support is no longer just an external aspiration: this clone now also contains a checked `Wightman/NuclearSpaces/*` lane. The remaining work is to decide and implement the exact bridge from that local support lane and/or imported `gaussian-field` results into the downstream `WightmanAxioms.lean` consumer surfaces without duplicating theorem packaging.

4. **A2 (separately continuous -> jointly continuous)** -- Moderate at the theorem level, but still part of the same documentation-level integration problem above: the local NuclearSpaces lane, any imported `gaussian-field` theorem, and the downstream axiom-export surface must be kept distinct until one exact bridge route is chosen.

5. **S4 (wightman_uniqueness)** -- Moderate. Execute only after honest cyclicity: cyclic-word core -> exact inner-product formula -> quotient descent -> descended-map/isometry -> dense range -> unitary extension -> cyclic-core field intertwining -> domain closure. Not on the critical path.

### Bottom line

The GNS pipeline has made significant progress. The core mathematical content --
the reproducing identity, the inner product space construction, Poincare
covariance, locality, field hermiticity, and **vacuum uniqueness** -- is
**fully proved**. The spectrum condition has been decomposed from a monolithic
sorry into `MatrixElementSpectralCondition`; in the current checked tree the
translation/strong-continuity sublane is already closed at
`GNSHilbertSpace.lean:1005` and `:1062`, leaving only the holomorphic bridge
slot `gns_matrix_coefficient_holomorphic_axiom` open on that route. The
cyclicity sorry (S2) remains unchanged, blocked by the nuclear theorem.
