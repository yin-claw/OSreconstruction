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
   `ComplexSchwartz.lean`, plus helpers);
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
   `BochnerMinlos.lean`: 5), but those support-lane holes remain outside the
   headline repo-wide `63`-sorry census because that headline is reserved for
   the theorem-2/3/4 critical-path ledger.

For the GNS lane, that means the implementation contract is:

1. local theorem work may happen in the checked `Wightman/NuclearSpaces/*`
   files;
2. reconstruction-facing consumers still read the theorem surface from
   `Wightman/WightmanAxioms.lean`;
3. any import/re-export replacement of those axioms is bridge work and should
   be tracked explicitly as such, not hidden as if `gns_cyclicity` already had
   direct local NuclearSpaces ownership.

---

## Summary

| ID | Name | Kind | File | Status |
|----|------|------|------|--------|
| A1 | `schwartz_nuclear_extension` | axiom | WightmanAxioms.lean:342 | On critical path (transitive) |
| A2 | `exists_continuousMultilinear_ofSeparatelyContinuous` | axiom | WightmanAxioms.lean:504 | On critical path (transitive) |
| S1a | `continuous_translate_npoint_schwartz` | sorry | GNSHilbertSpace.lean:840 | Helper for spectrum condition |
| S1b | `gns_stronglyContinuous_preHilbert` | sorry | GNSHilbertSpace.lean:901 | Helper for spectrum condition |
| S1c | `gns_matrix_coefficient_holomorphic_axiom` | sorry | GNSHilbertSpace.lean:993 | Bridge axiom for spectrum condition |
| S2 | `gns_cyclicity` | sorry | GNSHilbertSpace.lean:1067 | On critical path |
| S4 | `wightman_uniqueness` | sorry | Main.lean:82 | Standalone (not used elsewhere) |

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
`MatrixElementSpectralCondition`, which packages two fields:

1. **`strongly_continuous`** — proved via `gns_translationStronglyContinuous`,
   which in turn depends on two helper sorries (S1a, S1b).
2. **`matrix_coefficient_holomorphic`** — deferred as a bridge sorry (S1c).

### S1a. `continuous_translate_npoint_schwartz`

**File:** `GNSHilbertSpace.lean:840`

```lean
private theorem continuous_translate_npoint_schwartz
    (μ : Fin (d + 1)) {n : ℕ} (f : SchwartzNPoint d n) :
    Continuous (fun t : ℝ =>
      poincareActNPoint (PoincareRepresentation.translationInDirection d μ t) f) := by
  sorry
```

**What it says:** Translation in direction μ is continuous in the Schwartz
topology on n-point functions. This is the standard fact that translation is a
strongly continuous action on Schwartz space.

**Importance: Medium.**
Used by `continuous_wip_translate` (continuity of the Wightman inner product
under translation), which feeds into `gns_stronglyContinuous_preHilbert`.

**Difficulty to prove: Moderate.**
Standard seminorm estimation. The codebase already has
`SCV.tendsto_translateSchwartz_nhds_of_isCompactSupport` for the compact-support
case; the general case needs adapting that argument to the full Schwartz topology.

---

### S1b. `gns_stronglyContinuous_preHilbert`

**File:** `GNSHilbertSpace.lean:901`

```lean
private theorem gns_stronglyContinuous_preHilbert
    (μ : Fin (d + 1)) (x : PreHilbertSpace Wfn) :
    Continuous (fun t : ℝ =>
      poincareActGNS Wfn
        (PoincareRepresentation.translationInDirection d μ t)
        (x : GNSHilbertSpace Wfn)) := by
  ...
  sorry
```

**What it says:** Strong continuity of translations on embedded pre-Hilbert
vectors. The proof strategy (outlined in comments) uses
`‖U(t)x - U(t₀)x‖² = 2 Re⟨x,x⟩ - 2 Re⟨x, U(t-t₀)x⟩ → 0`
which follows from `continuous_wip_translate` (which depends on S1a).

**Importance: Medium.**
Direct dependency of `gns_translationStronglyContinuous`. Once S1a is proved,
S1b's proof is a standard norm-squared expansion.

**Difficulty to prove: Easy (once S1a is done).**
The argument is fully outlined. The extension from pre-Hilbert to the completion
(`gns_stronglyContinuous_completion`) is already fully proved via the standard
density + isometry triangle inequality.

---

### S1c. `gns_matrix_coefficient_holomorphic_axiom`

**File:** `GNSHilbertSpace.lean:993`

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

**File:** `GNSHilbertSpace.lean:1067`

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

**File:** `Main.lean:82`

```lean
theorem wightman_uniqueness (qft1 qft2 : WightmanQFT d)
    (h : forall n fs, qft1.wightmanFunction n fs = qft2.wightmanFunction n fs) :
    exists U : qft1.HilbertSpace →ₗᵢ[ℂ] qft2.HilbertSpace, ... := by
  sorry
```

**What it says:** Two Wightman QFTs with identical n-point functions are
unitarily equivalent.

**Importance: Low-Medium for the reconstruction theorem.**
This theorem is not used by any other proof in the codebase. It is a
standalone companion to `wightman_reconstruction`.

**Difficulty to prove: Moderate.**
Standard GNS uniqueness argument. Estimated effort: 2-4 weeks.

---

## Dependency and Criticality Summary

```
wightman_reconstruction  (PROVED, modulo sorries in gnsQFT)
  └── wightman_reconstruction'  (PROVED)
       └── gnsQFT : WightmanQFT d
            ├── spectrum_condition  = MatrixElementSpectralCondition
            │    ├── strongly_continuous     (proved modulo S1a, S1b)
            │    │    ├── gns_stronglyContinuous_completion     ✓ (proved)
            │    │    └── gns_stronglyContinuous_preHilbert     sorry [S1b]
            │    │         └── continuous_wip_translate          (proved modulo S1a)
            │    │              └── continuous_translate_npoint_schwartz  sorry [S1a]
            │    └── matrix_coefficient_holomorphic  sorry [S1c]
            │
            ├── cyclicity           = sorry  [S2]  ← nuclear theorem (A1)
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

wightman_uniqueness  = sorry  [S4]  (standalone, not used elsewhere)

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
| Schwartz translation continuity | S1a, S1b | Analysis (seminorm estimation) |
| Fourier-Laplace / boundary values | S1c | Complex analysis / distribution theory |
| NuclearSpaces support -> bridge -> downstream reconstruction integration | S2 and transitively the downstream axiom surfaces A1, A2 | Functional analysis / nuclear spaces |
| GNS uniqueness argument | S4 | Operator algebras |

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

5. **S1a (Schwartz translation continuity)** -- Moderate. Standard seminorm estimation, partially available in the SCV module.

6. **S1b (pre-Hilbert strong continuity)** -- Easy once S1a is done. Proof strategy fully outlined.

7. **S4 (wightman_uniqueness)** -- Moderate. Standard GNS uniqueness argument. Not on the critical path.

### Bottom line

The GNS pipeline has made significant progress. The core mathematical content --
the reproducing identity, the inner product space construction, Poincare
covariance, locality, field hermiticity, and **vacuum uniqueness** -- is
**fully proved**. The spectrum condition has been decomposed from a monolithic
sorry into `MatrixElementSpectralCondition` with three isolated helper sorries
(Schwartz translation continuity, pre-Hilbert strong continuity, holomorphic
bridge). The cyclicity sorry (S2) remains unchanged, blocked by the nuclear
theorem.
