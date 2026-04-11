# GNS Pipeline Blueprint

Purpose: this note is the implementation blueprint for the GNS-side
reconstruction pipeline.

It should be read together with:
- `docs/gns-pipeline-sorries.md`,
- `docs/wightman_uniqueness_blueprint.md`,
- `docs/nuclear_spaces_blueprint.md`,
- `docs/scv_infrastructure_blueprint.md`.

This note is not a summary. It is the theorem-by-theorem implementation guide
for the remaining GNS-facing proof packages.

## 1. Live theorem surfaces

Checked-tree clarification for this clone:

1. the downstream GNS consumer files named below are checked-present;
2. the repo tree also contains a checked `OSReconstruction/Wightman/NuclearSpaces/`
   subtree (`NuclearSpace.lean`, `SchwartzNuclear.lean`,
   `GaussianFieldBridge.lean`, `BochnerMinlos.lean`, `EuclideanMeasure.lean`,
   `ComplexSchwartz.lean`, plus helpers), so the nuclear/kernel lane is **not**
   merely historical in this clone;
3. however, the reconstruction-critical consumer surface is still the pair of
   axioms in `Wightman/WightmanAxioms.lean`, and later Lean work must keep
   separate:
   - checked support files that already exist under `Wightman/NuclearSpaces/`,
   - theorem surfaces already exported as axioms in `Wightman/WightmanAxioms.lean`, and
   - any still-planned integration/wrapper work needed to connect the two;
4. the current policy-level sorry census also keeps that distinction explicit:
   a direct checked-tree scan shows **7** local `sorry`s in the checked
   `Wightman/NuclearSpaces/*` lane (`NuclearSpace.lean`: 2,
   `BochnerMinlos.lean`: 5), and those 7 are already included in the live
   **60**-sorry whole-project census used by the proof-doc stack. The live
   overview docs still track the NuclearSpaces lane separately, but that is an
   ownership/readout split rather than an outside-the-headline-count exception.
   Any narrower auxiliary census must be labeled explicitly.

So the GNS documentation contract in this clone is three-layered:

1. local support ownership: `Wightman/NuclearSpaces/NuclearSpace.lean`,
   `SchwartzNuclear.lean`, `GaussianFieldBridge.lean`,
   `BochnerMinlos.lean`, `EuclideanMeasure.lean`, `ComplexSchwartz.lean`;
2. downstream consumer ownership: `Wightman/WightmanAxioms.lean` exports
   `exists_continuousMultilinear_ofSeparatelyContinuous` (`:504`) and
   `schwartz_nuclear_extension` (`:342`), then
   `Wightman/Reconstruction/GNSHilbertSpace.lean` consumes the resulting
   `WightmanQFT` surface through `gns_cyclicity` (`:1643`) and `gnsQFT`
   (`:2114`);
3. integration ownership: any future import/re-export/wrapper work that wires
   the checked local NuclearSpaces lane into those downstream axiom surfaces
   must be documented as bridge work rather than silently treated as if the
   axioms had already been replaced in-place.

The GNS pipeline currently feeds:

1. `Wightman/Reconstruction/GNSHilbertSpace.lean :2114 :: gnsQFT`,
2. `Wightman/Reconstruction/Main.lean :63 :: wightman_reconstruction`,
3. `Wightman/Reconstruction/Main.lean :74 :: wightman_uniqueness`.

Source-checked owner/consumer split for the live GNS lane:

1. `GNSHilbertSpace.lean :1005 :: continuous_translate_npoint_schwartz` is the
   first still-open translation-continuity slot;
2. `:1062 :: gns_stronglyContinuous_preHilbert` is the second slot and may
   consume Package A, but nothing later;
3. `:1249 :: gns_matrix_coefficient_holomorphic_axiom` is the only spectrum
   bridge theorem allowed to touch the one-point forward-tube package;
4. `:1643 :: gns_cyclicity` is the first direct GNS consumer of the downstream
   nuclear theorem surfaces exported by `WightmanAxioms.lean`;
5. `:2114 :: gnsQFT` is assembly only, and `Main.lean :74 :: wightman_uniqueness`
   is downstream of that assembly rather than a co-owner of any GNS package.

The implementation contract is therefore not just “finish the GNS file”. The
literal owner queue is:

`continuous_translate_npoint_schwartz`
-> `gns_stronglyContinuous_preHilbert`
-> `gns_matrix_coefficient_holomorphic_axiom`
-> nuclear bridge through exported `WightmanAxioms.lean` surfaces
-> `gns_cyclicity`
-> `gnsQFT`
-> `wightman_uniqueness`.

The remaining GNS-side blockers are:

1. `continuous_translate_npoint_schwartz`,
2. `gns_stronglyContinuous_preHilbert`,
3. `gns_matrix_coefficient_holomorphic_axiom`,
4. `gns_cyclicity`,
5. the transitive nuclear axioms
   `schwartz_nuclear_extension` and
   `exists_continuousMultilinear_ofSeparatelyContinuous`.

## 2. What is already fully proved

The docs should treat the following as closed infrastructure, not live
frontiers:

1. the Borchers quotient / pre-Hilbert construction,
2. the completion to the GNS Hilbert space,
3. the field-operator algebraic package,
4. covariance, locality, hermiticity,
5. vacuum normalization,
6. vacuum uniqueness via cluster decomposition,
7. the final theorem `wightman_reconstruction'` modulo the remaining fields of
   `gnsQFT`.

So later Lean work should not reopen those packages unless an exact compile
failure forces it.

## 3. Package A: Translation continuity on Schwartz n-point functions

The first remaining package is:

```lean
private theorem continuous_translate_npoint_schwartz
```

Its job is narrow:

1. fix a direction `μ`,
2. fix a Schwartz n-point function `f`,
3. prove continuity of
   `t ↦ poincareActNPoint (translationInDirection μ t) f`
   in the Schwartz topology.

The implementation should be split into:

```lean
lemma seminorm_translate_bound
lemma seminorm_translate_tendsto_self
lemma translate_npoint_schwartz_continuous
theorem continuous_translate_npoint_schwartz
```

This should be proved by seminorm control, not by appealing to an abstract
Lie-group action theorem.

### 3.1. Exact proof transcript for translation continuity

The later Lean proof should be written at the seminorm level:

1. fix a Schwartz seminorm `p_{α,β}`,
2. compute the derivative and polynomial-weight effect of translation on
   `poincareActNPoint (translationInDirection μ t) f`,
3. prove a uniform bound
   `p_{α,β}(translate_t f) ≤ C_{α,β} * Σ_{γ≤β} p_{α,γ}(f)`,
4. prove `translate_t f -> f` in each seminorm as `t -> 0`,
5. package seminorm convergence into continuity in the Schwartz topology.

So the theorem slots should really be read as:

```lean
lemma derivative_of_npoint_translation
lemma polynomial_weight_under_translation
lemma seminorm_translate_bound
lemma seminorm_translate_tendsto_self
lemma translate_npoint_schwartz_continuous
theorem continuous_translate_npoint_schwartz
```

This keeps Package A entirely on the explicit Schwartz-analysis surface already
used elsewhere in the repo.

## 4. Package B: Strong continuity on the pre-Hilbert level

The second remaining package is:

```lean
private theorem gns_stronglyContinuous_preHilbert
```

This theorem should be treated as almost formal once Package A is available.

Exact proof route:

1. reduce strong continuity to continuity of the norm square,
2. expand the norm square by the Wightman inner product,
3. use continuity of translated n-point test functions from Package A,
4. conclude continuity at the pre-Hilbert level,
5. then reuse the already-proved completion extension theorem.

Documentation-standard theorem slots:

```lean
lemma continuous_wip_translate
lemma norm_sq_translate_difference_formula
lemma prehilbert_translation_continuous_at_zero
theorem gns_stronglyContinuous_preHilbert
```

The later Lean file should not treat this as a spectral theorem argument. It is
just a continuity-of-the-inner-product argument.

### 4.1. Exact proof transcript for pre-Hilbert strong continuity

The later Lean proof should use the following literal norm-square identity:

```lean
‖U(t)ξ - ξ‖² = ⟪U(t)ξ, U(t)ξ⟫ - ⟪U(t)ξ, ξ⟫ - ⟪ξ, U(t)ξ⟫ + ⟪ξ, ξ⟫
```

and then proceed as:

1. reduce to algebraic pre-Hilbert vectors represented by Borchers sequences,
2. rewrite each inner-product term as a finite sum of Wightman pairings,
3. invoke Package A on each translated test-function term,
4. conclude continuity of the norm square at `0`,
5. deduce continuity of the norm,
6. extend from `0` to all `t` using the group law.

The theorem slots should therefore be:

```lean
lemma algebraic_preHilbert_translation_inner_formula
lemma continuous_wip_translate
lemma norm_sq_translate_difference_formula
lemma prehilbert_translation_continuous_at_zero
lemma prehilbert_translation_continuous
theorem gns_stronglyContinuous_preHilbert
```

## 5. Package C: Matrix-coefficient holomorphic bridge

This is the hard theorem:

```lean
theorem gns_matrix_coefficient_holomorphic_axiom
```

The later implementation should state its honest mathematical content as:

1. fix `χ ψ` in the GNS Hilbert space,
2. show the real-translation matrix coefficient
   `a ↦ ⟪χ, U(a) ψ⟫`
   extends holomorphically to the one-point forward tube,
3. show the real coefficient is recovered as the boundary value.

The paper-faithful route is one-variable and distributional:

1. represent matrix coefficients by smeared Wightman distributions,
2. isolate one translation variable,
3. apply a forward-tube boundary-value theorem,
4. recover the holomorphic extension by uniqueness.

So the theorem-slot inventory should be:

```lean
lemma matrix_coefficient_as_smeared_wightman
lemma matrix_coefficient_distribution_has_forward_support
lemma matrix_coefficient_partial_boundary_value
lemma matrix_coefficient_holomorphic_extension
theorem gns_matrix_coefficient_holomorphic_axiom
```

This package depends on the SCV/forward-tube documentation in
`docs/scv_infrastructure_blueprint.md`.

### 5.1. Exact proof transcript for the matrix-coefficient bridge

The later Lean proof should proceed in the following explicit order:

1. reduce from arbitrary `χ ψ : GNSHilbertSpace Wfn` to dense algebraic GNS
   vectors represented by Borchers sequences;
2. on those algebraic vectors, expand the translation matrix coefficient as a
   finite sum of Wightman pairings with one translated factor;
3. freeze all non-translation variables, producing a one-variable tempered
   distribution on spacetime;
4. prove forward support of that one-variable distribution from the existing
   spectrum-condition support package;
5. apply the one-point forward-tube boundary-value theorem;
6. recover the real matrix coefficient as the boundary value;
7. extend from algebraic vectors to arbitrary `χ ψ` by density and continuity.

So the theorem-slot inventory should really be read as:

```lean
lemma matrix_coefficient_as_smeared_wightman
    (F G : BorchersSequence d) :
    ∀ a : MinkowskiSpace d,
      ⟪χ_F, (gnsPoincareRep Wfn).U (PoincareGroup.translation' a) ψ_G⟫_ℂ
        =
      finite_translation_pairing_sum Wfn F G a

lemma matrix_coefficient_distribution_has_forward_support
    (F G : BorchersSequence d) :
    ForwardSupportedDistribution
      (fun a : MinkowskiSpace d => finite_translation_pairing_sum Wfn F G a)

lemma matrix_coefficient_partial_boundary_value
    (F G : BorchersSequence d) :
    ∃ H : ComplexSpacetime d → ℂ,
      DifferentiableOn ℂ H (TranslationForwardTube d) ∧
      boundaryValueOf H =
        (fun a : MinkowskiSpace d => finite_translation_pairing_sum Wfn F G a)

lemma matrix_coefficient_holomorphic_extension
    (χ ψ : GNSHilbertSpace Wfn) :
    ∃ H : ComplexSpacetime d → ℂ,
      DifferentiableOn ℂ H (TranslationForwardTube d) ∧
      matrixCoefficientBoundaryValue H χ ψ
```

The crucial point is that this is a one-variable forward-tube theorem in
disguise. It should not be implemented as a new many-variable SCV package.

### 5.2. Exact interface to the forward-tube package

The later Lean file should not leave the SCV dependency vague. The actual
consumer interface should be:

1. a one-variable tempered distribution with forward support,
2. a one-point flat-regular / Fourier-Laplace package,
3. a one-point boundary-value recovery theorem,
4. a uniqueness theorem on the one-point translation tube.

So the later implementation should either reuse or locally define theorem slots
of the form:

```lean
lemma onePoint_forward_support_to_flatRegular
lemma onePoint_boundary_value_recovery
lemma onePoint_forwardTube_uniqueness
```

Only after those are in place should
`gns_matrix_coefficient_holomorphic_axiom` be a short consumer theorem.

## 6. Package D: Cyclicity

The theorem

```lean
theorem gns_cyclicity
```

should be treated as the first direct GNS consumer of the downstream
nuclear-space theorem surface.

More explicitly, the ownership chain for this package is:

1. local support/theorem work belongs in the checked
   `Wightman/NuclearSpaces/*` files and in the bridge/import layer described in
   `docs/nuclear_spaces_blueprint.md`;
2. the reconstruction-facing theorem surfaces remain
   `Wightman/WightmanAxioms.lean ::
   exists_continuousMultilinear_ofSeparatelyContinuous` and
   `Wightman/WightmanAxioms.lean :: schwartz_nuclear_extension` until that
   bridge is actually implemented;
3. `Wightman/Reconstruction/GNSHilbertSpace.lean :: gns_cyclicity` is the
   first theorem that should consume those downstream surfaces on the GNS side,
   rather than reaching directly into a local NuclearSpaces file by ad hoc
   imports or new wrapper surfaces.

Exact route:

1. product test functions span a dense subspace of the joint Schwartz space,
2. Borchers vectors generated from those product tests span the algebraic orbit
   of the vacuum,
3. the reproducing identity identifies the GNS norm closure with the full
   Hilbert space.

Documentation-standard theorem slots:

```lean
lemma productTensor_dense_in_joint_schwartz
lemma field_words_generate_productTensor_vectors
lemma cyclic_span_contains_dense_borchers_subspace
theorem gns_cyclicity
```

The honest blocker here is not GNS algebra. It is the Schwartz nuclear/kernel
theorem documented in `docs/nuclear_spaces_blueprint.md`.

### 6.1. Exact proof transcript for cyclicity

The later Lean proof should be written as:

1. use the kernel theorem to identify product tensors as a dense subspace of
   the full joint Schwartz space,
2. prove every product tensor corresponds to a finite field word applied to the
   vacuum,
3. prove every Borchers class in the pre-Hilbert quotient is a finite sum of
   such single/product-tensor vectors,
4. use the completion map to transport density from the algebraic quotient to
   the Hilbert space,
5. conclude density of the vacuum algebraic span.

So the theorem slots should be read more literally as:

```lean
lemma productTensor_dense_in_joint_schwartz
lemma productTensor_singlePH_representation
lemma quotient_vector_eq_finite_sum_of_singlePH
lemma cyclic_span_contains_dense_borchers_subspace
theorem gns_cyclicity
```

This theorem is therefore a kernel-theorem consumer plus a quotient-density
argument; no new QFT-specific analysis should be hiding in it. More sharply,
in this clone the theorem should be read as consuming one of two checked support
routes:

1. imported/re-exported support already routed through the checked
   `Wightman/NuclearSpaces/GaussianFieldBridge.lean` and companion files, or
2. local support proved directly in the checked
   `Wightman/NuclearSpaces/*` lane described in
   `docs/nuclear_spaces_blueprint.md`.

But whichever support route is chosen, the proof transcript for the GNS lane
must still pass through the downstream exported surfaces in
`Wightman/WightmanAxioms.lean` before it reaches
`GNSHilbertSpace.lean :: gns_cyclicity`. In particular, later Lean work should
not bypass the exported `exists_continuousMultilinear_ofSeparatelyContinuous`
/ `schwartz_nuclear_extension` seam by importing a local helper directly into
`gns_cyclicity` unless the docs are updated in the same pass to replace that
consumer contract.

What is *not* allowed is to talk as if theorem 2/3/4 or GNS cyclicity will be
closed by an unspecified hidden package somewhere outside the checked tree.

## 7. Assembly into `gnsQFT`

Once Packages A-D are in place, the later assembly should become mechanical.

Lean-style pseudocode:

```lean
def gnsQFT : WightmanQFT d :=
{ vacuum := gnsVacuum Wfn
  field := gnsField Wfn
  poincare_rep := gnsPoincareRep Wfn
  spectrum_condition :=
    { strongly_continuous := gns_translationStronglyContinuous Wfn
      matrix_coefficient_holomorphic := gns_matrix_coefficient_holomorphic_axiom Wfn }
  cyclicity := gns_cyclicity Wfn
  vacuum_unique := gns_vacuum_unique Wfn
  ... }
```

At this stage, no theorem-shape choices should remain. The only remaining work
should be the actual proofs of the named theorem slots above.

## 8. Exact dependency order

The later Lean implementation should proceed in this order:

1. `GNSHilbertSpace.lean :1005 :: continuous_translate_npoint_schwartz`,
2. `GNSHilbertSpace.lean :1062 :: gns_stronglyContinuous_preHilbert`,
3. `GNSHilbertSpace.lean :1249 :: gns_matrix_coefficient_holomorphic_axiom`,
4. the nuclear-space bridge in the exact ownership order
   `Wightman/NuclearSpaces/*` support -> optional import/re-export bridge ->
   downstream `Wightman/WightmanAxioms.lean :504/:342` theorem surfaces,
5. `GNSHilbertSpace.lean :1643 :: gns_cyclicity`,
6. `GNSHilbertSpace.lean :2114 :: gnsQFT`,
7. `Main.lean :63 :: wightman_reconstruction`,
8. only then `Main.lean :74 :: wightman_uniqueness`.

The last step is not a one-line epilogue. Source-checked file ownership for
that final lane is now part of the contract: the live tree contains no
separate `Wightman/Reconstruction/Main/*` helper module and no checked
uniqueness support `.lean` file sitting beside `Main.lean`; a direct source
check of `Wightman/Reconstruction/Main.lean` also shows that, besides the
already checked `wightman_reconstruction`, the only checked uniqueness-side
declaration presently there is `:74 :: wightman_uniqueness`. By contrast the
nuclear-side support lane really does have checked files under
`Wightman/NuclearSpaces/*`, including `Helpers/PositiveDefiniteKernels.lean`
and `NuclearOperator.lean`. So once the queue reaches `Main.lean :74`, the
later Lean transcript must be read as a documentation-owned helper package
ending at the checked theorem surface in `Main.lean`, rather than as a hidden
support-file import or a promise that names like `uniquenessPreMap` already
exist somewhere in the checked tree. Concretely, the downstream uniqueness
lane itself must run in the fixed helper order

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
-> `wightman_uniqueness`.

The queue is not just an ordering slogan; it freezes where each mathematical
responsibility begins and ends. `cyclicWordVector_inner_cyclicWordVector` is
the only slot allowed to settle the cyclic-word vacuum matrix-element formula.
`uniquenessPreMap_inner_formula` is the only transfer-across-`h` row before
quotient descent. `uniquenessPreMap_null_of_null` is the sole quotient/null
seam. `uniquenessDenseMap_inner_preserving` and
`uniquenessDenseMap_norm_preserving` begin only after the descended map exists,
and `uniquenessDenseMap_isometry` packages metric data only rather than starting
dense-range work. Dense range begins only at
`cyclicWord_in_range_of_uniquenessDenseMap -> cyclicWordSpan_le_range_uniquenessDenseMap`,
and field-domain closure begins only at `cyclicWordSpan_is_field_core`, so the
cyclic-core intertwining theorem may not hide a graph-closure argument.
Finally, `Main.lean :74 :: wightman_uniqueness` is assembly-only.

This fixes the implementation seams that were still easy to blur in overview
form: the transfer-across-`h` step is no longer collapsed into the quotient row;
descended inner/norm preservation is no longer hidden inside a generic
isometry package; dense range is the direct cyclic-word-in-range argument, not
a second inverse-map construction; the field intertwining proof reaches
arbitrary domain vectors only after the cyclic-core theorem plus the explicit
core/closure step; and file ownership is explicit — until a real support
`.lean` file is created, these helper slots belong to the
documentation/blueprint layer and culminate in the sole checked Main-side
 theorem surface `Wightman/Reconstruction/Main.lean :74`, rather than being
split across an undocumented helper module. In particular, later Lean work has
exactly two in-contract choices: either insert those helper declarations into
`Main.lean` in the order listed above and then finish `wightman_uniqueness`, or
first create a real helper module and update the ownership docs before using
it. Anything in between would reintroduce the old ambiguity about whether the
uniqueness queue is a theorem-creation contract or just a descriptive slogan.

Two anti-drift rules are part of that queue:

1. `wightman_reconstruction` is downstream packaging from `gnsQFT`, not a place
   to reopen Packages A-D;
2. `wightman_uniqueness` may consume the finished `WightmanQFT` surface only.
   It may not silently import the nuclear bridge, spectrum bridge, or cyclicity
   subproofs directly from unfinished GNS internals.

## 9. Do not do this

1. Do not hide the spectrum condition again behind one monolithic `sorry`.
2. Do not treat cyclicity as a purely algebraic statement; it is a density
   theorem.
3. Do not use new axioms for QFT-specific parts of the GNS pipeline.
4. Do not blur the boundary between SCV/forward-tube input and GNS algebra.
5. Do not prove `wightman_uniqueness` before `gns_cyclicity` is honest.

## 10. What counts as implementation-ready for this blueprint

This GNS blueprint should be considered ready for later Lean work only when the
following are explicit:

1. the theorem slots for Packages A-D,
2. the exact dependency on SCV forward-tube boundary-value results,
3. the exact dependency on the nuclear-space/kernel theorem package,
4. the assembly order into `gnsQFT`,
5. the separation of reconstruction-critical work from the standalone
   uniqueness theorem.

## 11. Recommended implementation size

Rough expected size for the later GNS pass:

1. Package A translation continuity:
   `80-140` lines,
2. Package B pre-Hilbert strong continuity:
   `60-120` lines,
3. Package C matrix-coefficient bridge:
   `180-280` lines once the SCV one-point package exists,
4. Package D cyclicity:
   `90-170` lines once the kernel theorem is honest,
5. final `gnsQFT` assembly:
   `20-40` lines.

This blueprint is implementation-ready once those five chunks are read as the
literal work units and not as one monolithic “finish GNS” task.
