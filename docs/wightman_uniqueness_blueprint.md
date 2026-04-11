# Wightman Uniqueness Blueprint

Purpose: this note is the implementation blueprint for the standalone theorem

- `wightman_uniqueness` in `Wightman/Reconstruction/Main.lean`.

It should be read together with:
- `docs/gns_pipeline_blueprint.md`,
- `docs/gns-pipeline-sorries.md`.

## 1. The live theorem

The theorem surface is:

```lean
theorem wightman_uniqueness (qft₁ qft₂ : WightmanQFT d)
```

Source-checked checked-tree anchors for this clone:

1. `Wightman/Reconstruction/Main.lean :74 :: wightman_uniqueness` is the only
   live uniqueness theorem surface;
2. `Wightman/Reconstruction/GNSHilbertSpace.lean :2114 :: gnsQFT` is the
   finished-construction surface uniqueness is allowed to consume;
3. `Wightman/Reconstruction/GNSHilbertSpace.lean :1643 :: gns_cyclicity` is
   the last GNS-internal theorem uniqueness is allowed to depend on;
4. the repo really does contain checked upstream support files under
   `Wightman/NuclearSpaces/*`, including
   `Helpers/PositiveDefiniteKernels.lean` and `NuclearOperator.lean`, but those
   stay upstream of GNS and are not Main-side uniqueness owners;
5. no uniqueness proof step is allowed to reach back into the upstream GNS
   spectrum bridge (`:1005`, `:1062`, `:1249`) or the nuclear support lane
   except through the completed `WightmanQFT` structure and cyclicity facts
   already exported by `gnsQFT`;
6. a direct tree scan also shows there is **no separate checked uniqueness
   helper module** under `Wightman/Reconstruction/` beyond `Main.lean` itself,
   so the helper queue in this blueprint is documentation-owned until a real
   support file is added.

It is not on the reconstruction critical path, but it is the clean endgame
companion to `wightman_reconstruction`.

## 2. Mathematical route

The standard GNS uniqueness proof should be formalized exactly as:

1. define a map on the cyclic word vectors
   `φ₁(f₁)...φ₁(fₙ)Ω₁ ↦ φ₂(f₁)...φ₂(fₙ)Ω₂`,
2. prove the map is well-defined using equality of all smeared n-point
   functions,
3. prove it preserves inner products on the dense cyclic subspaces,
4. extend it by continuity to a unitary on the completed Hilbert spaces,
5. prove it sends vacuum to vacuum and intertwines the field operators.

## 3. Exact prerequisites

The uniqueness theorem depends on:

1. cyclicity for each QFT,
2. the reproducing identity for vacuum matrix elements,
3. the field-domain description by cyclic word vectors,
4. density of the cyclic span in both Hilbert spaces.

The dependency boundary is now frozen more sharply:

1. uniqueness may consume `gns_cyclicity` as an already-finished theorem
   surface, but it is not allowed to absorb cyclicity's kernel-theorem or
   quotient-density work into a hidden preliminary block;
2. uniqueness also may not reopen the `gns_matrix_coefficient_holomorphic_axiom`
   or translation-continuity lane, because those are spectrum-condition owners,
   not uniqueness owners;
3. the only admissible upstream GNS boundary is therefore
   `gnsQFT -> cyclicity facts -> Main.lean :74 :: wightman_uniqueness`.

So if `gns_cyclicity` is still open, the later implementation must either:

1. prove uniqueness in a general abstract GNS uniqueness library first, or
2. finish cyclicity before attempting `wightman_uniqueness`.

The docs should assume option (2), since that keeps the route closest to the
current codebase.

## 4. Theorem-slot inventory

The uniqueness lane needs a stricter split than the earlier shorthand
`uniquenessDenseMap_wellDefined`. That label was too coarse because it blurred
three distinct ownership steps: the cyclic-word core formula, the null-vector
quotient descent, and only then the descended dense-subspace map. The literal
Main-file slot order should be frozen as:

```lean
def cyclicWordVector
    (qft : WightmanQFT d) :
    List (SchwartzSpacetime d) → qft.HilbertSpace

def cyclicWordSpan (qft : WightmanQFT d) : Submodule ℂ qft.HilbertSpace
lemma cyclicWordVector_nil
lemma cyclicWordVector_cons
lemma cyclicWordVector_mem_domain
lemma cyclicWordSpan_eq_vacuum_algebraicSpan
lemma cyclicWordSpan_dense
lemma cyclicWordVector_inner_cyclicWordVector

def uniquenessPreMap
    (qft₁ qft₂ : WightmanQFT d)
    (h : ∀ n fs, qft₁.wightmanFunction n fs = qft₂.wightmanFunction n fs) :
    FreeCyclicWordSpan qft₁ →ₗ[ℂ] FreeCyclicWordSpan qft₂

lemma uniquenessPreMap_inner_formula
lemma uniquenessPreMap_null_of_null

def uniquenessDenseMap
    (qft₁ qft₂ : WightmanQFT d)
    (h : ∀ n fs, qft₁.wightmanFunction n fs = qft₂.wightmanFunction n fs) :
    CyclicDenseSubspace qft₁ →ₗ[ℂ] CyclicDenseSubspace qft₂

lemma uniquenessDenseMap_inner_preserving
lemma uniquenessDenseMap_norm_preserving
lemma uniquenessDenseMap_isometry
lemma cyclicWord_in_range_of_uniquenessDenseMap
lemma cyclicWordSpan_le_range_uniquenessDenseMap
lemma uniquenessDenseMap_denseRange
lemma uniquenessDenseMap_extends_to_unitary
lemma uniquenessUnitary_maps_vacuum
lemma uniquenessUnitary_intertwines_field_on_cyclic_core
lemma cyclicWordSpan_is_field_core
lemma uniquenessUnitary_intertwines_field

theorem wightman_uniqueness
```

Read that list as an ownership ledger, not a bag of optional helpers:

1. `cyclicWordVector` / `cyclicWordSpan` / `cyclicWordVector_inner_cyclicWordVector`
   own the dense-core and vacuum-matrix-element formula;
2. `uniquenessPreMap` / `uniquenessPreMap_null_of_null` own the only real
   quotient-descent step;
3. `uniquenessDenseMap` starts only after null-vector descent is finished;
4. dense range must be proved by the direct cyclic-word-in-range route rather
   than by inventing a reverse abstract map;
5. field intertwining splits into `..._on_cyclic_core` first and only then the
   domain/core extension theorem;
6. because the current tree has no separate checked uniqueness-helper file,
   this ledger is also the file-creation contract: if later Lean work decides
   to factor out a helper module before filling `Main.lean`, it must do so
   explicitly rather than pretending these names already live in an unnamed
   support file.

Without this split, later Lean work would still have to rediscover where the
quotient argument ends, where dense-range begins, and where the field-domain
closure step first enters.

### 4.1. Slot-by-slot owner / consumes / exports / first-consumer contract

Read the Main-side queue as a literal execution ledger, not just a list of
names. In the current checked tree there is still no separate uniqueness helper
file, so each row below is a documentation-owned slot that must either be
implemented in `Main.lean` in this order or moved, explicitly and visibly, into
an actually created helper module.

| Slot | Local owner today | Must consume directly | Must export / settle | First downstream consumer |
| --- | --- | --- | --- | --- |
| `cyclicWordVector`, `cyclicWordSpan`, `cyclicWordVector_nil`, `..._cons`, `..._mem_domain`, `cyclicWordSpan_eq_vacuum_algebraicSpan`, `cyclicWordSpan_dense` | documentation-owned Main-side slot | only `WightmanQFT` field/vacuum/domain surfaces plus finished cyclicity facts already exported by `gnsQFT` | explicit cyclic-word generating family, span, domain membership, and density package | `cyclicWordVector_inner_cyclicWordVector` and later `cyclicWordSpan_le_range_uniquenessDenseMap` / `cyclicWordSpan_is_field_core` |
| `cyclicWordVector_inner_cyclicWordVector` | documentation-owned Main-side slot | the cyclic-word core package above plus the checked `qft.wightmanFunction` surface and field adjoint/domain axioms already inside `WightmanQFT` | exact `(Fs.length + Gs.length)` vacuum matrix-element formula on cyclic words | `uniquenessPreMap_inner_formula`, `uniquenessPreMap_null_of_null`, `uniquenessDenseMap_inner_preserving` |
| `uniquenessPreMap`, `uniquenessPreMap_inner_formula` | documentation-owned Main-side slot | only the cyclic-word inner-product formula plus the hypothesis `h` equating Wightman functions | linear pre-map on free cyclic-word combinations together with its transferred inner-product formula | `uniquenessPreMap_null_of_null` |
| `uniquenessPreMap_null_of_null` | documentation-owned Main-side slot | only `uniquenessPreMap_inner_formula` and the quotient/null-space norm-zero criterion for the cyclic pre-Hilbert package | the sole quotient-descent permission for the lane | `uniquenessDenseMap` |
| `uniquenessDenseMap`, `uniquenessDenseMap_inner_preserving`, `uniquenessDenseMap_norm_preserving`, `uniquenessDenseMap_isometry` | documentation-owned Main-side slot | only the descended quotient map from `uniquenessPreMap_null_of_null`; do **not** reopen cyclic-word expansion or invent a second quotient proof here | honest dense-subspace map + isometry package | `cyclicWord_in_range_of_uniquenessDenseMap`, `uniquenessDenseMap_extends_to_unitary` |
| `cyclicWord_in_range_of_uniquenessDenseMap` | documentation-owned Main-side slot | only the explicit definition of `uniquenessDenseMap` and the cyclic-word generators | pointwise range witnesses for each cyclic-word vector in `qft₂` | `cyclicWordSpan_le_range_uniquenessDenseMap` |
| `cyclicWordSpan_le_range_uniquenessDenseMap` | documentation-owned Main-side slot | only the previous row plus the algebraic-span definition of `cyclicWordSpan` | span-level range inclusion | `uniquenessDenseMap_denseRange` |
| `uniquenessDenseMap_denseRange` | documentation-owned Main-side slot | only `cyclicWordSpan_le_range_uniquenessDenseMap` together with `cyclicWordSpan_dense` for `qft₂` | dense range for the isometric dense-subspace map | `uniquenessDenseMap_extends_to_unitary` |
| `uniquenessDenseMap_extends_to_unitary` | documentation-owned Main-side slot | only `uniquenessDenseMap_isometry` + `uniquenessDenseMap_denseRange` and the standard completion-extension theorem | unitary `U` extending the dense map | `uniquenessUnitary_maps_vacuum`, `uniquenessUnitary_intertwines_field_on_cyclic_core` |
| `uniquenessUnitary_maps_vacuum` | documentation-owned Main-side slot | only the extension identity for `U` plus `cyclicWordVector_nil` / `cyclicWordSpan_eq_vacuum_algebraicSpan` or an equivalent vacuum-as-empty-word fact | the explicit theorem `U qft₁.vacuum = qft₂.vacuum` | final `wightman_uniqueness` assembly |
| `uniquenessUnitary_intertwines_field_on_cyclic_core` | documentation-owned Main-side slot | only the unitary extension identity, the cyclic-word constructors, and the field action on cyclic words; do **not** use arbitrary-domain closure here | field intertwining on the cyclic core only | `uniquenessUnitary_intertwines_field` |
| `cyclicWordSpan_is_field_core` | documentation-owned Main-side slot | only the cyclic span package and the checked field-domain/graph closure facts exported by `WightmanQFT`; no new spectrum/nuclear/cyclicity work allowed | the separate core theorem needed to pass from cyclic vectors to all domain vectors | `uniquenessUnitary_intertwines_field` |
| `uniquenessUnitary_intertwines_field` | documentation-owned Main-side slot | only `uniquenessUnitary_intertwines_field_on_cyclic_core` + `cyclicWordSpan_is_field_core` | full domain-level intertwining theorem | final `wightman_uniqueness` assembly |
| `wightman_uniqueness` | checked target theorem in `Main.lean:74` | only `uniquenessUnitary_maps_vacuum` + `uniquenessUnitary_intertwines_field` | final unitary-equivalence theorem surface | none |

This table removes the remaining implementation ambiguity about where each
proof step is first allowed to consume the previous one. In particular:

1. quotient descent is exhausted at `uniquenessPreMap_null_of_null`;
2. dense range starts only at the explicit range-witness row, not at
   `uniquenessDenseMap_isometry`;
3. field-domain closure starts only at `cyclicWordSpan_is_field_core`, not
   inside the cyclic-core intertwining lemma;
4. the final theorem at `Main.lean:74` is assembly-only and may not hide a
   second descent, dense-range, or closure argument.

### 4.2. Exact file-ownership / insertion contract

The queue above is now fixed strongly enough that later Lean work should not
have to guess where the declarations physically live. Against the current checked
repo tree there are only two admissible implementation layouts:

1. **Direct-in-`Main.lean` layout**
   - create the slots `cyclicWordVector` through
     `uniquenessUnitary_intertwines_field` directly in
     `Wightman/Reconstruction/Main.lean`, above the existing theorem
     `Main.lean:74 :: wightman_uniqueness`;
   - keep the same order as the slot ledger above;
   - do not insert a hidden local “helper block” whose internal theorem order
     differs from the documented queue.
2. **Explicit helper-module layout**
   - first create a real Lean file under `Wightman/Reconstruction/` with an
     explicit name such as `MainUniqueness.lean` or `Uniqueness.lean`;
   - move an initial contiguous prefix of the queue there (for example the
     cyclic-word core plus quotient/descent package, or the whole helper queue
     except the final theorem);
   - update imports plus all planning/status docs so the new file becomes the
     named owner of those slots instead of leaving `docs/wightman_uniqueness_blueprint.md`
     as the only owner record.

What is **not** admissible:

1. acting as if a hidden uniqueness helper file already exists somewhere in the
   current tree;
2. introducing slot names in proofs or comments without first giving them a
   visible file home;
3. splitting the queue across multiple new files without documenting which file
   owns which consecutive theorem block;
4. leaving `Main.lean:74` as a mixed theorem-plus-helper construction where the
   descent, dense-range, or field-core closure arguments are partly hidden in
   unnamed local lets.

So the file-ownership rule is now literal: either implement the queue in
`Main.lean` in the documented order, or create an explicitly named helper file
and transfer ownership there visibly. No third layout is endorsed by the docs.

## 5. Exact proof decomposition

### 5.1. Well-definedness

To prove the map on cyclic words is well-defined:

1. expand the inner product of two cyclic words on the first QFT,
2. rewrite it entirely as an `(n+m)`-point vacuum expectation,
3. apply the hypothesis `h`,
4. identify the same number as the inner product of the corresponding cyclic
   words on the second QFT.

The proof should not invoke abstract operator-algebra uniqueness theorems at
this stage. It should use the repo’s explicit Wightman-function interface.

### 5.1.1. Exact quotient/descent mechanism

The implementation should not leave the descent step implicit. The correct
order is:

1. define a pre-map on the free finite span of cyclic words,
2. prove that if `ξ` has zero norm in `qft₁`, then its image has zero norm in
   `qft₂`,
3. descend from the pre-Hilbert quotient by the null space,
4. only then package the descended map as `uniquenessDenseMap`.

So the actual theorem slots should be thought of as:

```lean
def uniquenessPreMap :
    FreeCyclicWordSpan qft₁ →ₗ[ℂ] FreeCyclicWordSpan qft₂

lemma uniquenessPreMap_inner_formula
lemma uniquenessPreMap_null_of_null
def uniquenessDenseMap :
    CyclicDenseSubspace qft₁ →ₗ[ℂ] CyclicDenseSubspace qft₂
```

The key proof of `uniquenessPreMap_null_of_null` is:

1. assume `‖ξ‖ = 0` in the quotient on the `qft₁` side,
2. rewrite `‖ξ‖²` as `⟪ξ, ξ⟫`,
3. expand that inner product by `uniquenessPreMap_inner_formula`, whose only
   real content is repeated reduction to `cyclicWordVector_inner_cyclicWordVector`,
4. transfer the resulting scalar to the `qft₂` side by the hypothesis `h`,
5. rewrite back to the `qft₂` norm square,
6. conclude the image also has norm square zero.

Operational rule: after this theorem closes, the later Lean file must treat the
quotient issue as finished. `uniquenessDenseMap` and every later row may use
this descent theorem, but they may not silently reopen representative-choice or
null-space arguments.

This is the only non-formal descent step. Once it is proved, the quotient map
is honest.

### 5.1.2. Exact cyclic-word inner-product formula

The implementation should explicitly prove the formula:

```lean
lemma cyclicWordVector_inner_cyclicWordVector
    (Fs : List (SchwartzSpacetime d)) (Gs : List (SchwartzSpacetime d)) :
    ⟪cyclicWordVector qft Fs, cyclicWordVector qft Gs⟫_ℂ
      =
    qft.wightmanFunction (Fs.length + Gs.length)
      (joinedConjugatedTestFamily Fs Gs)
```

The proof is by induction on `Fs`, pushing adjoints across the vacuum and using
the Wightman hermiticity/domain axioms already packaged in `WightmanQFT`.

That theorem is the real heart of uniqueness. All later inner-product
preservation statements should be short corollaries of it.

### 5.2. Isometry

Once well-definedness is proved, isometry is formal:

1. the map preserves inner products on the dense cyclic subspaces,
2. hence it preserves norms,
3. hence it extends uniquely to an isometry on the Hilbert completion.

The later Lean file should split that into:

```lean
lemma uniquenessDenseMap_inner_preserving
lemma uniquenessDenseMap_norm_preserving
lemma uniquenessDenseMap_isometry
```

so that the completion-extension theorem can consume the isometry theorem
directly, with no hidden algebra.

### 5.3. Surjectivity / unitary

There are two standard routes:

1. show the same construction in the reverse direction and prove the two
   extensions are mutual inverses;
2. or show the image contains the dense cyclic subspace of `qft₂`.

The documentation-standard route should use (2), because it avoids building a
second abstract map.

### 5.3.1. Exact dense-range proof

The dense-range proof should be written literally as:

1. every cyclic word vector in `qft₂` is the image of the corresponding cyclic
   word vector in `qft₁`, proved in the standalone witness slot
   `cyclicWord_in_range_of_uniquenessDenseMap`,
2. only then upgrade those pointwise witnesses to the span inclusion theorem
   `cyclicWordSpan_le_range_uniquenessDenseMap`,
3. invoke `cyclicWordSpan_dense` for `qft₂` to obtain
   `uniquenessDenseMap_denseRange`,
4. only after the dense-range theorem is closed feed the pair
   `uniquenessDenseMap_isometry + uniquenessDenseMap_denseRange` to the
   completion-extension theorem,
5. package the resulting unitary in `uniquenessDenseMap_extends_to_unitary`.

This avoids ever needing a second inverse construction.

The theorem slots should therefore be:

```lean
lemma cyclicWord_in_range_of_uniquenessDenseMap
lemma cyclicWordSpan_le_range_uniquenessDenseMap
lemma uniquenessDenseMap_denseRange
lemma uniquenessDenseMap_extends_to_unitary
```

### 5.3.2. Exact completion-extension proof transcript

The unitary-extension row should also be read as a literal Lean transcript,
not as a slogan "apply completion". The correct local order is:

1. start only from the already-closed metric package
   `uniquenessDenseMap_isometry` plus the already-closed dense-range theorem
   `uniquenessDenseMap_denseRange`,
2. invoke the standard completion-extension theorem to obtain the unique
   isometric extension `U` of `uniquenessDenseMap` to the Hilbert completion,
3. use the dense-range theorem to upgrade that extension from a mere isometric
   embedding to a surjective linear isometry,
4. package the result once and for all as the unitary exported by
   `uniquenessDenseMap_extends_to_unitary`, together with its extension
   identity on the dense cyclic subspace,
5. forbid every later row from reopening completion existence, surjectivity,
   or inverse construction.

Operationally, that means the row
`uniquenessDenseMap_extends_to_unitary` must export both:

1. the unitary `U`, and
2. the exact extension identity saying `U` agrees with
   `uniquenessDenseMap` on the dense cyclic subspace.

Both downstream consumers use that same package:

1. `uniquenessUnitary_maps_vacuum` needs the extension identity specialized to
   the empty cyclic word;
2. `uniquenessUnitary_intertwines_field_on_cyclic_core` needs the extension
   identity on nonempty cyclic words.

So no later theorem is allowed to construct a second extension or to prove
surjectivity by manufacturing a reverse unitary after this row has closed.

### 5.4. Intertwining the field

The field intertwining theorem should be proved only after the unitary exists.

Exact route:

1. first prove the intertwining identity on cyclic vectors in the field domain,
2. then lift it to the stated domain theorem in `Main.lean`.

### 5.4.1. Exact field-domain proof transcript

The later Lean proof should not try to prove intertwining on an arbitrary
domain vector first. The correct order is:

1. prove
   `U (fieldWordAction qft₁ f ξ) = fieldWordAction qft₂ f (U ξ)`
   on the cyclic-word span,
2. identify the cyclic-word span as a core inside `qft₁.field.domain`,
3. use closedness/continuity of the field operators on their domains to extend
   the intertwining identity from the core to every `ψ ∈ qft₁.field.domain`.

So the actual theorem-slot inventory should include:

```lean
lemma uniquenessUnitary_intertwines_field_on_cyclic_core
lemma cyclicWordSpan_is_field_core
lemma uniquenessUnitary_intertwines_field
```

This keeps the domain argument honest and prevents the final theorem from
hiding an unproved graph-closure step.

### 5.4.2. Exact `cyclicWordSpan_is_field_core` sub-transcript

The separate core theorem is still easy to under-specify, so its local proof
order is now frozen too. Later Lean work should read
`cyclicWordSpan_is_field_core` as the theorem that packages exactly the
following four moves, in this order:

1. show every cyclic word vector lies in `qft.field.domain`, using only the
   already-closed cyclic-word constructor/domain lemmas from the first package;
2. upgrade that pointwise domain-membership statement to a span-level theorem
   saying `cyclicWordSpan qft ≤ qft.field.domain`;
3. invoke only the checked field-domain / graph-closure / core facts already
   exported by `WightmanQFT` to state that this span is a core for the field
   operator;
4. export the resulting core theorem once, under the name
   `cyclicWordSpan_is_field_core`, and forbid later rows from reopening the
   span-in-domain argument or graph-closure packaging.

What this is **not** allowed to do:

1. it may not reprove cyclicity or density from scratch;
2. it may not rebuild the cyclic-word span under a second name;
3. it may not already prove the full intertwining theorem on arbitrary domain
   vectors;
4. it may not import any spectrum-condition, nuclear-space, or GNS-construction
   work beyond the field/domain surfaces already exported inside `WightmanQFT`.

So the local consumer boundary is now literal:

`cyclicWordVector_mem_domain`
-> span-level domain inclusion for `cyclicWordSpan`
-> checked field-core / graph-closure facts from `WightmanQFT`
-> `cyclicWordSpan_is_field_core`
-> `uniquenessUnitary_intertwines_field`.

### 5.4.3. Exact final domain-extension transcript

The theorem `uniquenessUnitary_intertwines_field` should then be read as a
separate three-step theorem, not as a continuation of the cyclic-core lemma:

1. start only from `uniquenessUnitary_intertwines_field_on_cyclic_core`,
2. import `cyclicWordSpan_is_field_core` as the sole permission to pass from
   the cyclic span to arbitrary domain vectors,
3. use the checked closedness/core-extension principle for the field operators
   to extend the equality from the core to every `ψ ∈ qft₁.field.domain`.

After this row closes, the field-domain argument is finished. The final theorem
`wightman_uniqueness` may only assemble
`uniquenessUnitary_maps_vacuum` together with
`uniquenessUnitary_intertwines_field`; it may not do any residual closure or
domain bookkeeping itself.

## 6. Lean-style pseudocode

```lean
theorem wightman_uniqueness (qft₁ qft₂ : WightmanQFT d)
    (h : ∀ n : ℕ, ∀ fs : Fin n → SchwartzSpacetime d,
      qft₁.wightmanFunction n fs = qft₂.wightmanFunction n fs) :
    ∃ U : qft₁.HilbertSpace →ₗᵢ[ℂ] qft₂.HilbertSpace,
      U qft₁.vacuum = qft₂.vacuum ∧
      (∀ (f : SchwartzSpacetime d) (ψ : qft₁.HilbertSpace),
        ψ ∈ qft₁.field.domain →
        U (qft₁.field.operator f ψ) = qft₂.field.operator f (U ψ)) := by
  let T := uniquenessDenseMap qft₁ qft₂ h
  have hT_iso : Isometry T := uniquenessDenseMap_isometry qft₁ qft₂ h
  have hT_dense : DenseRange T := uniquenessDenseMap_denseRange qft₁ qft₂ h
  obtain ⟨U, hU_ext⟩ := uniquenessDenseMap_extends_to_unitary qft₁ qft₂ h hT_iso hT_dense
  refine ⟨U, ?_, ?_⟩
  · exact uniquenessUnitary_maps_vacuum qft₁ qft₂ h hU_ext
  · intro f ψ hψ
    exact uniquenessUnitary_intertwines_field qft₁ qft₂ h hU_ext f ψ hψ
```

## 7. Do not do this

1. Do not re-prove the whole GNS construction in the uniqueness theorem.
2. Do not hide the dense cyclic subspace inside an opaque quotient argument.
3. Do not use a theorem about “same Wightman functions implies same GNS space”
   unless it is made explicit in the repo under a named theorem.
4. Do not mix this theorem with the `R -> E` or `E -> R` routes.

## 8. What counts as implementation-ready

This uniqueness blueprint should be considered ready only when:

1. the dense cyclic-word map is explicitly named,
2. well-definedness/isometry/dense-range/unitary-extension are split,
3. the dependency on cyclicity is stated openly,
4. the field intertwining is documented as a post-unitary theorem, not hidden
   in the existence proof,
5. the physical file layout is unambiguous: either direct insertion into
   `Main.lean` in queue order, or an explicitly created/helper-named
   `Wightman/Reconstruction/*` support file with updated ownership docs.

## 9. Recommended implementation order and size

The later Lean work should attack this file in the following order:

1. cyclic-word core definitions and domain lemmas,
2. cyclic-word inner-product formula,
3. pre-map and quotient descent,
4. dense-range/unitary extension,
5. field-core intertwining,
6. final assembly theorem.

In checked owner/consumer language, read that queue as:

`cyclicWordVector` / `cyclicWordSpan`
-> `cyclicWordVector_inner_cyclicWordVector`
-> `uniquenessPreMap`
-> `uniquenessPreMap_null_of_null`
-> `uniquenessDenseMap`
-> `uniquenessDenseMap_isometry`
-> `cyclicWord_in_range_of_uniquenessDenseMap`
-> `cyclicWordSpan_le_range_uniquenessDenseMap`
-> `uniquenessDenseMap_denseRange`
-> `uniquenessDenseMap_extends_to_unitary`
-> `uniquenessUnitary_maps_vacuum`
-> `uniquenessUnitary_intertwines_field_on_cyclic_core`
-> `cyclicWordSpan_is_field_core`
-> `uniquenessUnitary_intertwines_field`
-> `Main.lean :74 :: wightman_uniqueness`.

Anti-drift rule: the final theorem is only the consumer of this queue. It is
not allowed to hide a second quotient-descent proof, a second dense-range
construction, or a first-use cyclicity argument inside the closing `by` block.

Rough expected size:

1. cyclic-word core and density: 120-180 lines,
2. inner-product formula and descent: 120-180 lines,
3. unitary extension and intertwining: 80-140 lines,
4. final assembly theorem: 20-40 lines.

This note is implementation-ready once those six steps are read as the literal
construction order rather than as a high-level summary.
