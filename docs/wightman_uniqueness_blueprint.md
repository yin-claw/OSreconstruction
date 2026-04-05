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

So if `gns_cyclicity` is still open, the later implementation must either:

1. prove uniqueness in a general abstract GNS uniqueness library first, or
2. finish cyclicity before attempting `wightman_uniqueness`.

The docs should assume option (2), since that keeps the route closest to the
current codebase.

## 4. Theorem-slot inventory

```lean
def cyclicWordVector
    (qft : WightmanQFT d) :
    List (SchwartzSpacetime d) → qft.HilbertSpace

lemma cyclicWordVector_nil
lemma cyclicWordVector_cons

def uniquenessDenseMap
    (qft₁ qft₂ : WightmanQFT d)
    (h : ∀ n fs, qft₁.wightmanFunction n fs = qft₂.wightmanFunction n fs) :
    CyclicDenseSubspace qft₁ →ₗ[ℂ] CyclicDenseSubspace qft₂

lemma uniquenessDenseMap_wellDefined
lemma uniquenessDenseMap_inner_preserving
lemma uniquenessDenseMap_isometry
lemma uniquenessDenseMap_denseRange
lemma uniquenessDenseMap_extends_to_unitary
lemma uniquenessUnitary_maps_vacuum
lemma uniquenessUnitary_intertwines_field

theorem wightman_uniqueness
```

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

### 5.2. Isometry

Once well-definedness is proved, isometry is formal:

1. the map preserves inner products on the dense cyclic subspaces,
2. hence it preserves norms,
3. hence it extends uniquely to an isometry on the Hilbert completion.

### 5.3. Surjectivity / unitary

There are two standard routes:

1. show the same construction in the reverse direction and prove the two
   extensions are mutual inverses;
2. or show the image contains the dense cyclic subspace of `qft₂`.

The documentation-standard route should use (2), because it avoids building a
second abstract map.

### 5.4. Intertwining the field

The field intertwining theorem should be proved only after the unitary exists.

Exact route:

1. first prove the intertwining identity on cyclic vectors in the field domain,
2. then lift it to the stated domain theorem in `Main.lean`.

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
   in the existence proof.

This note now records all four.
