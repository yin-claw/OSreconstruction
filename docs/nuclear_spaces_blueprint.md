# Nuclear Spaces Blueprint

Purpose: this note is the implementation blueprint for the nuclear-space and
Bochner-Minlos packages that feed the Wightman kernel theorem and the Euclidean
measure side.

It should be read together with:
- `docs/gns_pipeline_blueprint.md`,
- `docs/gns-pipeline-sorries.md`,
- `docs/r_to_e_blueprint.md`.

## 1. Live frontier surfaces

The relevant current open theorem surfaces are:

1. `subspace_seminorm_dominated` and `product_seminorm_dominated` in
   `Wightman/NuclearSpaces/NuclearSpace.lean`,
2. the Bochner-Minlos sorries in
   `Wightman/NuclearSpaces/BochnerMinlos.lean`,
3. the axioms
   `schwartz_nuclear_extension` and
   `exists_continuousMultilinear_ofSeparatelyContinuous`
   in `Wightman/WightmanAxioms.lean`.

These are not independent. They form one package:

1. nuclearity of the relevant Schwartz/Frechet spaces,
2. separately continuous multilinear maps become jointly continuous,
3. joint continuity feeds the Schwartz kernel theorem,
4. the kernel theorem feeds GNS cyclicity and Wightman packaging,
5. Bochner-Minlos feeds the measure-based Euclidean examples.

## 2. What is already available

The docs should treat the following as clean inputs:

1. `GaussianFieldBridge.lean` provides sorry-free Hermite and Gaussian
   infrastructure,
2. `ComplexSchwartz.lean` already transports nuclearity across complexification,
3. the basic `NuclearSpace` API exists and only two dominance theorems remain
   sorry-backed.

So the later implementation should not start from “what is a nuclear space?”
It should start from the two remaining dominance lemmas and the kernel-theorem
consumer interfaces.

## 3. Package A: Nuclearity infrastructure

The current explicit blockers in `NuclearSpace.lean` are:

1. `gauge_dominates_on_subspace_of_convex_nhd`,
2. `product_seminorm_dominated`.

These feed:

1. `subspace_seminorm_dominated`,
2. `subspace_nuclear`,
3. `product_nuclear`.

Documentation-standard theorem slots:

```lean
lemma gauge_dominates_on_subspace_of_convex_nhd
theorem subspace_seminorm_dominated
theorem subspace_nuclear

lemma product_coordinate_seminorm_control
theorem product_seminorm_dominated
theorem product_nuclear
```

The proof discipline should be:

1. prove subspace domination geometrically from convex neighborhoods and the
   gauge construction,
2. prove product domination from countable seminorm bookkeeping,
3. only then apply the generic nuclear-space closure lemmas already in the file.

## 4. Package B: Separate continuity to joint continuity

The axiom

```lean
exists_continuousMultilinear_ofSeparatelyContinuous
```

should eventually be replaced by a theorem package with exact slots:

```lean
lemma schwartz_isFrechet
lemma separatelyContinuous_multilinear_on_frechet
theorem exists_continuousMultilinear_ofSeparatelyContinuous
```

This is the Banach-Steinhaus / Frechet-space package. The docs should keep it
separate from the nuclear theorem itself.

## 5. Package C: Schwartz kernel / nuclear theorem

The axiom

```lean
schwartz_nuclear_extension
```

is the next package and should be treated as the main direct consumer of
Packages A and B.

Documentation-standard theorem slots:

```lean
lemma schwartz_productTensor_dense
lemma schwartz_joint_space_nuclear
lemma multilinear_to_linear_kernel_candidate
lemma kernel_candidate_agrees_on_productTensor
theorem schwartz_nuclear_extension
```

This package is what later closes:

1. `wightmanDistribution_extends`,
2. `gns_cyclicity`,
3. any “product tests are dense” statements in the GNS uniqueness lane.

## 6. Package D: Bochner finite-dimensional existence

The first open finite-dimensional theorem is:

```lean
private theorem bochner_tightness_and_limit
```

The later implementation should decompose it into:

1. approximate finite measures from mollified/compactly truncated data,
2. tightness,
3. weak-limit extraction,
4. characteristic-function recovery.

Documentation-standard theorem slots:

```lean
lemma bochner_approximate_measures_exist
lemma bochner_approximate_measures_tight
lemma bochner_weak_limit_exists
lemma bochner_limit_has_correct_characteristic_function
theorem bochner_tightness_and_limit
theorem bochner_existence
theorem bochner_theorem
```

## 7. Package E: Minlos projective family and uniqueness

The open Minlos-side theorems are:

1. `minlos_projective_consistency`,
2. `minlos_nuclearity_tightness`,
3. `eval_maps_generate_sigma_algebra`,
4. `eval_charfun_implies_fd_distributions`,
5. the downstream `minlos_theorem` / `minlos_unique` consumers.

The implementation order should be:

1. finite-dimensional projection measures,
2. projective consistency,
3. nuclearity-driven tightness,
4. Kolmogorov/projective extension,
5. uniqueness from evaluation-characteristic functions.

Documentation-standard theorem slots:

```lean
lemma minlos_finite_dim_projection
lemma minlos_projective_consistency
lemma minlos_nuclearity_tightness
lemma minlos_kolmogorov_extension
theorem minlos_theorem

lemma eval_maps_generate_sigma_algebra
lemma eval_charfun_implies_fd_distributions
theorem measures_eq_of_eval_charfun_eq
theorem minlos_unique
```

## 8. Exact dependency graph

The later implementation should proceed in this order:

1. finish `NuclearSpace.lean` dominance lemmas,
2. replace separate-continuity axiom,
3. replace Schwartz nuclear-extension axiom,
4. close `gns_cyclicity`,
5. separately finish the Bochner finite-dimensional existence package,
6. then the Minlos projective/tightness/uniqueness package.

The docs should not present Bochner-Minlos as if it were required before the
GNS/kernel theorem. They are parallel consumers of overlapping nuclear-space
infrastructure.

## 9. Lean-style pseudocode for the kernel-theorem consumer side

```lean
theorem wightmanDistribution_extends (qft : WightmanQFT d) (n : ℕ) :
    ∃ W_n : SchwartzMap (NPointDomain d n) ℂ →L[ℂ] ℂ,
      ∀ fs, W_n (SchwartzMap.productTensor fs) =
        qft.vacuumExpectation n fs := by
  obtain ⟨PhiCont, hPhiCont⟩ :=
    exists_continuousMultilinear_ofSeparatelyContinuous
      (d := d) (n := n) (wightman_separately_continuous qft n)
  obtain ⟨W_n, hW_n, _⟩ := schwartz_nuclear_extension (d := d) (n := n) PhiCont
  exact ⟨W_n, hW_n⟩
```

## 10. Do not do this

1. Do not mix the Frechet separate-continuity theorem with the kernel theorem.
2. Do not treat Bochner and Minlos as one undifferentiated measure theorem.
3. Do not reopen the sorry-free GaussianFieldBridge package.
4. Do not let GNS cyclicity smuggle in the nuclear theorem implicitly.

## 11. What counts as implementation-ready

This blueprint should be considered ready only when:

1. the two open `NuclearSpace.lean` dominance lemmas are isolated,
2. the two current axioms are split into theorem packages,
3. the Bochner and Minlos packages are separated into finite-dimensional,
   projective, tightness, and uniqueness layers,
4. the dependency from these packages to GNS cyclicity is explicit.

This note now records all four.
