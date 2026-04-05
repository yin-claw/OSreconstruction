# vNA Infrastructure Blueprint

Purpose: this note is the implementation blueprint for the remaining
von-Neumann-algebra / unbounded-operator infrastructure in `OSReconstruction/vNA`.

This area is not on the critical `E -> R` path, but it is part of the longer
operator-algebra formalization surface and should have an honest theorem-by-
theorem plan.

## 1. Live open areas

The current open/sorry-backed files include:

1. `vNA/MeasureTheory/CaratheodoryExtension.lean`,
2. `vNA/ModularTheory.lean`,
3. `vNA/ModularAutomorphism.lean`,
4. `vNA/KMS.lean`,
5. `vNA/Predual.lean`,
6. `vNA/Unbounded/StoneTheorem.lean`.

Other files such as `vNA/Bochner/CfcInfrastructure.lean` are already largely
proved and should be treated as infrastructure, not frontiers.

## 2. Package A: Measure-theoretic base

`CaratheodoryExtension.lean` is the foundational measure-theory package. Later
modular/spectral proofs should not proceed until its core extension theorems
are honest.

Documentation-standard theorem slots:

```lean
lemma outerMeasure_of_premeasure
lemma measurable_sets_form_sigmaAlgebra
lemma caratheodory_extension_exists
lemma caratheodory_extension_unique
theorem sesqForm_measure_construction
```

The later port should isolate the pure extension theorem before any Hilbert-
space-valued measure constructions.

## 3. Package B: Stone / unbounded spectral base

`Unbounded/StoneTheorem.lean` and `Unbounded/Spectral.lean` supply the operator
theory under modular theory.

The documentation should now distinguish:

1. the spectral differentiation package, which is already proved in
   `SpectralPowers.lean`,
2. the genuinely remaining Stone-side frontier, which sits in the final
   generator/time-evolution assembly.

So the theorem package should be documented as:

```lean
lemma unitaryGroup_hasDerivAt_dom
lemma unitaryGroup_preserves_domain
lemma unitaryGroup_commutes_with_generator
lemma unitaryGroup_generator_domain_eq
lemma generator_from_stronglyContinuous_unitaryGroup
lemma spectral_measure_recovers_generator
theorem stone_theorem_unbounded
```

This package should remain separate from Tomita-Takesaki. Modular theory should
consume Stone/spectral inputs, not rebuild them.

### 3.1. Exact proof route for the spectral differentiation package

The later docs should say explicitly that the spectral derivative package is a
direct spectral-measure proof:

1. prove the Parseval identity
   `‖U(h)x - x‖² = ∫ |e^{ihλ} - 1|² dμ_x(λ)`,
2. prove the domain characterization
   `x ∈ dom(T) ↔ ∫ λ² dμ_x < ∞`,
3. use dominated convergence with
   `|(e^{ihλ} - 1)/h| ≤ |λ|` to prove `unitaryGroup_hasDerivAt_dom`,
4. use invariance of the spectral measure under `U(t)` to prove
   `unitaryGroup_preserves_domain`,
5. use functional-calculus commutativity to prove
   `unitaryGroup_commutes_with_generator`,
6. use Fatou's lemma to prove `unitaryGroup_generator_domain_eq`.

So the proof pattern here is fully concrete:

1. spectral measure,
2. Parseval/integral identities,
3. DCT / Fatou,
4. functional calculus commutativity.

### 3.2. Honest remaining Stone-side frontier

The live remaining Stone-side theorem should be documented more honestly as the
final generator/time-evolution package:

```lean
lemma unique_from_generator_via_domain_ode
lemma timeEvolution_generator_sign_normalized
theorem timeEvolution_generator
```

Its proof route should be:

1. use `unitaryGroup_hasDerivAt_dom` to identify the derivative on `dom(T)`,
2. combine it with the generator integral formula,
3. prove uniqueness of the unitary group from the generator by the domain-ODE
   cancellation argument,
4. extend from the dense domain to all of `H`,
5. fix the sign convention once and state the final generator theorem.

This is much more implementation-ready than leaving Package B as
"prove Stone's theorem somehow."

## 4. Package C: Modular theory

`ModularTheory.lean` contains the Tomita / modular operator / modular
conjugation base.

The later implementation should split it into:

```lean
lemma tomita_operator_closable
lemma modular_operator_positive
lemma modular_operator_selfAdjoint
lemma modular_conjugation_exists
lemma modular_conjugation_antiunitary
theorem tomita_fundamental
```

The docs should keep the route:

1. Tomita operator,
2. closure,
3. modular operator,
4. modular conjugation,
5. fundamental theorem,

instead of mixing all five in one large proof file.

## 5. Package D: Modular automorphism group and KMS

`ModularAutomorphism.lean` and `KMS.lean` are later consumers of Package C.

Documentation-standard theorem slots:

```lean
lemma modularAutomorphismGroup_exists
lemma modularAutomorphismGroup_is_oneParameter
lemma modularAutomorphism_preserves_algebra
theorem tomita_takesaki_modular_automorphism

lemma kmsAnalyticStrip_function
lemma kmsBoundaryValues
theorem kms_condition_of_modular_group
```

These theorems should be implemented only after the core modular objects are
honest.

## 6. Package E: Predual

`Predual.lean` should be treated as its own package, not as fallout from the
modular theory files.

Documentation-standard theorem slots:

```lean
lemma vector_functionals_generate_sigmaWeak
lemma predual_exists
lemma predual_is_unique
theorem vonNeumannAlgebra_hasPredual
```

This package is conceptually downstream of the operator-topology foundations
and should not be used to justify them.

## 7. Exact dependency order

The later Lean implementation should proceed in this order:

1. Carathéodory / measure-theory base,
2. Stone/unbounded spectral base,
3. core modular theory,
4. modular automorphism group,
5. KMS package,
6. predual package.

## 8. Do not do this

1. Do not start with KMS before modular automorphisms are honest.
2. Do not start with modular theory before the Stone/spectral base is honest.
3. Do not let measure-extension sorries leak into later operator-theory files.
4. Do not treat the largely proved CFC infrastructure as if it were still a
   live blocker.

## 9. What counts as implementation-ready

This blueprint should be considered ready only when:

1. the six open areas above are separated into packages,
2. the dependency order is explicit,
3. the already-proved CFC/spectral infrastructure is treated as closed input,
4. no later operator-theory proof is allowed to hide its foundational
   dependency.

This note now records all four.
