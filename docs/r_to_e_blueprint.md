# R-to-E Blueprint

Purpose: this note is the implementation blueprint for the current reverse
reconstruction direction on `main`.

It documents two different theorem surfaces:

1. the theorem that already exists in production,
2. the fuller OS I Section 5 theorem package that would verify the Euclidean
   axioms directly for the constructed Schwinger family.

This note should be read together with:
- `docs/os1_detailed_proof_audit.md`, Section 10,
- `docs/os2_detailed_proof_audit.md` only for the background BHW/continuation
  route,
- `docs/theorem3_os_route_blueprint.md` only for the warning against false
  same-pairing theorem shapes.

## 1. The current production theorem surface

The current theorem on `main` is:

```lean
theorem wightman_to_os_full
```

in `OSToWightmanBoundaryValues.lean`.

Its exact statement is:

1. construct `S := constructZeroDiagonalSchwingerFunctions Wfn`,
2. prove every `S n` is continuous,
3. prove every `S n` is linear,
4. prove `IsWickRotationPair S Wfn.W`.

So current `main` does **not** claim "the constructed family already satisfies
all OS axioms as a packaged `OsterwalderSchraderAxioms` structure." It claims
the honest weaker bridge theorem `IsWickRotationPair`.

That theorem surface is already proved.

## 2. Exact production hooks already used

The current proof of `wightman_to_os_full` uses only:

1. `constructZeroDiagonalSchwingerFunctions`
   from `BHWTranslation.lean`,
2. `constructedSchwinger_tempered_zeroDiagonal`
   from `SchwingerTemperedness.lean`,
3. `constructedZeroDiagonalSchwinger_linear`
   from `SchwingerAxioms.lean`,
4. `W_analytic_BHW`
   from `BHWExtension.lean`,
5. `bhw_distributional_boundary_values`
   from `BHWTranslation.lean`.

So the currently proved theorem is a very clean OS-I Section 5 bridge:

1. build the common BHW holomorphic object,
2. Wick-restrict it to obtain the Euclidean family,
3. prove continuity and linearity,
4. prove the boundary-value pairing compatibility.

## 3. The exact constructed object

The Euclidean family used on the reverse route is

```lean
def constructSchwingerFunctions (Wfn : WightmanFunctions d) :
    SchwingerFunctions d :=
  fun n f => wickRotatedBoundaryPairing Wfn n f.1
```

and

```lean
abbrev constructZeroDiagonalSchwingerFunctions (Wfn : WightmanFunctions d) :
    ZeroDiagonalSchwingerFunctions d := constructSchwingerFunctions Wfn
```

in `BHWTranslation.lean`.

So the reverse route is already faithful to OS I Section 5 at the level of the
basic object: the Schwinger family is defined by Wick restriction of the common
holomorphic Wightman object, not by an unrelated algebraic formula.

## 4. What is already done versus what is still a larger theorem package

The current production theorem already proves:

1. the constructed Euclidean family exists,
2. it is continuous,
3. it is linear,
4. it is paired correctly with the given Wightman family through
   `IsWickRotationPair`.

The fuller OS I Section 5 theorem package would additionally verify:

1. Euclidean invariance,
2. Euclidean symmetry,
3. reflection positivity,
4. cluster,
5. the full `E0` temperedness estimate in the Euclidean axioms sense.

Those are not the same theorem surface, and the docs should keep them separate.

## 5. Honest current route constraints

There is a false route still present elsewhere in `SchwingerAxioms.lean`:

1. `schwingerExtension_os_term_eq_wightman_term`
2. `schwingerExtension_os_inner_product_eq_wightman`
3. `schwingerExtension_os_inner_product_eq_wightman_positivity`

That chain is off-paper. It tries to prove reverse-direction positivity by
identifying the OS pairing with the Wightman pairing on the nose.

The current `wightman_to_os_full` theorem does **not** depend on that false
chain. The blueprint should therefore treat the present reverse route as:

1. BHW extension,
2. Wick restriction,
3. honest `IsWickRotationPair`,
4. later reuse of OS I Section 4.3 and 4.4 if a stronger reverse theorem
   surface is desired.

## 6. Exact theorem-slot inventory for a fuller Section 5 formalization

If the repo later wants a stronger theorem such as

```lean
theorem wightman_to_os_axioms_full :
    ∃ OS : OsterwalderSchraderAxioms d,
      OS.S = constructSchwingerFunctions Wfn := by
```

then the documentation-standard theorem slots should be frozen at the **actual
field level** rather than a bundled "Euclidean invariance / symmetry /
positivity / cluster" slogan:

```lean
lemma constructSchwinger_tempered
    (Wfn : WightmanFunctions d) :
    ∀ n, Continuous (constructSchwingerFunctions Wfn n) := by
  -- Proposition 5.1 / `constructedSchwinger_tempered_zeroDiagonal`

lemma constructSchwinger_linear
    (Wfn : WightmanFunctions d) :
    ∀ n, IsLinearMap ℂ (constructSchwingerFunctions Wfn n) := by
  -- already current production theorem

lemma constructSchwinger_reality
    (Wfn : WightmanFunctions d) :
    ∀ (n : ℕ) (f g : ZeroDiagonalSchwartz d n),
      (∀ x, g.1 x = starRingEnd ℂ (f.1 (timeReflectionN d x))) →
      starRingEnd ℂ ((constructSchwingerFunctions Wfn) n f) =
        (constructSchwingerFunctions Wfn) n g := by
  -- package `wickRotatedBoundaryPairing_reality`

lemma constructSchwinger_symmetric
    (Wfn : WightmanFunctions d) :
    ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (f g : ZeroDiagonalSchwartz d n),
      (∀ x, g.1 x = f.1 (fun i => x (σ i))) →
      (constructSchwingerFunctions Wfn) n f =
        (constructSchwingerFunctions Wfn) n g := by
  -- package `wickRotatedBoundaryPairing_symmetric`

lemma constructSchwinger_translation_invariant
    (Wfn : WightmanFunctions d) :
    ∀ (n : ℕ) (a : SpacetimeDim d) (f g : ZeroDiagonalSchwartz d n),
      (∀ x, g.1 x = f.1 (fun i => x i + a)) →
      (constructSchwingerFunctions Wfn) n f =
        (constructSchwingerFunctions Wfn) n g := by
  -- transport BHW translation covariance, then descend to Wick restriction

lemma constructSchwinger_rotation_invariant
    (Wfn : WightmanFunctions d) :
    ∀ (n : ℕ) (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      R.transpose * R = 1 → R.det = 1 →
      ∀ (f g : ZeroDiagonalSchwartz d n),
      (∀ x, g.1 x = f.1 (fun i => R.mulVec (x i))) →
      (constructSchwingerFunctions Wfn) n f =
        (constructSchwingerFunctions Wfn) n g := by
  -- transport Lorentz/Poincare covariance through the common BHW object

lemma constructSchwinger_positive
    (Wfn : WightmanFunctions d) :
    ∀ (F : BorchersSequence d),
      (∀ n, tsupport ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n) →
      (OSInnerProduct d (constructSchwingerFunctions Wfn) F F).re ≥ 0 := by
  -- reuse the Section 4.3 transport package, not the false OS=W chain

lemma constructSchwinger_cluster
    (Wfn : WightmanFunctions d) :
    ∀ (n m : ℕ) (f : ZeroDiagonalSchwartz d n) (g : ZeroDiagonalSchwartz d m),
      ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ (g_a : ZeroDiagonalSchwartz d m),
            (∀ x : NPointDomain d m, g_a.1 x = g.1 (fun i => x i - a)) →
            ∀ (fg_a : ZeroDiagonalSchwartz d (n + m)),
              (∀ x : NPointDomain d (n + m),
                fg_a.1 x = f.1 (splitFirst n m x) * g_a.1 (splitLast n m x)) →
              ‖(constructSchwingerFunctions Wfn) (n + m) fg_a -
                (constructSchwingerFunctions Wfn) n f *
                (constructSchwingerFunctions Wfn) m g‖ < ε := by
  -- reuse the Section 4.4 transport package in the literal field order
  -- `constructSchwinger_cluster_translate_adapter ->
  --  constructSchwinger_cluster_tensor_adapter -> constructSchwinger_cluster`
```

The key contract change is that later Lean work is no longer allowed to hide
split `E1` packaging inside a bundled `EuclideanInvariance` theorem or to defer
the exact zero-diagonal theorem surface until implementation time.
## 7. Exact proof decomposition for the current theorem

The later maintainer reading `wightman_to_os_full` should understand its proof
as:

1. define the Euclidean family by Wick restriction,
2. obtain continuity from the already-proved temperedness theorem,
3. obtain linearity from the already-proved linearity theorem,
4. obtain the analytic continuation witness from `W_analytic_BHW`,
5. obtain the boundary-value statement from
   `bhw_distributional_boundary_values`.

No positivity theorem, cluster theorem, or Euclidean symmetry theorem is used
in that current proof.

## 8. Where Proposition 5.1 fits

OS I Section 5 is technically centered on Proposition 5.1, the Schwartz bound
for the Wick-restricted pairing on off-diagonal compactly supported tests.

In the current production route:

1. the minimal theorem surface uses only the already-packaged continuity theorem
   `constructedSchwinger_tempered_zeroDiagonal`,
2. the detailed Proposition 5.1 decomposition is documented in
   `docs/os1_detailed_proof_audit.md`,
3. later strengthening from `IsWickRotationPair` to full Euclidean axioms
   should call that Proposition 5.1 package explicitly rather than re-proving
   continuity ad hoc.

So the reverse blueprint should treat Proposition 5.1 as the technical heart of
any future strengthening, even though the current minimal theorem does not
mention it explicitly.

## 9. Exact theorem-name dictionary for the reverse route

The current proof should visibly use:

1. `constructSchwingerFunctions`
2. `constructZeroDiagonalSchwingerFunctions`
3. `constructedSchwinger_tempered_zeroDiagonal`
4. `constructedZeroDiagonalSchwinger_linear`
5. `W_analytic_BHW`
6. `bhw_distributional_boundary_values`
7. `IsWickRotationPair`

The fuller Section 5 route should additionally reuse the Section 4 theorem
packages documented in `docs/os1_detailed_proof_audit.md`.

## 10. Do not do this

1. Do not claim the current theorem already packages the full OS axioms.
2. Do not use the false
   `schwingerExtension_os_inner_product_eq_wightman` route as if it were the
   reverse-direction positivity proof.
3. Do not detach the Euclidean family from the common holomorphic object.
4. Do not re-externalize a large hypothesis list for `wightman_to_os_full`;
   the current theorem surface on `main` is already smaller and cleaner than
   the older hypothesis-heavy drafts.

## 11. Minimal Lean pseudocode for the current theorem and the stronger future one

Current theorem:

```lean
theorem wightman_to_os_full (Wfn : WightmanFunctions d) :
    ∃ (S : SchwingerFunctions d),
      (∀ n, Continuous (S n)) ∧
      (∀ n, IsLinearMap ℂ (S n)) ∧
      IsWickRotationPair S Wfn.W := by
  refine ⟨constructZeroDiagonalSchwingerFunctions Wfn, ?_, ?_, ?_⟩
  · intro n
    simpa [constructZeroDiagonalSchwingerFunctions] using
      constructedSchwinger_tempered_zeroDiagonal Wfn n
  · intro n
    simpa [constructZeroDiagonalSchwingerFunctions] using
      constructedZeroDiagonalSchwinger_linear Wfn n
  · exact current_BHW_boundary_value_proof
```

Future stronger theorem surface:

```lean
theorem wightman_to_os_axioms_full (Wfn : WightmanFunctions d) :
    ∃ OS : OsterwalderSchraderAxioms d,
      OS.S = constructSchwingerFunctions Wfn := by
  -- Step A: build the Schwinger family by Wick restriction
  -- Step B: prove E0 via Proposition 5.1, including the explicit
  --         `E0_reality` packaging from
  --         `wickRotatedBoundaryPairing_reality`
  -- Step C: package `E3_symmetric` from
  --         `wickRotatedBoundaryPairing_symmetric`, then package the split
  --         `E1_translation_invariant` / `E1_rotation_invariant` fields from
  --         the checked BHW covariance seam
  --         `F_ext_translation_invariant ->
  --          wickRotatedBoundaryPairing_translation_invariant` and
  --         `F_ext_rotation_invariant ->
  --          wickRotatedBoundaryPairing_rotation_invariant`
  -- Step D: prove `E2_reflection_positive` / `E4_cluster` by reusing the
  --         reverse Section-4 transport/density packages
```

## 12. Exact status of the currently existing stronger reverse theorems

The later implementation should distinguish three categories of already-present
theorems in `SchwingerAxioms.lean`.

### 12.1. Directly reusable on the paper route

These are already on the right theorem shape and should be treated as genuine
inputs or model proofs for a future stronger reverse theorem.

1. `wickRotatedBoundaryPairing_symmetric`
2. `wickRotatedBoundaryPairing_reality`
3. `F_ext_permutation_invariant`
4. `bhw_euclidean_reality_ae`

These are all honest Euclidean-side statements about the BHW extension or the
Wick-restricted pairing. They do not identify the OS pairing with the
Wightman pairing on the nose.

### 12.2. Present in the file, but *not* documentation targets

These theorems exist, but their current proof route is off-paper or depends on
an earlier false theorem shape and therefore should not be copied into a future
faithful implementation plan.

1. `schwingerExtension_os_term_eq_wightman_term`
2. `schwingerExtension_os_inner_product_eq_wightman`
3. `schwingerExtension_os_inner_product_eq_wightman_positivity`
4. `wickRotatedBoundaryPairing_reflection_positive`

The future reverse-direction positivity proof should *not* cite those theorems.
It should instead be documented as a fresh transport of the OS I Section 4.3
positivity package to the constructed Schwinger family.

### 12.3. Present, but still incomplete because they sit on other open inputs

These theorems are useful as route indicators, but they are not yet a clean
implementation target because their current proofs depend on open blockers or
axioms elsewhere in the repo.

1. `bhw_pointwise_cluster_forwardTube`
2. `W_analytic_cluster_integral`
3. `wickRotatedBoundaryPairing_cluster`

So the `R -> E` blueprint should document cluster as a future Section 4.4
transport package, not as "already done modulo plumbing."

## 13. Exact source-checked OS-axiom slot inventory for a future stronger `R -> E` theorem

If the repo later strengthens `wightman_to_os_full` to a full
`OsterwalderSchraderAxioms` theorem, the documentation must follow the **actual
field surface in** `OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean`,
not a loose E0/E1/E2/E3/E4 slogan. The live source-checked field order is:

1. `E0_tempered`
2. `E0_linear`
3. `E0_reality`
4. `E1_translation_invariant`
5. `E1_rotation_invariant`
6. `E2_reflection_positive`
7. `E3_symmetric`
8. `E4_cluster`

So later reverse-direction docs and pseudocode must not swap `E2`/`E3`, and
must not omit the `E0_reality` slot.

### 13.1. E0 temperedness / continuity / linearity / reality

Current production already covers two of the three `E0` components directly:

1. `constructedSchwinger_tempered_zeroDiagonal`
2. `constructedZeroDiagonalSchwinger_linear`

A third source-checked Euclidean-side theorem already exists too:

3. `wickRotatedBoundaryPairing_reality`

So the future stronger theorem should document the `E0` package as a three-slot
repackaging layer rather than pretending that `E0` is only continuity plus
linearity.

The implementation-facing theorem slots should therefore be frozen as:

```lean
lemma constructSchwinger_tempered
    (Wfn : WightmanFunctions d) :
    ∀ n, Continuous (constructSchwingerFunctions Wfn n) := by
  simpa [constructSchwingerFunctions] using
    constructedSchwinger_tempered_zeroDiagonal Wfn

lemma constructSchwinger_linear
    (Wfn : WightmanFunctions d) :
    ∀ n, IsLinearMap ℂ (constructSchwingerFunctions Wfn n) := by
  simpa [constructSchwingerFunctions] using
    constructedZeroDiagonalSchwinger_linear Wfn

lemma constructSchwinger_reality
    (Wfn : WightmanFunctions d) :
    ∀ (n : ℕ) (f g : ZeroDiagonalSchwartz d n),
      (∀ x, g.1 x = starRingEnd ℂ (f.1 (timeReflectionN d x))) →
      starRingEnd ℂ ((constructSchwingerFunctions Wfn) n f) =
        (constructSchwingerFunctions Wfn) n g := by
  -- package `wickRotatedBoundaryPairing_reality`
```

The important ambiguity removed here is: the future reverse theorem is **not**
allowed to leave the `E0_reality` field implicit or to bury it under the later
positivity package.

### 13.2. E1 Euclidean invariance

In the live axiom surface, `E1` is split into two separate fields in
`SchwingerOS.lean`, not one bundled field:

1. `E1_translation_invariant`
2. `E1_rotation_invariant`

This is not yet isolated in production under final theorem names. The proof
package must therefore be documented as a literal four-slot implementation
queue rather than as two field wrappers alone:

```lean
lemma constructSchwinger_translation_covariant_BHW
    (Wfn : WightmanFunctions d) :
    -- BHW-side translation covariance on the common holomorphic object,
    -- using only the public route
    -- `Wightman/Groups/{Lorentz,Poincare}.lean -> Bridge/AxiomBridge.lean`

lemma constructSchwinger_translation_invariant
    (Wfn : WightmanFunctions d) :
    ∀ (n : ℕ) (a : SpacetimeDim d) (f g : ZeroDiagonalSchwartz d n),
      (∀ x, g.1 x = f.1 (fun i => x i + a)) →
      (constructSchwingerFunctions Wfn) n f =
        (constructSchwingerFunctions Wfn) n g := by
  -- unfold `constructSchwingerFunctions`, rewrite to the checked
  -- Wick-rotated boundary-pairing surface, consume only
  -- `constructSchwinger_translation_covariant_BHW`, then close definitionally

lemma constructSchwinger_rotation_covariant_BHW
    (Wfn : WightmanFunctions d) :
    -- BHW-side covariance specialized to the Euclidean rotation subgroup,
    -- transported only through the public route
    -- `Wightman/Groups/{Lorentz,Poincare}.lean -> Bridge/AxiomBridge.lean ->
    --  ForwardTubeLorentz.lean -> OSToWightmanBoundaryValues.lean`

lemma constructSchwinger_rotation_invariant
    (Wfn : WightmanFunctions d) :
    ∀ (n : ℕ) (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      R.transpose * R = 1 → R.det = 1 →
      ∀ (f g : ZeroDiagonalSchwartz d n),
      (∀ x, g.1 x = f.1 (fun i => R.mulVec (x i))) →
      (constructSchwingerFunctions Wfn) n f =
        (constructSchwingerFunctions Wfn) n g := by
  -- unfold `constructSchwingerFunctions`, rewrite to the checked
  -- Wick-rotated boundary-pairing surface, consume only
  -- `constructSchwinger_rotation_covariant_BHW`, then close definitionally
```

The important documentation point is now stronger than “transport covariance
through the common holomorphic object.” The reverse `E1` lane must run in the
exact order

`constructSchwinger_translation_covariant_BHW -> constructSchwinger_translation_invariant -> constructSchwinger_rotation_covariant_BHW -> constructSchwinger_rotation_invariant`,

with the anti-drift rule that only the two `*_covariant_BHW` slots may touch
public covariance transport and the two `*_invariant` slots may only package
Wick-restriction outputs into the exact `SchwingerOS.lean` field surfaces.

### 13.2.1. File ownership and proof-transcript order for the future stronger theorem

To make the later Lean pass mechanical rather than rediscovered, the reverse
route should freeze the ownership and consumption order of the future theorem
slots as follows.

1. `E0_tempered`
   - file owner: `Wightman/Reconstruction/WickRotation/SchwingerTemperedness.lean`
   - exported surface already present:
     `constructedSchwinger_tempered_zeroDiagonal`
   - packaging task: re-express that theorem on
     `constructSchwingerFunctions Wfn`
2. `E0_linear`
   - file owner: `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean`
   - exported surface already present:
     `constructedZeroDiagonalSchwinger_linear`
   - packaging task: re-express that theorem on
     `constructSchwingerFunctions Wfn`
3. `E0_reality`
   - file owner: `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean`
   - exported surface already present:
     `wickRotatedBoundaryPairing_reality`
   - packaging task: convert its current theorem surface into the exact
     `SchwingerOS.lean :: OsterwalderSchraderAxioms.E0_reality` witness format
4. `E3_symmetric`
   - file owner: `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean`
   - exported surface already present:
     `wickRotatedBoundaryPairing_symmetric`
   - packaging task: convert the existing permutation statement into the exact
     `E3_symmetric` field shape on `ZeroDiagonalSchwartz`
5. reverse `E1` four-slot package
   - expected owner: `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean`
   - theorem slots, in forced creation order:
     `constructSchwinger_translation_covariant_BHW ->
     constructSchwinger_translation_invariant ->
     constructSchwinger_rotation_covariant_BHW ->
     constructSchwinger_rotation_invariant`
   - supporting analytic input files and public route checkpoints:
     `BHWExtension.lean`, `BHWTranslation.lean`,
     `Wightman/Groups/{Lorentz,Poincare}.lean`,
     `Bridge/AxiomBridge.lean`, `ForwardTubeLorentz.lean`, and
     `OSToWightmanBoundaryValues.lean`
   - packaging task: first close the BHW-side translation transport slot,
     second package the translation field witness, third close the BHW-side
     rotation transport slot, and fourth package the rotation field witness;
     the field wrappers may not reopen bridge/covariance transport
6. `E2_reflection_positive`
   - expected owner: a future reverse-direction theorem package in
     `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean`
   - current source status in the live file:
     `wickRotatedBoundaryPairing_reflection_positive` is already present, but
     only as a **quarantined wrapper** because it still sits downstream of the
     false OS=`Wightman` pairing route through
     `schwingerExtension_os_inner_product_eq_wightman`
   - hard consumers it must target exactly:
     `SchwingerOS.lean :: OSInnerProduct` and
     `SchwingerOS.lean :: OsterwalderSchraderAxioms.E2_reflection_positive`
   - prohibited route: any reuse of
     `schwingerExtension_os_inner_product_eq_wightman`,
     `schwingerExtension_os_inner_product_eq_wightman_positivity`, or the
     current quarantined wrapper as if it were already honest infrastructure
7. `E4_cluster`
   - expected owner: a future reverse-direction packaging theorem layer
     targeting `Wightman/Reconstruction/SchwingerOS.lean`
   - source-checked checked-present suppliers / wrappers:
     `W_analytic_cluster_integral` then `wickRotatedBoundaryPairing_cluster`
   - still-missing zero-diagonal packaging theorem family:
     `constructSchwinger_cluster_translate_adapter ->
     constructSchwinger_cluster_tensor_adapter ->
     constructSchwinger_cluster`
   - hard consumer it must target exactly:
     `SchwingerOS.lean :: OsterwalderSchraderAxioms.E4_cluster`
   - required consumer ladder:
     `W_analytic_cluster_integral -> wickRotatedBoundaryPairing_cluster ->
     constructSchwinger_cluster_translate_adapter ->
     constructSchwinger_cluster_tensor_adapter -> constructSchwinger_cluster ->
     OsterwalderSchraderAxioms.E4_cluster`
   - exact field-shaped obligations that the adapter family must manufacture:
     `g_a : ZeroDiagonalSchwartz d m` with the translated pointwise formula,
     then `fg_a : ZeroDiagonalSchwartz d (n + m)` with the literal
     tensor-product pointwise formula from
     `SchwingerOS.lean:792-804`
   - prohibited route: vague citation of `W_analytic_cluster_integral`, direct
     reuse of `wickRotatedBoundaryPairing_cluster`, or a black-box invocation of
     `constructSchwinger_cluster` that leaves the witness-building order
     implicit

So the later strong theorem should be implemented in the literal order

`E0_tempered -> E0_linear -> E0_reality -> E3_symmetric -> constructSchwinger_translation_covariant_BHW -> constructSchwinger_translation_invariant -> constructSchwinger_rotation_covariant_BHW -> constructSchwinger_rotation_invariant -> E2 -> E4`,

with each later slot consuming the earlier packaged Euclidean surfaces rather
than rediscovering them from the raw BHW integral.

### 13.3. E2 reflection positivity

This is the main reverse-direction trap. The future theorem slot should be
documented as:

```lean
lemma constructSchwinger_positive
    (Wfn : WightmanFunctions d) :
    ∀ (F : BorchersSequence d),
      (∀ n, tsupport ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n) →
      (OSInnerProduct d (constructSchwingerFunctions Wfn) F F).re ≥ 0 := by
  -- do *not* use `schwingerExtension_os_inner_product_eq_wightman`
  -- reuse the OS I Section 4.3 transport package on the Wick-restricted family
```

The reverse blueprint should treat this as a transport theorem from the
already-understood OS-I positivity package, not as a fresh spectral/semigroup
construction and not as an algebraic identity of pairings.

This should also be documented explicitly as a reverse-direction transport:

1. start from Wightman data,
2. build the Wick-restricted Schwinger family,
3. identify the positive-time Wick-restricted core relevant to OS I Section 4.3,
4. reuse the Section-4.3 transport package on that constructed Euclidean
   family,
5. close by the Euclidean-side density / continuity argument.

So the later Lean proof should not cite the forward `E -> R` positivity theorem
as if it automatically runs backward. It should construct the reverse theorem
with the same Section-4.3 proof shape, now applied on the Euclidean family
produced from the Wightman input.

### 13.4. E3 symmetry

This one is already largely present on the correct theorem shape:

```lean
theorem wickRotatedBoundaryPairing_symmetric
```

So the future implementation step for `E3_symmetric` should mostly be a
packaging theorem that re-expresses the existing permutation-invariance result
in the exact axiom-field format.

### 13.5. E4 cluster

The future theorem slot should be documented as:

```lean
lemma constructSchwinger_cluster
    (Wfn : WightmanFunctions d) :
    ∀ (n m : ℕ) (f : ZeroDiagonalSchwartz d n) (g : ZeroDiagonalSchwartz d m),
      ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ (g_a : ZeroDiagonalSchwartz d m),
            (∀ x : NPointDomain d m, g_a.1 x = g.1 (fun i => x i - a)) →
            ∀ (fg_a : ZeroDiagonalSchwartz d (n + m)),
              (∀ x : NPointDomain d (n + m),
                fg_a.1 x = f.1 (splitFirst n m x) * g_a.1 (splitLast n m x)) →
              ‖(constructSchwingerFunctions Wfn) (n + m) fg_a -
                (constructSchwingerFunctions Wfn) n f *
                (constructSchwingerFunctions Wfn) m g‖ < ε := by
  -- reuse the OS I Section 4.4 transport package in the exact
  -- `SchwingerOS.lean :: E4_cluster` witness order
```

Again, the documentation should prefer the clean Section 4 transport route over
the currently half-open `W_analytic_cluster_integral` lane.

## 14. Exact implementation order for a future full reverse theorem

The later Lean implementation should proceed in this order.

1. Keep `wightman_to_os_full` as the minimal bridge theorem in
   `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`.
2. Repackage the already-proved continuity and linearity theorems as
   `E0_tempered` and `E0_linear`.
3. Repackage `wickRotatedBoundaryPairing_reality` as the missing `E0_reality`
   field.
4. Package `E3_symmetric` from `wickRotatedBoundaryPairing_symmetric`.
5. Package the split `E1` lane in the exact four-slot order
   `constructSchwinger_translation_covariant_BHW ->
   constructSchwinger_translation_invariant ->
   constructSchwinger_rotation_covariant_BHW ->
   constructSchwinger_rotation_invariant`, using the common BHW analytic
   object as the only endorsed transport surface and forbidding the final
   field wrappers from reopening public covariance transport.
6. Prove `E2_reflection_positive` by transporting the OS I Section-4.3
   positivity package.
7. Prove `E4_cluster` by transporting the OS I Section-4.4 cluster package.

This order matters because it keeps the route faithful to the currently proved
bridge, forces the reverse theorem to respect the actual `SchwingerOS.lean`
field inventory, and avoids rebuilding the reverse direction around the false
positivity chain or around an underspecified bundled `E1` theorem shape.

### 14.1. Explicit slot ledger for the split `E1` package

To make the later Lean pass mechanical, the reverse docs should now freeze the
split `E1` package at the same slot-ledger standard used elsewhere in the repo.
The route is no longer allowed to say only “transport BHW covariance.” It must
say exactly which checked public covariance surfaces are consumed and in what
order.

First keep the public covariance ownership split explicit:
1. group-definition owners:
   `OSReconstruction/Wightman/Groups/Lorentz.lean` and
   `OSReconstruction/Wightman/Groups/Poincare.lean`;
2. public representation bridge:
   `OSReconstruction/Bridge/AxiomBridge.lean`, with checked conversions
   `lorentzGroupToWightman` and `wightmanToLorentzGroup`;
3. public reverse consumers:
   `OSReconstruction/Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean`.

Under that checked-tree split, the reverse `E1` route is:

| Slot | Owner | Consumes | Exports | Next allowed consumer |
| --- | --- | --- | --- | --- |
| `constructSchwinger_translation_covariant_BHW` | `OSReconstruction/Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean` | checked-present `W_analytic_BHW` together with the existing public translation lane `F_ext_translation_invariant`; if a Lorentz/Poincaré representation change is needed on the way in, it must pass through `Bridge/AxiomBridge.lean`, not internal `ComplexLieGroups/*` aliases | BHW-side translation covariance statement on the common holomorphic object | `constructSchwinger_translation_invariant` only |
| `constructSchwinger_translation_invariant` | same file | only the previous BHW-side translation-covariance theorem together with the checked Wick-restriction consumer `wickRotatedBoundaryPairing_translation_invariant` and the definition of `constructSchwingerFunctions` | exact field-shaped witness for `SchwingerOS.lean :: OsterwalderSchraderAxioms.E1_translation_invariant` | `constructSchwinger_rotation_covariant_BHW`, final stronger wrapper, and later reverse-field consumers only through the packaged Euclidean family |
| `constructSchwinger_rotation_covariant_BHW` | same file | checked-present `W_analytic_BHW` plus the public Lorentz/Poincaré covariance lane routed through `Wightman/Groups/{Lorentz,Poincare}.lean -> Bridge/AxiomBridge.lean ->` the checked public consumers `ForwardTubeLorentz.lean :: lorentz_covariant_distributional_bv` and `OSToWightmanBoundaryValues.lean :: bvt_lorentz_covariant_restricted -> bvt_lorentz_covariant -> constructWightmanFunctions`; no fresh route through `ComplexLieGroups/LorentzLieGroup.lean :: RestrictedLorentzGroup` aliases is allowed | BHW-side covariance statement specialized to the Euclidean rotation subgroup on the Wick slice | `constructSchwinger_rotation_invariant` only |
| `constructSchwinger_rotation_invariant` | same file | only the previous BHW-side rotation-covariance theorem together with the checked Wick-restriction consumer `wickRotatedBoundaryPairing_rotation_invariant` and the definition of `constructSchwingerFunctions` | exact field-shaped witness for `SchwingerOS.lean :: OsterwalderSchraderAxioms.E1_rotation_invariant` | final stronger wrapper and downstream Euclidean-axiom consumers only |

The implementation consequence is strict:
- later Lean work may introduce small rewrite helpers under those four slots,
  but it may not collapse them back into one vague theorem called
  `constructSchwinger_euclidean_invariant`;
- the checked reverse `E1` lane must stay split literally as
  `F_ext_translation_invariant -> wickRotatedBoundaryPairing_translation_invariant`
  and
  `F_ext_rotation_invariant -> wickRotatedBoundaryPairing_rotation_invariant`;
- any covariance-type mismatch must first be classified as a public group
  definition issue, a public bridge issue, or a reverse consumer issue, rather
  than being patched ad hoc inside `SchwingerAxioms.lean`.## 15. Implementation-ready pseudocode for the stronger theorem surface

```lean
theorem wightman_to_os_axioms_full (Wfn : WightmanFunctions d) :
    ∃ OS : OsterwalderSchraderAxioms d,
      OS.S = constructSchwingerFunctions Wfn := by
  let S := constructSchwingerFunctions Wfn
  have hE0_tempered : ∀ n, Continuous (S n) := by
    intro n
    simpa [S, constructSchwingerFunctions] using
      constructedSchwinger_tempered_zeroDiagonal Wfn n
  have hE0_linear : ∀ n, IsLinearMap ℂ (S n) := by
    intro n
    simpa [S, constructSchwingerFunctions] using
      constructedZeroDiagonalSchwinger_linear Wfn n
  have hE0_reality :
      ∀ (n : ℕ) (f g : ZeroDiagonalSchwartz d n),
        (∀ x, g.1 x = starRingEnd ℂ (f.1 (timeReflectionN d x))) →
        starRingEnd ℂ (S n f) = S n g := by
    intro n f g hfg
    -- package `wickRotatedBoundaryPairing_reality` plus the given witness `hfg`
    exact constructSchwinger_reality (d := d) Wfn n f g hfg
  have hE3 :
      ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (f g : ZeroDiagonalSchwartz d n),
        (∀ x, g.1 x = f.1 (fun i => x (σ i))) →
        S n f = S n g := by
    intro n σ f g hfg
    simpa [S, constructSchwingerFunctions] using
      wickRotatedBoundaryPairing_symmetric Wfn n σ f.1 g.1 hfg
  have hE2 :
      ∀ (F : BorchersSequence d),
        (∀ n, tsupport ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
          OrderedPositiveTimeRegion d n) →
        (OSInnerProduct d S F F).re ≥ 0 := by
    exact constructSchwinger_positive (d := d) Wfn
  have hE4 := constructSchwinger_cluster (d := d) Wfn
  -- `E1_translation_invariant` / `E1_rotation_invariant` are separate later slots.
  exact ⟨{
    S := S
    E0_tempered := hE0_tempered
    E0_linear := hE0_linear
    E0_reality := hE0_reality
    E1_translation_invariant := constructSchwinger_translation_invariant (d := d) Wfn
    E1_rotation_invariant := constructSchwinger_rotation_invariant (d := d) Wfn
    E2_reflection_positive := hE2
    E3_symmetric := hE3
    E4_cluster := hE4
  }, rfl⟩
```

This pseudocode is intentionally explicit about the trusted and untrusted
pieces:

1. the `E0_tempered`, `E0_linear`, `E0_reality`, and `E3_symmetric` slots now
   point to honest current theorem surfaces or immediate repackaging targets;
2. the `E2_reflection_positive` and `E4_cluster` slots remain future targets
   that must reuse the Section 4 transport packages;
3. the old false OS=`Wightman` positivity chain does not appear anywhere in
   the target proof script;
4. the stronger theorem surface must target the actual structure fields
   `OS.S`, `OS.E0_tempered`, `OS.E0_linear`, `OS.E0_reality`,
   `OS.E1_translation_invariant`, `OS.E1_rotation_invariant`,
   `OS.E2_reflection_positive`, `OS.E3_symmetric`, and `OS.E4_cluster`.
   The derived projection `OS.schwinger` does exist in `SchwingerOS.lean`, but
   it is a wrapper definition rather than a structure field, so later docs
   should not blur "field inventory" with "derived accessor".

## 16. Concrete proof sketches and route classification for E0-E4

The reverse-direction blueprint should now be explicit about which packages are
already close to implementation and which ones remain theorem-level work.

### 16.1. E0 proof sketch

The E0 package should be a pure repackaging theorem.

1. take `S := constructSchwingerFunctions Wfn`,
2. for continuity use the already-proved
   `constructedSchwinger_tempered_zeroDiagonal`,
3. for linearity use
   `constructedZeroDiagonalSchwinger_linear`,
4. repackage these results under the `E0_*` axiom fields.

Estimated size: `20-40` Lean lines.

### 16.2. E1 proof sketch

E1 should be proved through the common holomorphic object, not by direct
integration on the Wick-restricted side.

The implementation transcript should now be read as a literal four-slot queue,
not as one bundled “Euclidean invariance” theorem:

| Order | Planned theorem slot | Owner | Consumes exactly | Exports exactly | Lean proof transcript |
| --- | --- | --- | --- | --- | --- |
| 1 | `constructSchwinger_translation_covariant_BHW` | `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean` | checked `W_analytic_BHW`, checked `F_ext_translation_invariant`, and only public group-representation rewrites routed through `Wightman/Groups/{Lorentz,Poincare}.lean -> Bridge/AxiomBridge.lean` when needed | a BHW-side translation-covariance statement written on the common holomorphic object, before Wick restriction | first normalize the acting group/representation on the public Wightman side; second rewrite that action through the checked bridge conversions only; third apply `F_ext_translation_invariant`; fourth restate the result on the `W_analytic_BHW` surface in the exact argument order later Wick-restriction consumers expect |
| 2 | `constructSchwinger_translation_invariant` | same file | only `constructSchwinger_translation_covariant_BHW`, checked `wickRotatedBoundaryPairing_translation_invariant`, and the definition of `constructSchwingerFunctions` | the exact field witness for `SchwingerOS.lean :: OsterwalderSchraderAxioms.E1_translation_invariant` | first unfold `constructSchwingerFunctions`; second rewrite the target field surface into the Wick-rotated boundary-pairing statement; third feed the BHW-side translation slot from row 1 into `wickRotatedBoundaryPairing_translation_invariant`; fourth close with definitional rewriting only |
| 3 | `constructSchwinger_rotation_covariant_BHW` | same file | checked `W_analytic_BHW`, the checked public Lorentz/Poincaré lane `Wightman/Groups/{Lorentz,Poincare}.lean -> Bridge/AxiomBridge.lean -> ForwardTubeLorentz.lean :: lorentz_covariant_distributional_bv -> OSToWightmanBoundaryValues.lean :: bvt_lorentz_covariant_restricted -> bvt_lorentz_covariant -> constructWightmanFunctions`, and checked `F_ext_rotation_invariant`; no internal `ComplexLieGroups/LorentzLieGroup.lean :: RestrictedLorentzGroup` route is allowed | a BHW-side covariance statement specialized to the Euclidean rotation subgroup on the Wick slice | first choose the Euclidean rotation input and rewrite it into the public connected Lorentz/Poincaré representation language; second transport that action along the checked public queue above until it matches the BHW-side boundary-value surface; third apply `F_ext_rotation_invariant`; fourth package the result so the next slot sees only the Wick-slice rotation statement, not the upstream bridge machinery |
| 4 | `constructSchwinger_rotation_invariant` | same file | only `constructSchwinger_rotation_covariant_BHW`, checked `wickRotatedBoundaryPairing_rotation_invariant`, and the definition of `constructSchwingerFunctions` | the exact field witness for `SchwingerOS.lean :: OsterwalderSchraderAxioms.E1_rotation_invariant` | first unfold `constructSchwingerFunctions`; second rewrite the field target into the Wick-rotated boundary-pairing surface; third feed the BHW-side rotation slot from row 3 into `wickRotatedBoundaryPairing_rotation_invariant`; fourth finish by definitional closure without reopening any public covariance bridge step |

Anti-drift contract for later Lean work:

1. rows 1 and 3 are the **only** slots allowed to mention public group owners
   or `Bridge/AxiomBridge.lean`;
2. rows 2 and 4 are pure Wick-restriction / field-packaging slots and may not
   introduce any new covariance transport theorem;
3. the checked split consumers must remain literally
   `F_ext_translation_invariant -> wickRotatedBoundaryPairing_translation_invariant`
   and
   `F_ext_rotation_invariant -> wickRotatedBoundaryPairing_rotation_invariant`;
4. if a proof attempt needs `ComplexLieGroups/*`, that must be documented as a
   new blocker or route mistake, not silently used inside the E1 queue.

Estimated size: `80-160` Lean lines, most of which are rewriting and group-
action bookkeeping.

### 16.3. E2 proof sketch

`E2_reflection_positive` must *not* go through the false OS=`Wightman`
positivity chain.

The honest route is:

1. identify the Wick-restricted family as the Euclidean image of the OS I
   Section 4.3 transport object,
2. prove the diagonal OS form equals the Hilbert norm square on the initial
   positive-time core,
3. extend by density / continuity to the full ordered positive-time Euclidean
   Borchers-sequence domain required by `E2_reflection_positive`,
4. conclude reflection positivity.

Estimated size: `120-220` Lean lines after the OS I Section 4.3 transport
package is implemented under exact theorem names.

### 16.4. E3 proof sketch

`E3_symmetric` is now an honest packaging theorem around the already-correct
symmetry surface.

1. use `wickRotatedBoundaryPairing_symmetric`,
2. rewrite it into the exact axiom-field format used by the OS structure,
3. discharge any zero-diagonal adapters explicitly.

Estimated size: `20-50` Lean lines.

### 16.5. E4 proof sketch

E4 should reuse the OS I Section 4.4 cluster transport package.

1. prove the Wick-restricted cluster pairing equals the transported
   Minkowski-side cluster form on the initial core,
2. feed that into the already-proved cluster theorem on the Minkowski side,
3. package the result as Euclidean cluster.

Estimated size: `120-220` Lean lines, again assuming the Section 4 transport
package exists under exact names.

## 17. Classification of current reverse-direction theorem surfaces

The current reverse-direction file should distinguish three statuses:

1. `KEEP`: correct theorem surface that should remain in production.
2. `QUARANTINE`: theorem surface may be mathematically meaningful, but the
   current proof depends on a false or off-paper route and should not be used
   as trusted infrastructure.
3. `DELETE`: theorem surface itself encodes the false route and should not be
   used going forward.

### 17.1. DELETE from the active route

These theorem surfaces encode the false "OS pairing = Wightman pairing"
positivity route and should not appear in later reverse-direction proofs.

1. `schwingerExtension_os_term_eq_wightman_term`
2. `schwingerExtension_os_inner_product_eq_wightman`
3. `schwingerExtension_os_inner_product_eq_wightman_positivity`

If the repo keeps them temporarily for historical reasons, the docs should
still classify them as deleted from the active route.

### 17.2. QUARANTINE until re-proved on the honest route

These theorems are not themselves the false route, but they currently sit
downstream of it and should not be consumed as trusted infrastructure until the
proofs are rerouted.

1. `wickRotatedBoundaryPairing_reflection_positive`

The right long-term fate is to re-prove this theorem from the Section 4.3
transport package and then move it back into the `KEEP` class.

### 17.3. KEEP as honest current surfaces

These are on the right theorem shape and should remain the documentation
targets.

1. `constructSchwingerFunctions`
2. `constructedSchwinger_tempered_zeroDiagonal`
3. `constructedZeroDiagonalSchwinger_linear`
4. `wickRotatedBoundaryPairing_reality`
5. `wickRotatedBoundaryPairing_symmetric`
6. `bhw_euclidean_reality_ae`
7. `bhw_pointwise_cluster_forwardTube`
8. `wightman_to_os_full`

The live `SchwingerAxioms.lean` front should therefore be described with more
precision than a generic “positivity / reality / cluster” slogan:
- actual remaining `sorry` slots there are only
  `schwingerExtension_os_term_eq_wightman_term` and
  `W_analytic_cluster_integral`;
- `bhw_euclidean_reality_ae` is an already-checked analytic supplier, not a
  remaining hole;
- `wickRotatedBoundaryPairing_reflection_positive` exists but stays in the
  `QUARANTINE` bucket until rerouted through the honest Section-4.3 transport
  package.

## 18. Estimated Lean line counts for a future full reverse theorem

The reverse blueprint is now detailed enough for rough sizing.

1. E0 packaging (including the now-explicit `E0_reality` slot):
   `40-80` lines.
2. E1 transport package:
   `80-160` lines.
3. E2 honest positivity transport:
   `120-220` lines.
4. E3 symmetry packaging:
   `20-50` lines.
5. E4 honest cluster transport:
   `120-220` lines.
6. final `wightman_to_os_axioms_full` wrapper:
   `20-40` lines.

So the honest route to a full reverse-direction axiom theorem should be thought
of as an approximately `400-770` line package, with almost all of the real
work in the `E2`/`E4` transport theorems rather than in the final wrapper.

## 19. Exact dependency chain for E0/E1/E2/E3/E4

The reverse-direction doc should now write the theorem dependencies in a way
that prevents accidental reuse of the false positivity route and keeps the
source-checked `SchwingerOS.lean` field order visible.

### 19.1. E1 dependency chain

The later implementation should proceed through these theorem slots:

```lean
lemma constructSchwinger_translation_covariant_BHW
lemma constructSchwinger_translation_invariant
lemma constructSchwinger_rotation_covariant_BHW
lemma constructSchwinger_rotation_invariant
```

with the proof transcript frozen as:

1. transport Wightman translation covariance through the checked common BHW
   object,
2. descend that covariance to the exact
   `SchwingerOS.lean :: OsterwalderSchraderAxioms.E1_translation_invariant`
   field witness on `constructSchwingerFunctions Wfn`,
3. transport Lorentz/Poincaré covariance through the same BHW object but now
   specialized to the Euclidean rotation subgroup on the Wick slice,
4. descend that to the exact
   `SchwingerOS.lean :: OsterwalderSchraderAxioms.E1_rotation_invariant`
   field witness.

The key documentation constraint is that the action should always be pushed
through the common holomorphic object first, and only then restricted to the
Wick-rotated Euclidean slice. Later docs are **not** allowed to collapse this
back into a bundled theorem such as `constructSchwinger_euclidean_invariant`.

### 19.2. E2 dependency chain

The later positivity proof should be forced through the following package:

```lean
lemma wickRotatedBoundaryPairing_on_positive_core
lemma wickRotatedBoundaryPairing_eq_transport_inner_on_core
lemma wickRotatedBoundaryPairing_nonneg_on_core
lemma wickRotatedBoundaryPairing_nonneg_by_density
theorem constructSchwinger_positive
```

The docs should continue to ban any route that tries to prove `E2` by asserting
a direct equality of the OS form with the Wightman form.

### 19.2.1. Exact proof transcript for the E2 transport package

The later Lean proof should make the transport mechanism literal:

1. define the positive-time Euclidean core generated by Wick-restrictions of
   ordered positive-time Minkowski test data,
2. prove the Wick-restricted pairing on that core agrees with the OS-I
   Section 4.3 transport inner product,
3. deduce nonnegativity on the core from the already-packaged Section 4.3
   positivity theorem,
4. prove the core is dense in the relevant Euclidean positive-time subspace,
5. extend the nonnegativity statement from the core to the closure,
6. repackage the resulting quadratic-form nonnegativity as reflection
   positivity.

So the theorem slots should be read as:

```lean
def wickRotated_positiveTimeCore
lemma wickRotatedBoundaryPairing_eq_transport_inner_on_core
lemma wickRotatedBoundaryPairing_nonneg_on_core
lemma wickRotated_positiveTimeCore_dense
lemma wickRotatedBoundaryPairing_nonneg_by_density
theorem constructSchwinger_positive
```

This is the point where the docs must remain strict: the proof is a transport
and density theorem, not a direct comparison of Euclidean and Minkowski
pairings.

### 19.3. E3 dependency chain

The later symmetry proof should be split as:

```lean
lemma constructSchwinger_symmetry_on_Schwartz
lemma constructSchwinger_symmetry_on_zeroDiagonal
theorem constructSchwinger_symmetric
```

In practice this is expected to collapse almost immediately to
`wickRotatedBoundaryPairing_symmetric`, but the docs should still keep the
packaging seam explicit: the production theorem is on `SchwartzNPoint`, while
`OsterwalderSchraderAxioms.E3_symmetric` is stated on `ZeroDiagonalSchwartz`.

### 19.4. E4 dependency chain

The later cluster proof is no longer allowed to hide behind a generic
"transport on a core, then density" slogan. The checked-present reverse file
already exposes one literal wrapper surface,
`SchwingerAxioms.lean :: wickRotatedBoundaryPairing_cluster`, and the docs now
freeze the implementation-facing consumer ladder around that fact:

```lean
lemma W_analytic_cluster_integral
lemma wickRotatedBoundaryPairing_cluster
theorem constructSchwinger_cluster
```

with the final consumer target fixed as
`SchwingerOS.lean :: OsterwalderSchraderAxioms.E4_cluster`.

More explicitly, the reverse cluster lane must now be read in the same
checked/planned split used elsewhere in the repo:

1. `W_analytic_cluster_integral`
   - file owner:
     `OSReconstruction/Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean`
   - status: checked-present live supplier theorem on the common-BHW /
     full-`SchwartzNPoint` side
   - exports: the common-BHW/full-Schwartz cluster estimate
   - next allowed consumer: `wickRotatedBoundaryPairing_cluster` only
2. `wickRotatedBoundaryPairing_cluster`
   - file owner:
     `.../SchwingerAxioms.lean`
   - status: checked-present wrapper theorem
   - consumes: `W_analytic_cluster_integral`
   - exports: the Wick-restricted full-`SchwartzNPoint` cluster wrapper
   - next allowed consumer: `constructSchwinger_cluster` only
3. `constructSchwinger_cluster`
   - file owner: future packaging theorem on the reverse `R -> E` lane,
     documented against
     `OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean`
   - status: still-missing planned zero-diagonal packaging theorem
   - consumes: `wickRotatedBoundaryPairing_cluster` plus an explicit
     zero-diagonal adapter package matching the *actual* field surface of
     `SchwingerOS.lean :: OsterwalderSchraderAxioms.E4_cluster`
   - required local theorem slots before the final packaging step:
     1. `constructSchwinger_cluster_translate_adapter`
        - theorem surface: for `g : ZeroDiagonalSchwartz d m` and spatial `a`,
          build / identify the translated witness `g_a : ZeroDiagonalSchwartz d m`
          with pointwise equation `g_a.1 x = g.1 (fun i => x i - a)`
        - role: converts the checked full-`SchwartzNPoint` translation input of
          `wickRotatedBoundaryPairing_cluster` into the exact zero-diagonal
          quantifier expected by `E4_cluster`
     2. `constructSchwinger_cluster_tensor_adapter`
        - theorem surface: for `f : ZeroDiagonalSchwartz d n` and translated
          `g_a`, build / identify `fg_a : ZeroDiagonalSchwartz d (n + m)` with
          pointwise equation
          `fg_a.1 x = f.1 (splitFirst n m x) * g_a.1 (splitLast n m x)`
        - role: supplies the exact `(n+m)`-point test object quantified by the
          field `E4_cluster`; later Lean work is no longer allowed to hide this
          under a vague "tensor product restriction" slogan
     3. `constructSchwinger_cluster`
        - theorem surface: consume `wickRotatedBoundaryPairing_cluster` together
          with the two adapter witnesses above and discharge the exact norm
          inequality appearing in `SchwingerOS.lean : E4_cluster`
   - exports: the exact field witness consumed by
     `OsterwalderSchraderAxioms.E4_cluster`

So the implementation-facing theorem order is frozen as

```lean
W_analytic_cluster_integral
  -> wickRotatedBoundaryPairing_cluster
  -> constructSchwinger_cluster_translate_adapter
  -> constructSchwinger_cluster_tensor_adapter
  -> constructSchwinger_cluster
  -> OsterwalderSchraderAxioms.E4_cluster
```

The adapter pair is not optional bookkeeping: it is the exact local proof
transcript forced by `SchwingerOS.lean:792-804`, where the final field first
quantifies the translated witness `g_a` and then the tensor witness `fg_a`
before the norm inequality is even stated. Later Lean work must therefore not
replace this lane with a generic pseudo-family such as
`wickRotatedBoundaryPairing_cluster_transport_on_core` /
`..._by_density` unless those names are first introduced and justified as real
intermediate theorem surfaces.

### 19.4.1. Exact proof transcript for the E4 packaging route

The later Lean proof should proceed as:

1. prove or repair `W_analytic_cluster_integral` on the honest common-BHW /
   full-`SchwartzNPoint` side,
2. package that supplier as the checked Wick-restricted wrapper
   `wickRotatedBoundaryPairing_cluster` in `SchwingerAxioms.lean`,
3. add the still-missing zero-diagonal adapter package above that checked
   wrapper, in the literal order
   `constructSchwinger_cluster_translate_adapter -> constructSchwinger_cluster_tensor_adapter -> constructSchwinger_cluster`,
   so the proof explicitly manufactures the quantified witnesses `g_a` and
   `fg_a` required by `SchwingerOS.lean :: OsterwalderSchraderAxioms.E4_cluster`
   rather than silently coercing a full-`SchwartzNPoint` tensor product,
4. assign that packaged witness to the exact structure field
   `SchwingerOS.lean :: OsterwalderSchraderAxioms.E4_cluster`.

The critical ambiguity removed here is ownership: the reverse docs are no
longer allowed to suggest that the implementation target is an unspecified
core/density package living somewhere between `SchwingerAxioms.lean` and
`SchwingerOS.lean`. The checked wrapper already lives in
`SchwingerAxioms.lean`; the missing work above it is the explicit
zero-diagonal packaging theorem `constructSchwinger_cluster`.

### 19.4. Implementation consequence

If a later reverse-direction Lean proof tries to jump directly from:

1. `constructSchwingerFunctions`,
2. `wickRotatedBoundaryPairing_reality`,
3. `wickRotatedBoundaryPairing_symmetric`,
4. `bhw_euclidean_reality_ae`,

to the full `E2_reflection_positive` or `E4_cluster` axiom fields without the
intermediate transport theorems above, the docs should be updated first. The
current note should no longer permit hidden large steps in the reverse
direction.
