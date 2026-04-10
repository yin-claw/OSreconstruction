# Theorem 4 Cluster Blueprint

Purpose: this note is the theorem-specific implementation blueprint for the
live `E -> R` cluster frontier

- `OSToWightmanBoundaryValues.lean`, private theorem
  `bvt_F_clusterCanonicalEventually_translate`.

It is not a paper summary. It is the implementation ledger for the current
production route on `main`.

This note should be read together with:
- `docs/os1_detailed_proof_audit.md`, Section 8,
- `docs/theorem3_os_route_blueprint.md`,
- `docs/os2_detailed_proof_audit.md` only for the already-used k=2
  continuation background.

### 0.1. Checked production file inventory for theorem 4

This blueprint now records the exact repo-relative file inventory that the
cluster route was checked against, so the implementation loci for the core,
adapter, and final wrapper are not left implicit.

Checked-present theorem-4 production files:

- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean`
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesComparison.lean`
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean`
- `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean`
- `OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean`

Source-check note against the live repo tree (2026-04-08):

- `OSToWightmanBoundaryValuesBase.lean` really does contain the checked base
  reduction chain
  `bvt_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero`
  -> `..._schwinger`
  -> `bvt_eq_schwinger_of_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero`
  -> `schwinger_cluster_osConjTensorProduct_translate_spatial_right_local`
  -> `osInner_single_translate_spatial_right_cluster_local`
  -> `bvt_F_clusterCanonicalEventually_translate_of_singleSplitLargeSpatial`
  -> `bvt_F_clusterCanonicalEventually_translate_of_singleSplitSchwingerLargeSpatial`
  -> legacy
     `bvt_F_clusterCanonicalEventually_translate_of_singleSplitFactorComparison`.
- `OSToWightmanBoundaryValues.lean` really does contain only the final
  theorem-4-facing consumer shell:
  `bv_cluster_transfer_of_canonical_eventually`, private
  `bvt_F_clusterCanonicalEventually_translate`, private
  `bvt_F_clusterCanonicalEventually`, and private `bvt_W_cluster`.
- `OSToWightmanPositivity.lean` is present and is still the designated theorem-3
  consumer/supplier file for theorem 4, but a direct source check shows that it
  does **not yet** contain any of the planned theorem-4 extraction names
  `normalizedZeroDegreeRightVector`,
  `zeroDegree_right_single_wightman_extracts_factor`,
  `cluster_left_factor_transport`, or `cluster_right_factor_transport`.
  So those names below are implementation-contract targets for that file, not
  checked-present helpers.
- `OSToWightmanBoundaryValueLimits.lean` is checked-present but remains a
  theorem-2/theorem-3 support file; no theorem-4 adapter theorem names live
  there in the current tree.

Implementation rule for this blueprint:

1. the positive-time single-split cluster core and the legacy large-spatial
   reductions live in `.../OSToWightmanBoundaryValuesBase.lean`;
2. the corrected theorem-3 transport inputs that theorem 4 consumes live in
   `.../OSToWightmanPositivity.lean`;
3. the public transfer theorem `bv_cluster_transfer_of_canonical_eventually`
   and the final private wrapper
   `bvt_F_clusterCanonicalEventually_translate` live in
   `.../OSToWightmanBoundaryValues.lean`;
4. the immediate theorem-2 locality consumer
   `bv_local_commutativity_transfer_of_swap_pairing` already sits in
   `.../OSToWightmanBoundaryValuesComparison.lean`, so theorem-4 work should
   not treat `BoundaryValues.lean` as the only consumer surface around the
   boundary-value transfer layer;
5. the checked `.../OSToWightmanBoundaryValueLimits.lean` file is currently a
   theorem-2/theorem-3 support file, not a theorem-4 home. The theorem-4 docs
   may consume its already-proved `xiShift`/limit machinery, but later Lean
   work should not quietly drift the cluster adapter into that file unless this
   blueprint and the global plans are rewritten first;
6. if a future refactor moves any of these files, this blueprint must be
   updated in the same pass.

### 0.2. Fixed file ownership for the still-missing theorem-4 package

The checked-present inventory above is not enough by itself, because the main
remaining theorem-4 ambiguity was **which missing theorem package belongs in
which file**. That ownership is now fixed as part of the implementation
contract.

Checked-present consumer/support surfaces:

- `OSToWightmanPositivity.lean` is the checked file that should own the
  theorem-3-derived bookkeeping consumed by theorem 4, but the theorem-4-facing
  extraction package there is still missing under separate names.
- `OSToWightmanBoundaryValuesBase.lean` already owns the positive-time
  single-split cluster reductions
  (`...singleSplitLargeSpatial`, `...singleSplitSchwingerLargeSpatial`, legacy
  `...singleSplitFactorComparison`).
- `OSToWightmanBoundaryValues.lean` already owns the final wrapper
  `bvt_F_clusterCanonicalEventually_translate`, its translated wrapper, and the
  downstream public transfer theorem.

Checked-missing theorem-package ownership:

1. `OSToWightmanPositivity.lean` should export the theorem-3-derived one-factor
   transport inputs that theorem 4 consumes:
   `cluster_left_factor_transport` and
   `cluster_right_factor_transport`.
   Current checked-tree status: these theorem names are **planned only**; they
   are not yet present in the file, so later Lean work must add them there
   explicitly rather than assuming they already exist behind the theorem-3
   narrative.
2. `OSToWightmanBoundaryValuesBase.lean` should own the repaired core-side
   replacement theorem
   `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`
   together with the thin positive-time wrapper
   `bvt_cluster_positiveTime_singleSplit_core`. This is the same mathematical
   layer as the already-present `singleSplitLargeSpatial` /
   `singleSplitSchwingerLargeSpatial` reductions, so it belongs in the base
   file rather than in the final wrapper file.
3. `OSToWightmanBoundaryValues.lean` should own the public canonical-shell
   adapter package
   `canonical_cluster_integrand_eq_singleSplit_integrand`
   -> `canonical_translate_factor_eq_singleSplit_translate_factor`
   -> `singleSplit_core_rewrites_to_canonical_shell`
   -> `canonical_shell_limit_of_rewrite`
   -> `bvt_cluster_canonical_from_positiveTime_core`,
   and then consume that package in the final private theorem
   `bvt_F_clusterCanonicalEventually_translate`.
   The file-local seam is now frozen more sharply than “wrapper-file support”:
   `canonical_cluster_integrand_eq_singleSplit_integrand` is the **first**
   theorem-4 slot allowed to live in `OSToWightmanBoundaryValues.lean`, while
   the already-checked public transfer theorem
   `bv_cluster_transfer_of_canonical_eventually` is a **downstream consumer** of
   the final private wrapper chain, not an admissible input to the 5-slot
   adapter queue.

   So those adapter theorems are allowed to consume only the checked generic
   supplier surfaces that genuinely sit upstream of that queue, namely:
   - from `OSToWightmanBoundaryValuesComparison.lean`:
     `canonicalForwardConeDirection` and
     `canonicalForwardConeDirection_mem` only;
   - from `OSToWightmanBoundaryValueLimits.lean`:
     the theorem-3 scalar-holomorphic package
     `bvt_singleSplit_xiShiftHolomorphicValue`,
     `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue`,
     `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`,
     `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift`,
     `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger`,
     `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`, and
     `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq`.
   But the theorem-4 adapter may consume that list only in the now-frozen split:
   `canonical_shell_limit_of_rewrite` alone may import the
   `BoundaryValueLimits.lean` package, and the direct consumer surfaces are now
   source-checked against exact anchors in
   `OSToWightmanBoundaryValueLimits.lean`:
   `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue` (line 273),
   `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq` (line 290),
   `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`
   (line 446), and `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq`
   (line 536). Inside that theorem the internal proof order is fixed as
   `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`
   -> optional right-half-plane uniqueness only via
   `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue` +
   `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq`
   -> final Wightman-target `t -> 0+` transport only via
   `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`.
   The object `bvt_singleSplit_xiShiftHolomorphicValue` itself (line 260) is
   only the underlying scalar holomorphic function these direct consumers talk
   about; it is not a separate theorem-4 adapter step. The Schwinger-target
   theorems `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift`
   (line 314) and
   `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger`
   (line 350) stay supplier-only lower legs on this lane, and the lower helper
   `eqOn_rightHalfPlane_of_ofReal_eq` (line 494) remains quarantined beneath
   `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq` rather than a direct
   theorem-4 input. The theorem-4 adapter must not pretend that
   `BoundaryValueLimits.lean` already contains any theorem-4-specific cluster
   wrapper under separate names, and it must not use the deprecated
   bridge `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_schwinger_eq_bvt_W_conjTensorProduct_timeShift`.
4. `SchwingerOS.lean` remains only the source of the already-checked OS-side
   positive-time/Hilbert-space algebra. It is not the place to hide theorem-4
   wrapper glue.

This ownership split is strict: later Lean work should not leave the theorem-4
bridge theorem, the public canonical-shell adapter, and the final wrapper
intermixed in one long `BoundaryValues.lean` proof block.

## 1. The live theorem and its consumers

The live frontier theorem is:

```lean
private theorem bvt_F_clusterCanonicalEventually_translate
```

in `OSToWightmanBoundaryValues.lean`.

Its immediate consumers are:

1. `bvt_F_clusterCanonicalEventually`
   in `OSToWightmanBoundaryValues.lean`,
2. `bvt_W_cluster`
   in the same file,
3. the public transfer theorem
   `bv_cluster_transfer_of_canonical_eventually`,
4. the exported Wightman axiom
   `HasClusterProperty` through `bvt_W_cluster`.

So theorem 4 is not a leaf theorem. It is the unique live bridge from the
Euclidean/OS cluster package to the public reconstructed Wightman cluster
axiom.

## 2. OS-paper reading of theorem 4

OS I Section 4.4 proves cluster by the same three-layer pattern already used in
Section 4.3:

1. Euclidean cluster on ordered positive-time test data,
2. reinterpretation as an OS Hilbert-space matrix-element statement,
3. transport of that matrix-element statement back to the reconstructed
   Wightman pairing after the positivity/isometry bridge is already available.

So theorem 4 is downstream of theorem 3 in the strict OS route.

This has two immediate implementation consequences.

1. Theorem 4 must consume the theorem-3 one-factor comparison statements.
   It must not try to replace theorem 3.
2. The honest new mathematics in theorem 4 is the Euclidean large-spatial
   factorization and its transport through the already-built boundary-value
   comparison layer. It is not a new continuation problem.

### 2.1. OS I error / OS II correction note

Theorem 4 sits downstream of the same OS I / OS II distinction that governs
theorem 3.

1. OS I Section 4.4 gives the correct **cluster theorem shape**:
   Euclidean cluster -> OS Hilbert-space matrix element -> reconstructed
   Wightman cluster statement.
2. But in the original OS I paper, the reconstructed Wightman-side kernel used
   in the Section-4 transport package is tied back to the flawed Lemma-8.8
   continuation route.
3. Therefore the current production reading must be:
   - use OS I for the cluster transport architecture,
   - use the OS II-repaired continuation / boundary-value object on the
     Wightman side,
   - and never treat theorem 4 as an independent many-variable continuation
     theorem.

So the theorem-4 route is safe only as a **consumer** of the repaired theorem-3
transport package. Any proof attempt that reopens many-variable continuation
inside theorem 4 is off-route.

## 3. Exact production theorem hooks already available

The current codebase already contains almost all of the genuine cluster
mathematics.

In `OSToWightmanBoundaryValuesBase.lean`:

1. `schwinger_cluster_osConjTensorProduct_translate_spatial_right_local`
   is the exact Euclidean cluster theorem on the translated single-split shell.
2. `osInner_single_translate_spatial_right_cluster_local`
   rewrites that Schwinger theorem as an OS Hilbert-space matrix-element
   factorization.
3. `bvt_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero`
   gives the small-`t` continuity leg on the boundary-value side.
4. `bvt_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero_schwinger`
   gives the same limit with the Schwinger target already identified.
5. `bvt_eq_schwinger_of_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero`
   upgrades the BV-side `xiShift` limit to the translated single-split
   Euclidean identity.
6. `bvt_eq_schwinger_of_tendsto_singleSplit_xiShift_nhdsWithin_zero`
   is the zero-translation specialization.
7. `bvt_F_clusterCanonicalEventually_translate_of_singleSplitLargeSpatial`
   says large-spatial factorization of the translated OS Hilbert matrix element
   is enough for the translated BV cluster shell.
8. `bvt_F_clusterCanonicalEventually_translate_of_singleSplitSchwingerLargeSpatial`
   removes the explicit Hilbert-space matrix element from that theorem.
9. `bvt_F_clusterCanonicalEventually_translate_of_singleSplitFactorComparison`
   says that once the two one-factor comparisons are known, theorem 4 follows
   on the exact positive-time single-split shell.

In `OSToWightmanBoundaryValues.lean`:

1. `bv_cluster_transfer_of_canonical_eventually`
   is already the public boundary-value-to-Wightman transfer theorem.
2. `bvt_F_clusterCanonicalEventually`
   is just the translated-`g_a` wrapper.
3. `bvt_W_cluster`
   is just `bv_cluster_transfer_of_canonical_eventually` instantiated with
   `bvt_W` and `bvt_F`.

So the current production picture is:

1. the Euclidean cluster theorem exists,
2. the Hilbert-space rewrite exists,
3. the single-split BV shell theorem exists modulo two one-factor comparison
   hypotheses,
4. the public transfer theorem exists,
5. the only live frontier is the missing production connection between those
   pieces.

## 4. Honest remaining gap

The exact already-proved support theorem

```lean
bvt_F_clusterCanonicalEventually_translate_of_singleSplitFactorComparison
```

is now legacy infrastructure only. It still asks for two hypotheses:

```lean
hleft  : bvt_W OS lgc n f = OS.S n (ZeroDiagonalSchwartz.ofClassical (f.osConj))
hright : bvt_W OS lgc m g = OS.S m (ZeroDiagonalSchwartz.ofClassical g)
```

with the usual ordered-positive-time and compact-support assumptions on `f` and
`g`.

These hypotheses are now known to be the wrong theorem surface. They are the
same false same-shell comparison pattern already quarantined in theorem 3:

1. the Wightman side is built from the Borchers/Fourier involution;
2. the OS side is built from the Euclidean/Laplace involution
   `osConjTensorProduct`;
3. these are not equal on the same literal test-function input in general.

So theorem 4 splits into two mathematically separate layers.

Layer A: the positive-time single-split cluster core.
- This is reduced to supplying a **corrected** one-factor transport statement,
  not the false same-shell identities `hleft` and `hright`.

Layer B: the public canonical boundary-value theorem
`bvt_F_clusterCanonicalEventually_translate`.
- This still hides the adapter from the public canonical BV shell to the
  positive-time single-split core.

The documentation must keep those two layers separate. If later Lean work
cannot point to an exact theorem name for one of them, that should be treated
as a genuine missing theorem, not hidden inside a long proof.

## 5. What theorem 3 should supply to theorem 4

Theorem 4 should not invent new positivity infrastructure. It should consume
the already-documented theorem-3 comparison package.

The old same-shell factor identities are withdrawn. The corrected theorem-slot
inventory needed by theorem 4 is:

```lean
def normalizedZeroDegreeLeftVector (d : ℕ) : PositiveTimeBorchersSequence d :=
  normalizedZeroDegreeRightVector d

lemma cluster_left_factor_transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ)) :
    WightmanInnerProduct d (bvt_W OS lgc)
      (PositiveTimeBorchersSequence.single n f hf_ord : BorchersSequence d)
      (normalizedZeroDegreeRightVector d : BorchersSequence d)
      =
    OSInnerProduct d OS.S
      (PositiveTimeBorchersSequence.single n f hf_ord : BorchersSequence d)
      (normalizedZeroDegreeRightVector d : BorchersSequence d) := by
  -- theorem-3 Package-I transport specialized to the degree-zero right vector;
  -- positive-degree right shells vanish by `normalizedZeroDegreeRightVector_funcs_pos`

lemma cluster_right_factor_transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (m : ℕ) (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    WightmanInnerProduct d (bvt_W OS lgc)
      (normalizedZeroDegreeLeftVector d : BorchersSequence d)
      (PositiveTimeBorchersSequence.single m g hg_ord : BorchersSequence d)
      =
    OSInnerProduct d OS.S
      (normalizedZeroDegreeLeftVector d : BorchersSequence d)
      (PositiveTimeBorchersSequence.single m g hg_ord : BorchersSequence d) := by
  -- same transport statement with the nontrivial factor on the right

theorem bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n m : ℕ) (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hleft : cluster_left_factor_transport (d := d) OS lgc n f hf_ord hf_compact)
    (hright : cluster_right_factor_transport (d := d) OS lgc m g hg_ord hg_compact) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R > 0 ∧
      ∀ a : Fin d → ℝ, (∑ i : Fin d, (a i)^2) > R^2 →
        ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
          ‖(∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                ((f.osConjTensorProduct
                  (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y)) -
            bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε := by
  -- exact same conclusion as the current legacy theorem
  -- `bvt_F_clusterCanonicalEventually_translate_of_singleSplitFactorComparison`,
  -- but with corrected transport inputs instead of false same-shell inputs
```

Those should be the exact hypotheses of the **corrected** theorem-4 bridge.

So the next production theorem on this lane should be the transport-input
replacement

```lean
theorem bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison
```

with the exact same conclusion as the legacy theorem, but consuming
`cluster_left_factor_transport` and `cluster_right_factor_transport` instead of
false same-shell identities.

If the current theorem
`bvt_F_clusterCanonicalEventually_translate_of_singleSplitFactorComparison`
continues to demand the false same-shell identities, then that theorem itself
must be treated as deprecated legacy infrastructure and replaced by the
transport-input variant before theorem 4 can be considered settled.

### 5.1. Exact derivation route for the one-factor identities

Note:

The "one-factor transport" / "single-split core" decomposition below is a Lean
implementation strategy chosen to fit the existing `WightmanInnerProduct` /
`BorchersSequence` API and the already-proved single-split production hooks. It
is **not** a paper decomposition. OS I Section 4.4 uses the full sesquilinear
identity `(4.22)` together with the spatial-translation limit and continuity
extension; it does not isolate one-factor or single-split layers. The Lean
strategy is justified only because `(4.22)` expands as a finite degree sum in
the repo's Borchers-sequence model, and the one-factor extraction lemmas are
how that finite sum is manipulated locally.

The needed one-factor transport statements should **not** be described as if
they fell out of theorem 3 by simply "setting one factor equal to the vacuum."
The corrected theorem-3 route no longer supplies same-shell identities at all.
The one-factor cluster inputs arise only after the degree-zero bookkeeping and
the Section-4.3 transport package are both made explicit.

The relevant already-proved production surfaces are:

1. `WightmanInnerProduct_right_single`
2. `OSInnerProduct_right_single`
3. `bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero`
4. `bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_zero_right`

The intended paper-faithful route is:

1. choose an auxiliary positive-time Borchers vector concentrated in right
   degree `0`;
2. rewrite the Wightman and OS inner products against that right-single degree
   `0` vector using `WightmanInnerProduct_right_single` and
   `OSInnerProduct_right_single`;
3. observe that the positive-degree `m > 0` shell comparisons supplied by
   theorem 3 are now vacuous, because the auxiliary right vector has no
   positive-degree components;
4. supply the remaining `m = 0` comparison explicitly as the normalized
   zero-degree bookkeeping theorem;
5. read off the desired one-factor identity.

The exact additional theorem-slot inventory is therefore:

```lean
def normalizedZeroDegreeRightVector (d : ℕ) : PositiveTimeBorchersSequence d := by
  exact
    PositiveTimeBorchersSequence.single 0 degreeZeroUnit
      (by
        -- degree 0 has no time coordinates, so ordered-positive-time support is automatic
        simpa using degreeZeroUnit_orderedSupport (d := d))

lemma normalizedZeroDegreeRightVector_bound
    (d : ℕ) :
    (normalizedZeroDegreeRightVector d : BorchersSequence d).bound = 0

lemma normalizedZeroDegreeRightVector_funcs_zero
    (d : ℕ) :
    ((normalizedZeroDegreeRightVector d : BorchersSequence d).funcs 0) = degreeZeroUnit

lemma normalizedZeroDegreeRightVector_funcs_pos
    (d : ℕ) :
    ∀ m > 0,
      ((normalizedZeroDegreeRightVector d : BorchersSequence d).funcs m) = 0

lemma conjTensorProduct_degreeZeroUnit_eq
    (n : ℕ) (f : SchwartzNPoint d n) :
    f.conjTensorProduct degreeZeroUnit = f

lemma osConjTensorProduct_degreeZeroUnit_eq
    (n : ℕ) (f : SchwartzNPoint d n) :
    f.osConjTensorProduct degreeZeroUnit = ZeroDiagonalSchwartz.ofClassical (f.osConj)

lemma ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq
    (n : ℕ) (f : SchwartzNPoint d n) :
    ZeroDiagonalSchwartz.ofClassical
      (f.osConjTensorProduct degreeZeroUnit)
      =
    ZeroDiagonalSchwartz.ofClassical (f.osConj)

lemma zeroDegree_right_single_wightman_extracts_factor
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) (f : SchwartzNPoint d n) :
    WightmanInnerProduct d (bvt_W OS lgc)
      (PositiveTimeBorchersSequence.single n f hf_ord : BorchersSequence d)
      (normalizedZeroDegreeRightVector d : BorchersSequence d)
      =
      bvt_W OS lgc n f := by
  -- proof transcript is frozen:
  --   `WightmanInnerProduct_right_single`
  --   -> `normalizedZeroDegreeRightVector_funcs_zero`
  --   -> `normalizedZeroDegreeRightVector_funcs_pos`
  --   -> `conjTensorProduct_degreeZeroUnit_eq`

lemma zeroDegree_right_single_os_extracts_factor
    (OS : OsterwalderSchraderAxioms d)
    (n : ℕ) (f : SchwartzNPoint d n) :
    OSInnerProduct d OS.S
      (PositiveTimeBorchersSequence.single n f hf_ord : BorchersSequence d)
      (normalizedZeroDegreeRightVector d : BorchersSequence d)
      =
      OS.S n (ZeroDiagonalSchwartz.ofClassical (f.osConj)) := by
  -- proof transcript is frozen:
  --   `OSInnerProduct_right_single`
  --   -> `normalizedZeroDegreeRightVector_funcs_zero`
  --   -> `normalizedZeroDegreeRightVector_funcs_pos`
  --   -> `osConjTensorProduct_degreeZeroUnit_eq`
  --   -> `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq`

lemma zero_degree_component_comparison_for_normalized_right_vector
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d) :
    WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d)
      (normalizedZeroDegreeRightVector d : BorchersSequence d)
      =
    OSInnerProduct d OS.S
      (F : BorchersSequence d)
      (normalizedZeroDegreeRightVector d : BorchersSequence d) := by
  -- proof transcript is frozen:
  --   specialize the repaired theorem-3 Section-4.3 comparison to the literal
  --   right witness `normalizedZeroDegreeRightVector d`
  --   -> discharge every `m > 0` component using
  --      `normalizedZeroDegreeRightVector_funcs_pos`
  --   -> leave exactly the `m = 0` component as the only surviving slot
```

The crucial documentation point is that
`normalizedZeroDegreeRightVector` should be the literal degree-zero unit
generator, not an abstract existential placeholder. The frozen theorem-creation
queue on this lane is the 12-slot package
`normalizedZeroDegreeRightVector`
-> `normalizedZeroDegreeRightVector_bound`
-> `normalizedZeroDegreeRightVector_funcs_zero`
-> `normalizedZeroDegreeRightVector_funcs_pos`
-> `conjTensorProduct_degreeZeroUnit_eq`
-> `osConjTensorProduct_degreeZeroUnit_eq`
-> `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq`
-> `zeroDegree_right_single_wightman_extracts_factor`
-> `zeroDegree_right_single_os_extracts_factor`
-> `zero_degree_component_comparison_for_normalized_right_vector`
-> `cluster_left_factor_transport`
-> `cluster_right_factor_transport`.
There is intentionally **no** extra contract-level theorem slot such as
`normalizedZeroDegreeRightVector_is_unit_normalized`: if a later proof wants a
scalar evaluation fact, it should derive it locally from
`normalizedZeroDegreeRightVector_funcs_zero` and the literal definition of
`degreeZeroUnit` rather than expanding the frozen public queue.

Once those structural lemmas are in place, the remaining theorem-4 input is no
longer a same-shell factor identity. It is the exact transport comparison
stated above in `cluster_left_factor_transport` and
`cluster_right_factor_transport`.

The right-factor theorem is the same argument with the nontrivial factor moved
to the right.

So the honest theorem-4 dependency is:

1. theorem 3 gives the corrected Section-4.3 transport package,
2. the degree-zero bookkeeping theorem supplies the missing `hzero` input,
3. the one-factor transport statements are extracted by the right-single
   inner-product lemmas,
4. only then can
   the theorem-4 single-split core be stated on the correct transport-input
   surface, concretely through
   `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`.

This is exactly the point where the theorem-4 route touches the "Hermitian
zero-right repair" style bookkeeping already visible in the theorem-3
production chain. The docs should keep that dependency explicit.

### 5.2. Exact `m > 0` versus `m = 0` case split

The later Lean implementation should not leave the zero-degree bookkeeping
inside a single opaque proof term. The route should be documented as an actual
case split.

For the corrected left-factor transport theorem:

1. fix `F_left := PositiveTimeBorchersSequence.single n f hf_ord`,
2. fix `G0 := normalizedZeroDegreeRightVector d`,
3. use theorem 3 only through the corrected transport package, not through any
   same-shell positive-time comparison theorem,
4. observe that every positive-degree right shell comparison is vacuous because
   `(G0 : BorchersSequence d).funcs m = 0` for `m > 0`,
5. provide the unique surviving `m = 0` transport-side bookkeeping theorem;
6. rewrite the resulting Wightman and OS Hilbert-space matrix elements by the
   right-single extraction lemmas;
7. finally rewrite the normalization constants away via the degree-zero unit
   bookkeeping lemmas.

The right-factor identity is the same argument with the nontrivial component on
the right and the normalized degree-zero vector on the left. No new analytic
continuation theorem appears here; the entire step is algebraic/bookkeeping
above theorem 3.

The old same-shell pseudocode is withdrawn. The corrected theorem surface is:

1. theorem 3 supplies the transport package from Section 4.3;
2. theorem 4 adds the degree-zero bookkeeping;
3. right-single extraction turns that transport identity into the one-factor
   transport statements needed by the cluster core.

## 6. Positive-time single-split core

Once the two corrected one-factor transport statements are available, the
positive-time
single-split cluster theorem is already formal.

The exact theorem slot is:

```lean
theorem bvt_cluster_positiveTime_singleSplit_core
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (n m : ℕ) (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R > 0 ∧
      ∀ a : Fin d → ℝ, (∑ i : Fin d, (a i)^2) > R^2 →
        ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
          ‖(∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                ((f.osConjTensorProduct
                  (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g)) y)) -
            bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε := by
  -- use the corrected theorem-4 bridge
  -- `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`,
  -- not the legacy same-shell factor-comparison theorem
  ...
```

This is the theorem that should be proved first once theorem 3 is available.
No new analytic continuation is needed here, but the theorem surface must be
repaired away from the false same-shell inputs before production resumes.

## 7. Public theorem-shape still missing

The public frontier theorem in `OSToWightmanBoundaryValues.lean` does not ask
for ordered-positive-time support or compact support. So after the
single-split core closes, one more wrapper layer still remains.

Cross-check against the current repo tree:

1. `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean`
   already contains the legacy core-side reduction theorems
   `bvt_F_clusterCanonicalEventually_translate_of_singleSplitLargeSpatial`,
   `...of_singleSplitSchwingerLargeSpatial`, and
   `...of_singleSplitFactorComparison`;
2. `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean`
   already contains only the final checked wrapper layer, at exact source
   anchors `:27 :: bv_cluster_transfer_of_canonical_eventually`,
   `:398 :: private bvt_F_clusterCanonicalEventually_translate`,
   `:414 :: private bvt_F_clusterCanonicalEventually`, and
   `:473 :: private bvt_W_cluster`;
3. there is **not yet** any separately named production theorem for the public
   canonical-shell adapter package
   (`canonical_cluster_integrand_eq_singleSplit_integrand`,
   `canonical_translate_factor_eq_singleSplit_translate_factor`,
   `singleSplit_core_rewrites_to_canonical_shell`,
   `canonical_shell_limit_of_rewrite`,
   `bvt_cluster_canonical_from_positiveTime_core`);
4. therefore those names below are part of the required implementation
   contract for the next theorem-4 pass, not claims about already-existing
   code.

The documentation should record that layer honestly as:

```lean
theorem bvt_cluster_canonical_from_positiveTime_core
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
      ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
            ‖(∫ x : NPointDomain d (n + m),
                bvt_F OS lgc (n + m) (fun k μ =>
                  ↑(x k μ) +
                    t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I) *
                  ((f.tensorProduct (translateSchwartzNPoint (d := d) a g)) x)) -
              bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε := by
  -- exact adapter from the public canonical shell to the positive-time
  -- single-split core
```

At the current repo state, this adapter theorem is not yet isolated under a
separate production name. More precisely: the repo has the final private theorem
`OSToWightmanBoundaryValues.lean :: bvt_F_clusterCanonicalEventually_translate`,
but it does **not** yet expose the intermediate public-adapter package under
separate theorem names. The docs should therefore not pretend the adapter is
already mechanical or already factored in code. But they should also not treat
it as a new Euclidean cluster theorem. It is a wrapper/adaptation problem
sitting strictly above the already-proved single-split core.

### 7.1. Exact imported supplier surfaces for the missing canonical-shell adapter

To keep the later Lean pass from rediscovering the import graph by grep, the
missing canonical-shell adapter package is now constrained to the following
supplier map.

1. `canonical_cluster_integrand_eq_singleSplit_integrand`
   should consume only checked generic shell data already imported through
   `OSToWightmanBoundaryValuesComparison.lean`:
   - `canonicalForwardConeDirection`
   - `canonicalForwardConeDirection_mem`
   together with the public theorem-4 target shell appearing in the statement
   of private `bvt_F_clusterCanonicalEventually_translate` and the base-core
   shell appearing in
   `OSToWightmanBoundaryValuesBase.lean ::
   bvt_cluster_positiveTime_singleSplit_core`.
   Its job is purely to rewrite the canonical-direction integrand into the
   positive-time `xiShift`/single-split integrand shape. It does **not**
   consume any cluster-specific theorem already living in
   `BoundaryValueLimits.lean`, because none exist there today.
2. `canonical_translate_factor_eq_singleSplit_translate_factor`
   should consume only the checked generic translation shell objects already in
   scope in `OSToWightmanBoundaryValues.lean`:
   - `translateSchwartzNPoint`
   - the same checked `canonicalForwardConeDirection` surface
   - the explicit positive-time translated factor appearing in the base-core
     theorem statement.
   This theorem is a parameter/argument rewrite only; it should not invoke any
   OS cluster theorem.
3. `singleSplit_core_rewrites_to_canonical_shell`
   should be the first theorem that actually consumes the repaired base-core
   theorem `bvt_cluster_positiveTime_singleSplit_core`. Its allowed imported
   suppliers are exactly:
   - `bvt_cluster_positiveTime_singleSplit_core`
   - `canonical_cluster_integrand_eq_singleSplit_integrand`
   - `canonical_translate_factor_eq_singleSplit_translate_factor`.
   So the proof transcript order is fixed: first the two explicit rewrites,
   then apply the positive-time core.
4. `canonical_shell_limit_of_rewrite`
   should consume only the checked generic limit-transport surfaces already in
   `OSToWightmanBoundaryValueLimits.lean`, but its internal proof transcript is
   now fixed more sharply than a bare list of allowed imports. The endorsed
   order is:
   - first, use
     `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq` to identify the
     positive-real trace of the chosen scalar holomorphic object with the raw
     `singleSplit_xiShift` boundary-value integral;
   - second, if the canonical-shell statement is presented via a separately
     defined holomorphic scalar trace, use
     `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue` together with
     `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq` to show that this
     canonical-shell trace agrees with the chosen checked scalar holomorphic
     object on the full right half-plane; no other uniqueness theorem slot is
     allowed here;
   - third, discharge the actual `t → 0+` transport to the Wightman target with
     `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`.
   The auxiliary checked surfaces
   `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift` and
   `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger`
   remain available only as lower supplier legs when the rewritten
   positive-time core is first routed through the Schwinger time-shift shell;
   they are not permission to replace the final Wightman-target limit step with
   a Schwinger-only endpoint. The deprecated theorem
   `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_schwinger_eq_bvt_W_conjTensorProduct_timeShift`
   is explicitly out of contract for theorem 4.
   The implementation rule here is strict: `canonical_shell_limit_of_rewrite`
   may use theorem-3 scalar-holomorphic / limit transport as generic imported
   machinery, but it may not claim that `BoundaryValueLimits.lean` already owns
   a theorem-4 canonical cluster adapter theorem, and it may not leave the
   positive-real identification / right-half-plane uniqueness / final Wightman
   limit order implicit.
5. `bvt_cluster_canonical_from_positiveTime_core`
   should consume only:
   - `canonical_shell_limit_of_rewrite`.
   It is therefore a thin public wrapper theorem immediately below private
   `bvt_F_clusterCanonicalEventually_translate`, not a place for hidden new
   analytic content. In particular, once
   `canonical_shell_limit_of_rewrite` has produced the exact eventual
   canonical-shell statement, `bvt_cluster_canonical_from_positiveTime_core`
   should do no further shell rewriting and should not reopen
   `singleSplit_core_rewrites_to_canonical_shell` by hand.

## 8. Exact proof decomposition for theorem 4

The later Lean proof should be carried out in the following exact order.
This is intentionally finer than a slogan like “bridge, then adapter, then
wrapper”: each row below is a distinct implementation obligation with a fixed
next consumer.

### 8.0. Owner / consumes / exports / next-consumer ledger

The theorem-4 route should now be read as the following literal execution
ledger. This table is the contract-level version of the prose decomposition
below: later Lean work should be able to implement the rows in order without
having to guess where the positivity-side extraction ends, where the repaired
base bridge begins, or where the public canonical-shell adapter first imports
any theorem-3 limit transport.

| Slot | Owner | Consumes | Exports | Next consumer |
| --- | --- | --- | --- | --- |
| `normalizedZeroDegreeRightVector` | `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean` | degree-`0` unit shell only | literal positive-time Borchers vector concentrated in degree `0` with value `1` | its structural lemmas, then the normalization rewrites, then the right-single extraction lemmas |
| `normalizedZeroDegreeRightVector_bound` / `..._funcs_zero` / `..._funcs_pos` | same file | `normalizedZeroDegreeRightVector` | exact bound / degree-`0` / positive-degree-vanishing facts for the normalized witness | `conjTensorProduct_degreeZeroUnit_eq`, `osConjTensorProduct_degreeZeroUnit_eq`, `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq`, the right-single extraction pair, and the degree-`0` comparison theorem |
| `conjTensorProduct_degreeZeroUnit_eq` | same file | `normalizedZeroDegreeRightVector_funcs_zero` | exact Wightman-side degree-`0` normalization rewrite | `zeroDegree_right_single_wightman_extracts_factor` |
| `osConjTensorProduct_degreeZeroUnit_eq` | same file | `normalizedZeroDegreeRightVector_funcs_zero` | exact OS-side degree-`0` normalization rewrite | `zeroDegree_right_single_os_extracts_factor` |
| `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq` | same file | `normalizedZeroDegreeRightVector_funcs_zero` | exact zero-diagonal wrapper / cast cleanup for the degree-`0` unit shell | both right-single extraction lemmas and the degree-`0` comparison theorem |
| `zeroDegree_right_single_wightman_extracts_factor` | same file | checked `WightmanInnerProduct_right_single` plus the three normalization lemmas above | extraction of the left Wightman factor against the normalized degree-`0` right vector | `cluster_left_factor_transport` |
| `zeroDegree_right_single_os_extracts_factor` | same file | checked `OSInnerProduct_right_single` plus the same normalization lemmas | extraction of the left OS factor against the normalized degree-`0` right vector | `cluster_left_factor_transport` |
| `zero_degree_component_comparison_for_normalized_right_vector` | same file | repaired theorem-3 Section-4.3 transport package plus the normalized degree-`0` structural lemmas | the unique surviving `m = 0` transport comparison | `cluster_left_factor_transport`, `cluster_right_factor_transport` |
| `cluster_left_factor_transport` | same file | `zeroDegree_right_single_wightman_extracts_factor`, `zeroDegree_right_single_os_extracts_factor`, `zero_degree_component_comparison_for_normalized_right_vector` | corrected theorem-3-to-theorem-4 left one-factor transport identity | `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison` |
| `cluster_right_factor_transport` | same file | the same normalized witness package reused via `normalizedZeroDegreeLeftVector d := normalizedZeroDegreeRightVector d`, together with the corresponding right-single extraction rewrites and `zero_degree_component_comparison_for_normalized_right_vector`; no second normalization package is allowed here | corrected theorem-3-to-theorem-4 right one-factor transport identity | `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison` |
| `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison` | `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValuesBase.lean` | checked base anchors `:2214 :: ...singleSplitLargeSpatial`, `:2352 :: ...singleSplitSchwingerLargeSpatial`, `:2514 :: ...singleSplitFactorComparison`, plus `cluster_left_factor_transport` and `cluster_right_factor_transport` | repaired positive-time single-split bridge with corrected transport inputs | `bvt_cluster_positiveTime_singleSplit_core` |
| `bvt_cluster_positiveTime_singleSplit_core` | same file | `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison` only | the sole theorem-4 cluster statement allowed to leave the base file | `singleSplit_core_rewrites_to_canonical_shell` only |
| `canonical_cluster_integrand_eq_singleSplit_integrand` | `OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean` | only `canonicalForwardConeDirection`, `canonicalForwardConeDirection_mem`, the public canonical-shell statement shape, and the repaired base-core shell statement; it may **not** import `OSToWightmanBoundaryValueLimits.lean` | integrand-level rewrite from the public canonical shell to the repaired positive-time single-split shell | `singleSplit_core_rewrites_to_canonical_shell` |
| `canonical_translate_factor_eq_singleSplit_translate_factor` | same file | only `translateSchwartzNPoint`, the same canonical-direction surfaces, and the translated factor appearing in the repaired base-core theorem; it may **not** hide any limit transport | translated-right-factor rewrite needed before the base-core theorem can be applied | `singleSplit_core_rewrites_to_canonical_shell` |
| `singleSplit_core_rewrites_to_canonical_shell` | same file | `bvt_cluster_positiveTime_singleSplit_core`, `canonical_cluster_integrand_eq_singleSplit_integrand`, `canonical_translate_factor_eq_singleSplit_translate_factor` | the repaired positive-time core restated in the exact public canonical-shell form | `canonical_shell_limit_of_rewrite` |
| `canonical_shell_limit_of_rewrite` | same file | `singleSplit_core_rewrites_to_canonical_shell` plus only the checked scalar-holomorphic / right-half-plane uniqueness / `t -> 0+` transport package from `OSToWightmanBoundaryValueLimits.lean`, in the strict internal order fixed below | transport from the rewritten shell statement to the eventual canonical-shell limit statement | `bvt_cluster_canonical_from_positiveTime_core` |
| `bvt_cluster_canonical_from_positiveTime_core` | same file | `canonical_shell_limit_of_rewrite` only | the full public theorem-4 canonical-shell adapter theorem | `OSToWightmanBoundaryValues.lean:398 :: private bvt_F_clusterCanonicalEventually_translate` only |
| `OSToWightmanBoundaryValues.lean:398 :: private bvt_F_clusterCanonicalEventually_translate` | same file | `bvt_cluster_canonical_from_positiveTime_core` only | checked private frontier theorem | downstream `:414 :: private bvt_F_clusterCanonicalEventually` -> `:27 :: bv_cluster_transfer_of_canonical_eventually` -> `:473 :: private bvt_W_cluster` |

1. Prove the normalized degree-`0` witness package in
   `OSToWightmanPositivity.lean`:
   `normalizedZeroDegreeRightVector`
   -> `normalizedZeroDegreeRightVector_bound`
   -> `normalizedZeroDegreeRightVector_funcs_zero`
   -> `normalizedZeroDegreeRightVector_funcs_pos`.
2. Close the hidden scalar/cast cleanup lemmas in the same file:
   `conjTensorProduct_degreeZeroUnit_eq`
   -> `osConjTensorProduct_degreeZeroUnit_eq`
   -> `ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq`.
3. Package the checked right-single extraction theorems into theorem-4-facing
   slots:
   `zeroDegree_right_single_wightman_extracts_factor`
   -> `zeroDegree_right_single_os_extracts_factor`.
4. Compare the resulting degree-`0` components via
   `zero_degree_component_comparison_for_normalized_right_vector`.
5. Only then close the one-factor transport pair
   `cluster_left_factor_transport`
   -> `cluster_right_factor_transport`.
   The right lane must reuse the same normalized witness via the definitional
   alias `normalizedZeroDegreeLeftVector d := normalizedZeroDegreeRightVector d`;
   it may not introduce a second normalization package.
6. Build the repaired base-file bridge
   `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`
   in `OSToWightmanBoundaryValuesBase.lean`, consuming only the checked base
   anchors `:2214`, `:2352`, `:2514` together with
   `cluster_left_factor_transport` and `cluster_right_factor_transport`.
7. Export the thin base wrapper
   `bvt_cluster_positiveTime_singleSplit_core`.
   This is the sole theorem allowed to leave
   `OSToWightmanBoundaryValuesBase.lean` and enter the public adapter ladder.
8. Build the public canonical-shell rewrite pair in
   `OSToWightmanBoundaryValues.lean`:
   `canonical_cluster_integrand_eq_singleSplit_integrand`
   -> `canonical_translate_factor_eq_singleSplit_translate_factor`.
9. Package those two rewrites together with the base export as
   `singleSplit_core_rewrites_to_canonical_shell`.
   The proof order here is literal and should be written that way in Lean:
   - first introduce the public canonical-shell goal in the exact statement
     shape consumed later by `canonical_shell_limit_of_rewrite`;
   - second prove a local integrand-rewrite sublemma/have using
     `canonical_cluster_integrand_eq_singleSplit_integrand`;
   - third prove a separate translated-factor sublemma/have using
     `canonical_translate_factor_eq_singleSplit_translate_factor`;
   - fourth rewrite the canonical-shell goal by those two sublemmas so the goal
     now matches the positive-time single-split shell verbatim;
   - fifth apply `bvt_cluster_positiveTime_singleSplit_core` with no theorem-3
     limit machinery in scope.
10. Transport that rewritten shell statement through the checked generic
    theorem-3 scalar-holomorphic machinery by proving
    `canonical_shell_limit_of_rewrite`.
    Its internal proof transcript is fixed more sharply than a theorem list:
    - first bind the output of
      `singleSplit_core_rewrites_to_canonical_shell` as the only shell-level
      input to this theorem;
    - second instantiate the checked scalar holomorphic object and identify its
      positive-real trace with the rewritten shell statement using
      `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`;
    - third, only if the chosen canonical-shell scalar was introduced under a
      separately named trace, use
      `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue` together with
      `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq` to upgrade the
      positive-real identity to right-half-plane equality;
    - fourth discharge the actual `t -> 0+` passage to the Wightman target only
      with
      `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`;
    - fifth export the exact eventual canonical-shell statement consumed by
      `bvt_cluster_canonical_from_positiveTime_core`, with no residual mention
      of `bvt_cluster_positiveTime_singleSplit_core` or of the two rewrite
      lemmas.
11. Package the resulting public adapter as
    `bvt_cluster_canonical_from_positiveTime_core`, then feed only that theorem
    into the checked frontier shell
    `OSToWightmanBoundaryValues.lean:398 :: private bvt_F_clusterCanonicalEventually_translate`.
    The implementation order here is also fixed:
    - first state `bvt_cluster_canonical_from_positiveTime_core` with exactly
      the same eventual canonical-shell surface produced by
      `canonical_shell_limit_of_rewrite`;
    - second prove it by a single direct application of
      `canonical_shell_limit_of_rewrite`;
    - third let private
      `bvt_F_clusterCanonicalEventually_translate` consume only this wrapper,
      after which the already-landed downstream consumers remain
      `:414 :: private bvt_F_clusterCanonicalEventually`
      -> `:27 :: bv_cluster_transfer_of_canonical_eventually`
      -> `:473 :: private bvt_W_cluster`.

The later implementation should not invert that order, collapse multiple rows
back into a black-box “canonical adapter”, or import theorem-3 limit transport
before `singleSplit_core_rewrites_to_canonical_shell` has already fixed the
exact shell statement being transported.

Two negative routing rules are part of this ledger:

1. the normalization / one-factor package in `OSToWightmanPositivity.lean`
   must be completely finished before the repaired bridge in
   `OSToWightmanBoundaryValuesBase.lean` is stated, rather than letting the
   base file hide degree-`0` bookkeeping or right-single extraction work;
2. the public adapter in `OSToWightmanBoundaryValues.lean` must remain a pure
   rewrite/limit-transport layer above `bvt_cluster_positiveTime_singleSplit_core`.
   In particular, `canonical_cluster_integrand_eq_singleSplit_integrand` and
   `canonical_translate_factor_eq_singleSplit_translate_factor` are not allowed
   to import theorem-3 limit transport early, and
   `private bvt_F_clusterCanonicalEventually_translate` is not allowed to hide
   any leftover rewrite or bridge work behind the final wrapper.

## 9. Exact theorem-name dictionary for theorem 4

The theorem names that should appear in the eventual proof script are:

Checked-present today in the repo tree:

1. `bvt_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero`
2. `bvt_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero_schwinger`
3. `bvt_eq_schwinger_of_tendsto_singleSplit_xiShift_translate_spatial_right_nhdsWithin_zero`
4. `schwinger_cluster_osConjTensorProduct_translate_spatial_right_local`
5. `osInner_single_translate_spatial_right_cluster_local`
6. `bvt_F_clusterCanonicalEventually_translate_of_singleSplitLargeSpatial`
7. `bvt_F_clusterCanonicalEventually_translate_of_singleSplitSchwingerLargeSpatial`
8. `bv_cluster_transfer_of_canonical_eventually`
9. private `bvt_F_clusterCanonicalEventually_translate`
10. private `bvt_F_clusterCanonicalEventually`
11. private `bvt_W_cluster`

Planned theorem-4 package names that are **not yet checked-present** and must be
implemented explicitly:

1. `normalizedZeroDegreeRightVector`
2. `normalizedZeroDegreeRightVector_bound`
3. `normalizedZeroDegreeRightVector_funcs_zero`
4. `normalizedZeroDegreeRightVector_funcs_pos`
5. `zeroDegree_right_single_wightman_extracts_factor`
6. `zeroDegree_right_single_os_extracts_factor`
7. `zero_degree_component_comparison_for_normalized_right_vector`
8. `cluster_left_factor_transport`
9. `cluster_right_factor_transport`
10. `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`
11. `bvt_cluster_positiveTime_singleSplit_core`
12. `canonical_cluster_integrand_eq_singleSplit_integrand`
13. `canonical_translate_factor_eq_singleSplit_translate_factor`
14. `singleSplit_core_rewrites_to_canonical_shell`
15. `canonical_shell_limit_of_rewrite`
16. `bvt_cluster_canonical_from_positiveTime_core`

`bvt_F_clusterCanonicalEventually_translate_of_singleSplitFactorComparison`
may still appear only as a legacy source theorem reused while proving the new
transport-input variant; it is no longer part of the endorsed end-state
contract.

If the eventual implementation does not visibly use that chain, it is likely
drifting away from the current production route.

## 10. Do not do this

1. Do not reopen theorem 3 inside theorem 4.
2. Do not invent a new same-shell Euclidean/Minkowski comparison theorem.
3. Do not bypass the already-proved Euclidean cluster theorem with an ad hoc
   dominated-convergence argument on the boundary-value integral.
4. Do not mix the reverse-direction `R -> E` cluster notes from
   `docs/cluster_property_analysis.md` into this forward theorem-4 route.
5. Do not hide the public canonical-to-positive-time adapter inside the final
   `sorry` proof. If it needs a theorem, name it explicitly first.

## 11. Minimal Lean pseudocode for the full closure

```lean
private theorem bvt_F_clusterCanonicalEventually_translate
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
      ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
            ‖(∫ x : NPointDomain d (n + m),
                bvt_F OS lgc (n + m) (fun k μ =>
                  ↑(x k μ) +
                    t * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I) *
                  ((f.tensorProduct (translateSchwartzNPoint (d := d) a g)) x)) -
              bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε := by
  -- Below this wrapper, the repaired base bridge has already been closed in
  -- OStoWightmanBoundaryValuesBase.lean and exported only through the thin row
  -- `bvt_cluster_positiveTime_singleSplit_core`.
  have hcore : _ :=
    bvt_cluster_positiveTime_singleSplit_core (d := d) (OS := OS) (lgc := lgc)
  -- First canonical-shell rewrite row: integrand only.
  have hintegrand : _ :=
    canonical_cluster_integrand_eq_singleSplit_integrand
      (d := d) (OS := OS) (lgc := lgc)
  -- Second canonical-shell rewrite row: translated factor only.
  have htranslate : _ :=
    canonical_translate_factor_eq_singleSplit_translate_factor
      (d := d) (OS := OS) (lgc := lgc)
  -- Package those three inputs into the exact positive-time core shell shape.
  have hshell : _ :=
    singleSplit_core_rewrites_to_canonical_shell
      (d := d) (OS := OS) (lgc := lgc)
      hcore hintegrand htranslate
  -- Only now import the theorem-3 scalar-holomorphic / limit machinery.
  have hlimit : _ :=
    canonical_shell_limit_of_rewrite (d := d) (OS := OS) (lgc := lgc) hshell
  -- Thin public adapter immediately above the checked private frontier.
  exact bvt_cluster_canonical_from_positiveTime_core
    (d := d) (OS := OS) (lgc := lgc) hlimit
```

This pseudocode is intentionally more verbose than the previous two-line sketch:
it makes explicit that the checked private frontier theorem is *not* allowed to
hide the integrand rewrite, translated-factor rewrite, shell-level reduction,
or limit transport. Those rows must already exist as separate named lemmas or
theorems before the final wrapper closes.

The point of this pseudocode is not that the final theorem is one line. The
point is that every real mathematical ingredient has already been named above.

## 12. Signature cross-checks and implementation contract

The theorem-4 blueprint should now be explicit about which signatures have
already been checked against production, which new local objects must be
introduced exactly as documented below, and which file owns each of them.

### 12.1. Confirmed existing theorem signatures

The following two reduction theorems are already present with the exact
single-right-factor shape needed here:

```lean
theorem WightmanInnerProduct_right_single
    (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (W n))
    (F : BorchersSequence d) {m : ℕ} (g : SchwartzNPoint d m) :
    WightmanInnerProduct d W F (BorchersSequence.single m g) =
      ∑ n ∈ Finset.range (F.bound + 1),
        W (n + m) ((F.funcs n).conjTensorProduct g)
```

```lean
theorem OSInnerProduct_right_single
    (S : (n : ℕ) → ZeroDiagonalSchwartz d n → ℂ)
    (hlin : ∀ n, IsLinearMap ℂ (S n))
    (F : BorchersSequence d) {m : ℕ} (g : SchwartzNPoint d m) :
    OSInnerProduct d S F (BorchersSequence.single m g) =
      ∑ n ∈ Finset.range (F.bound + 1),
        S (n + m) (ZeroDiagonalSchwartz.ofClassical
          ((F.funcs n).osConjTensorProduct g))
```

So the later theorem-4 port should not invent any custom right-single lemma.
The existing production theorems already have the correct shape.

### 12.2. Fixed specification of `normalizedZeroDegreeRightVector`

The doc-level object

```lean
normalizedZeroDegreeRightVector : PositiveTimeBorchersSequence d
```

should be implemented only with the following exact semantic properties:

1. `(normalizedZeroDegreeRightVector d : BorchersSequence d).bound = 0`;
2. `((normalizedZeroDegreeRightVector d : BorchersSequence d).funcs 0)` is the
   degree-zero Schwartz function equal to the scalar `1`;
3. `((normalizedZeroDegreeRightVector d : BorchersSequence d).funcs m) = 0` for
   all `m > 0`;
4. the ordered-positive-time support condition is automatic because degree `0`
   has no time coordinates.

The Lean definition should therefore be "the positive-time single concentrated
at degree `0` with value `1`," and the implementation should prove those four
properties immediately and then use only those lemmas. The theorem-4 port
should not rely on unfolding the definition away from those structural lemmas.

### 12.3. Exact theorem package for the one-factor extraction

The later Lean port should build theorem 4 through the following exact theorem
package names unless an exact compile failure forces a local renaming. If that
happens, the docs must be updated at the same time.

```lean
def normalizedZeroDegreeRightVector (d : ℕ) : PositiveTimeBorchersSequence d

lemma normalizedZeroDegreeRightVector_bound
lemma normalizedZeroDegreeRightVector_funcs_zero
lemma normalizedZeroDegreeRightVector_funcs_pos

lemma zeroDegree_right_single_wightman_extracts_factor
lemma zeroDegree_right_single_os_extracts_factor
lemma zero_degree_component_comparison_for_normalized_right_vector
lemma cluster_left_factor_transport
lemma cluster_right_factor_transport
lemma bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison
```

The line `zero_degree_component_comparison_for_normalized_right_vector` is the
only genuinely theorem-4-specific new shell datum below theorem 3. The later
transport-factor theorems and corrected bridge then sit on top of that datum as
explicit consumer packaging.

### 12.4. Estimated Lean line counts

The theorem-4 closure is now explicit enough to estimate file size honestly.

1. `normalizedZeroDegreeRightVector` definition plus the three structural
   lemmas:
   roughly `20-45` lines.
2. `zeroDegree_right_single_wightman_extracts_factor`:
   roughly `20-40` lines. It should be a packaging lemma above the checked
   supplier `OSReconstruction/Wightman/Reconstruction/Core.lean ::
   WightmanInnerProduct_right_single`, not a new right-single theorem from
   scratch.
3. `zeroDegree_right_single_os_extracts_factor`:
   roughly `20-45` lines. It should package the checked supplier
   `OSReconstruction/Wightman/Reconstruction/SchwingerOS.lean ::
   OSInnerProduct_right_single` against the normalized degree-`0` witness,
   again not rediscover the base right-single identity.
4. `zero_degree_component_comparison_for_normalized_right_vector`:
   roughly `25-55` lines.
5. `cluster_left_factor_transport`:
   roughly `40-80` lines.
6. `cluster_right_factor_transport`:
   roughly `40-80` lines.
7. `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`:
   roughly `20-45` lines once the transport inputs are in place.
8. the positive-time single-split cluster core wrapper:
   roughly `20-40` lines.
9. the final public canonical-shell adapter:
   roughly `25-60` lines.

So theorem 4 should now be thought of as an approximately `210-445` line
package, and most of that is algebraic extraction/bookkeeping rather than new
analytic continuation.

### 12.4.1. Exact theorem package for the public canonical-shell adapter

The positive-time cluster core and the public canonical-shell statement should
be connected by a named adapter package rather than by hidden rewrites in the
final `sorry`.

Repository-status note:

1. none of the adapter theorems listed in this subsection currently exist under
   these names in the checked repo tree;
2. the only current production object above the base-layer reductions is the
   final checked private wrapper
   `OSToWightmanBoundaryValues.lean :398 :: bvt_F_clusterCanonicalEventually_translate`;
3. the next Lean/doc pass should therefore introduce or explicitly rename this
   missing adapter package before touching the final wrapper proof.

```lean
lemma singleSplit_core_rewrites_to_canonical_shell
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    positiveTime_singleSplit_cluster_core_statement (d := d) OS lgc ->
      canonical_cluster_shell_statement (d := d) OS lgc

lemma canonical_shell_limit_of_rewrite
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    canonical_cluster_shell_statement (d := d) OS lgc ->
      canonical_cluster_limit_statement (d := d) OS lgc

theorem bvt_cluster_canonical_from_positiveTime_core
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    canonical_cluster_limit_statement (d := d) OS lgc := by
  have hcore := bvt_cluster_positiveTime_singleSplit_core (d := d) (OS := OS) (lgc := lgc)
  have hshell :=
    singleSplit_core_rewrites_to_canonical_shell (d := d) OS lgc hcore
  exact canonical_shell_limit_of_rewrite (d := d) OS lgc hshell
```

The documentation point is that this public adapter should consume the
positive-time core **forward**, not backwards through a misoriented rewrite:

1. first prove the positive-time single-split core theorem,
2. rewrite that core statement into the public canonical shell,
3. then pass from the rewritten shell statement to the public eventual/limit
   statement,
4. then expose that result through the thin public adapter theorem consumed by
   the final private frontier wrapper.

The exact slot-by-slot consumer contract is therefore:

0. below the public adapter, the repaired base bridge is itself exclusive:
   `bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`
   may consume only the checked base anchors
   `OSToWightmanBoundaryValuesBase.lean:2214 :: bvt_F_clusterCanonicalEventually_translate_of_singleSplitLargeSpatial`,
   `:2352 :: bvt_F_clusterCanonicalEventually_translate_of_singleSplitSchwingerLargeSpatial`,
   and `:2514 :: bvt_F_clusterCanonicalEventually_translate_of_singleSplitFactorComparison`,
   together with `cluster_left_factor_transport` and
   `cluster_right_factor_transport`; then
   `bvt_cluster_positiveTime_singleSplit_core` is the sole theorem allowed to
   leave `OSToWightmanBoundaryValuesBase.lean` and enter the public adapter
   ladder;
1. `singleSplit_core_rewrites_to_canonical_shell` consumes only
   `bvt_cluster_positiveTime_singleSplit_core`,
   `canonical_cluster_integrand_eq_singleSplit_integrand`, and
   `canonical_translate_factor_eq_singleSplit_translate_factor`;
2. `canonical_shell_limit_of_rewrite` consumes only
   `singleSplit_core_rewrites_to_canonical_shell` plus the checked generic
   scalar-holomorphic / `t → 0+` transport package imported from
   `OSToWightmanBoundaryValueLimits.lean`, and the inner order is fixed:
   `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`
   -> optional right-half-plane uniqueness via
   `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue` and
   `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq`
   -> final limit transport by
   `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`.
   The Schwinger-target theorems
   `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift` and
   `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger`
   are lower supplier legs only, and the deprecated bridge
   `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_schwinger_eq_bvt_W_conjTensorProduct_timeShift`
   is forbidden here;
3. `bvt_cluster_canonical_from_positiveTime_core` consumes only
   `canonical_shell_limit_of_rewrite` and is the only public theorem allowed to
   feed the checked frontier `OSToWightmanBoundaryValues.lean:398 :: private
   bvt_F_clusterCanonicalEventually_translate`;
4. private `bvt_F_clusterCanonicalEventually_translate` consumes only
   `bvt_cluster_canonical_from_positiveTime_core`, so the literal frontier
   boundary is frozen as
   `canonical_shell_limit_of_rewrite`
   -> `bvt_cluster_canonical_from_positiveTime_core`
   -> `:398 :: private bvt_F_clusterCanonicalEventually_translate`.

The degree-zero normalization lemmas and theorem-3 one-factor transport package
belong strictly below this public adapter ladder: they are consumed while
proving the repaired bridge
`bvt_F_clusterCanonicalEventually_translate_of_singleSplitTransportComparison`
and must not be re-imported or silently reconstructed inside the later
canonical-shell adapter. Likewise this adapter package should not contain any
new analytic-continuation content beyond the already checked generic
limit-transport surfaces just listed.

### 12.4.2. Exact proof transcript for the public canonical-shell adapter

The later Lean implementation should write the public adapter as an explicit
three-stage rewrite/transport package:

1. rewrite the public canonical cluster integrand into the positive-time
   single-split shell using the existing canonical-direction / `xiShift`
   comparison lemmas,
2. rewrite the translated right factor into the single-split positive-time form
   used by
   `bvt_cluster_positiveTime_singleSplit_core`,
3. transport the eventual/limit statement through those two rewrites and then
   apply the already-proved positive-time core theorem.

So the actual theorem slots should be read as:

```lean
lemma canonical_cluster_integrand_eq_singleSplit_integrand
lemma canonical_translate_factor_eq_singleSplit_translate_factor
lemma singleSplit_core_rewrites_to_canonical_shell
lemma canonical_shell_limit_of_rewrite
theorem bvt_cluster_canonical_from_positiveTime_core
```

The proof order should be:

1. integrand-level rewrite,
2. translated-factor / parameter rewrite,
3. apply the repaired base theorem `bvt_cluster_positiveTime_singleSplit_core`
   — and only that base-file export, not the legacy `:2514` theorem directly,
4. package those rewrites plus that application as
   `singleSplit_core_rewrites_to_canonical_shell`,
5. use `canonical_shell_limit_of_rewrite` to transport the shell statement to
   the public eventual/limit statement in the explicit suborder
   positive-real identification
   -> right-half-plane uniqueness when needed
   -> final Wightman-target `t → 0+` transport, using only the checked generic
   scalar holomorphic / `t → 0+` transport surfaces imported from
   `OSToWightmanBoundaryValueLimits.lean`,
6. finish by packaging the result as
   `bvt_cluster_canonical_from_positiveTime_core`,
7. feed the final checked private wrapper only through that thin public adapter,
   so the frontier remains visibly
   `canonical_shell_limit_of_rewrite`
   -> `bvt_cluster_canonical_from_positiveTime_core`
   -> `:398 :: private bvt_F_clusterCanonicalEventually_translate`.

That is why this adapter is a wrapper package and not a new analytic theorem.
If the later Lean proof starts introducing contour or boundary-value arguments
here, it has drifted below the current documentation standard.

## 12.5. Exact hidden normalization identities

The theorem-4 doc should also make explicit the small identities that are easy
to suppress in prose but will matter in the later Lean file.

File-ownership note: these normalization lemmas should live beside the
one-factor transport package in `OSToWightmanPositivity.lean` unless that file
is explicitly split further. They are theorem-3-consumer bookkeeping for the
transport comparison, not final-wrapper lemmas for `BoundaryValues.lean`.

The normalized degree-zero vector only extracts the desired one-factor theorem
if all of the following are written down as explicit lemmas:

```lean
lemma conjTensorProduct_degreeZeroUnit_eq
    (f : SchwartzNPoint d n) :
    f.conjTensorProduct degreeZeroUnit = cast_to_degree_n f

lemma osConjTensorProduct_degreeZeroUnit_eq
    (f : SchwartzNPoint d n) :
    f.osConjTensorProduct degreeZeroUnit = cast_to_zeroDiagonal_degree_n f.osConj

lemma ZeroDiagonalSchwartz_ofClassical_degreeZeroUnit_eq
    (f : SchwartzNPoint d n) :
    ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct degreeZeroUnit) =
      ZeroDiagonalSchwartz.ofClassical f.osConj
```

The exact coercions/casts above may change in the later implementation, but the
semantic content must not be left implicit:

1. tensoring on the right by the normalized degree-zero unit does not change
   the left factor,
2. the same is true on the OS-conjugated side,
3. the zero-diagonal wrapper does not introduce an extra normalization
   constant.

### 12.5.1. Why these identities matter

Without them, the later port can still prove an equality of inner products, but
it may fail to extract the exact theorem-4 one-factor statement because of
hidden degree-zero casts or scalar constants. The documentation should therefore
force these normalization lemmas to exist under their own names.

### 12.5.2. Estimated Lean size

This hidden-normalization package should be small but explicit:

1. degree-zero unit definition:
   `5-15` lines.
2. two tensor-product normalization lemmas:
   `10-25` lines each.
3. zero-diagonal wrapper lemma:
   `10-20` lines.

So the normalization subpackage should be expected to cost another
`35-85` lines, and that cost should remain visible in the theorem-4 docs.
