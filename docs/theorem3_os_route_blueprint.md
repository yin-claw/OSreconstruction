# Theorem 3 OS-Route Blueprint

Purpose: this note is the implementation blueprint for the live `E -> R`
frontier theorem

- `OSToWightmanBoundaryValues.lean`, private theorem `bvt_W_positive`.

This document is not a historical summary. It is the route specification to be
followed during Lean work. If the code seems to suggest a different route, the
docs must be repaired first and Lean work must pause.

This note should be read together with:

- `docs/os1_detailed_proof_audit.md`
- `docs/os2_detailed_proof_audit.md`
- `docs/mathlib_gap_analysis.md`
- `docs/sorry_triage.md`

## 1. The live theorem and the current production situation

The live theorem is:

```lean
private theorem bvt_W_positive
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ F : BorchersSequence d,
      0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F F).re
```

The current production files still expose an older reduction chain through
boundary-ray / Schwinger / compact-approximation consumer interfaces. Those
surfaces are part of the current code graph, but they are **not** the theorem-3
blueprint any more. They are legacy consumers.

The theorem-3 blueprint now has exactly one endorsed route:

1. keep Packages A-B as valid one-variable support infrastructure;
2. do **not** use Package C / `hschw`, because that theorem surface is false;
3. build the OS I Section 4.3 transformed-image package:
   positive-time Euclidean data -> dense half-space transformed image ->
   OS Hilbert vector;
4. prove the quadratic identity on that transformed-image core, not on the same
   raw `BorchersSequence d` viewed on both sides;
5. extend positivity to arbitrary `BorchersSequence d` only afterwards, by the
   density/continuity closure supplied by the Section 4.3 image theorem.

That is the route Claude directed in `agents_chat.md`, and it is now the only
route this document endorses.

Implementation discipline:

1. the legacy `hschw` consumer interface may remain in production as deprecated
   dead-end infrastructure, but it is not an endorsed target theorem surface;
2. Package I is now the only endorsed theorem-3 closure route;
3. the old raw same-input theorem slogan for Package I is withdrawn;
4. if future work wants a different production endpoint than Package I, this
   blueprint must be rewritten first.

### 1.0. Mandatory documentation readiness gate

For this frontier, inability to close the live `bvt_W_positive` `sorry` is not
an invitation to add more production Lean scaffolding. It means this blueprint
is still missing mathematical proof detail.

Before any further blocker-facing Lean edit, the relevant subsection below must
state:

1. the exact theorem statement to implement;
2. the exact already-proved dependency names and files;
3. every hidden domain, support, compactness, integrability, Fourier-transform,
   and coercion obligation;
4. a proof transcript detailed enough that the Lean work is execution rather
   than route discovery;
5. the exact verification command for the touched file/module.

If any of those items is missing, pause production Lean and repair this
blueprint or the proof-audit docs first. Wrapper lemmas, conditional reducers,
residual limit algebra, and theorem-surface shuffling are forbidden in that
state unless the subsection explicitly identifies the lemma as a required
proof slot that directly discharges a named subgap.

### 1.1. Exact current local status on that route

The theorem-3 docs must distinguish three things:

1. what the route is in principle,
2. what is already implemented locally in production,
3. what exact theorem is still missing.

As of the current local branch state:

1. Package A is already implemented in
   `OSToWightmanPositivity.lean` as
   `identity_theorem_right_halfplane`;
2. Package B is already implemented there as
   `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single`;
3. Package C / `hschw` has now been settled as false at the exact theorem
   surface; see `agents_chat.md` Entries `#283`, `#285`, `#286`;
4. the later positive-time / compact-approximation consumers still exist in
   `OSToWightmanBoundaryValuesBase.lean`,
   `OSToWightmanBoundaryValuesCompactApprox.lean`, and
   `OSToWightmanBoundaryValues.lean`, but they are legacy consumers rather than
   endorsed theorem-3 route definitions;
5. the live theorem-3 frontier is now the corrected Package-I theorem surface;
6. the older raw theorem slogan
   `WightmanInnerProduct(bvt_W)(F,F).re = ‖u(F)‖^2` for the same raw
   `BorchersSequence d` on both sides is not endorsed and is under
   correction.

So the current frontier is not “find a theorem-3 route.” The route is fixed.
The current frontier is:

1. keep Packages A-B as valid support infrastructure,
2. stop treating Package C as a live theorem to prove,
3. repair Package I to the actual Section 4.3 transformed-image theorem
   surface,
4. only then implement the resulting transport / density / closure package.

### 1.2. Iteration B retraction (2026-04-07)

Between April 6 and April 7, 2026, branch `3b` briefly adopted "Option alpha"
(full Schwartz codomain via an internal Seeley extension) as the working
codomain choice for `os1TransportComponent`. A direct re-reading of the OS I
PDF on April 7, 2026, showed this is off-paper: OS I p. 95 Lemma 4.1 writes
the codomain as `L(R_+^{4n})`, i.e. the half-space Schwartz target, not the
full ambient Schwartz space.

Iteration B's Option alpha is therefore retracted, and the chosen codomain
reverts to **Option beta (quotient model of the half-space target)**.

This retraction implies:

1. the production docstring on `os1TransportComponent` should no longer claim
   the full-Schwartz / Seeley-extension route;
2. branch `3b` sub-CLM work should not spend time on a Seeley-extension stage;
3. the real branch-`3b` challenge remains the concrete partial-spatial-Fourier
   infrastructure, but now with the correct half-space codomain.

## 2. Exact existing theorem hooks already available

The current code already provides the main ingredients for the endorsed route.
The later Lean port should consume these exact theorem surfaces instead of
inventing new theorem shapes.

### 2.1. Holomorphic / boundary-value package

In `OSToWightmanBoundaryValueLimits.lean`:

- `bvt_singleSplit_xiShiftHolomorphicValue`
- `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue`
- `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`
- `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift`
- `bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq`
- `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger`
- `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_schwinger_eq_bvt_W_conjTensorProduct_timeShift`
- `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`

These theorems already package the one-variable holomorphic object attached to a
single/split pair and the relevant `z -> 0+` limit statements.

In `OSToWightmanPositivity.lean`:

- `identity_theorem_right_halfplane`
- `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single`

These are the current local production implementations of Packages A and B.
Note that the implemented Package-B theorem currently uses the simpler surface
`OSInnerProductTimeShiftHolomorphicValue` specialized to positive-time singles,
not the broader `...ExpandBoth` wrapper. That is fine and should be treated as
the canonical current production start point.

### 2.2. OS inner-product package

In `SchwingerOS.lean`:

- `PositiveTimeBorchersSequence`
- `PositiveTimeBorchersSequence.single`
- `PositiveTimeBorchersSequence.osInner`
- `PositiveTimeBorchersSequence.osInner_nonneg_self`
- `PositiveTimeBorchersSequence.osInner_eq_sum_right_singles`
- `OSInnerProduct_single_single`
- `OSInnerProduct_right_single`
- `OSInnerProduct_eq_sum_right_singles`
- `OSInnerProduct_zero_right`
- `OSInnerProduct_hermitian`

This is the OS-side algebraic package the theorem-3 proof should use.

### 2.3. Semigroup / time-shift package

In `OSToWightmanSemigroup.lean` and `OSToWightman.lean`:

- `OSInnerProductTimeShiftHolomorphicValue`
- `OSInnerProductTimeShiftHolomorphicValue_differentiableOn`
- `OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single`
- `OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_right_single`
- `OSInnerProductTimeShiftHolomorphicValueExpandBoth`
- `differentiableOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth`
- `continuousOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth`
- `OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_of_isCompactSupport`
- `OSInnerProductTimeShiftHolomorphicValueExpandBoth_single_eq_xiShift`
- `OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_piecewise_xiShift`

This is the OS-side holomorphic family to compare against
`bvt_singleSplit_xiShiftHolomorphicValue`.

### 2.4. Compact-approximation package

In `OSToWightmanBoundaryValuesCompactApprox.lean`:

- `compactApproxPositiveTimeBorchers`
- `compactApproxPositiveTimeBorchers_component_compact`
- `tendsto_compactApproxPositiveTimeBorchers_term`
- `tendsto_compactApproxPositiveTimeBorchers_wightmanInner_self`
- `bvt_wightmanInner_self_nonneg_of_compactApprox_timeShift_eq_osInner`
- `bvt_wightmanInner_self_nonneg_of_compactApprox_componentwise_ofReal_eq_bvt_W_conjTensorProduct_timeShift_of_hermitian`
- `bvt_wightmanInner_self_nonneg_of_compactApprox_componentwise_schwinger_eq_bvt_W_conjTensorProduct_timeShift_of_hermitian`

These theorems can still be used as **consumer interfaces** once the direct
positive-time semigroup bridge has been proved. They are not the route
definition.

### 2.5. Continuity package

In `OSToWightmanBoundaryValuesBase.lean` and nearby files:

- `bvt_W_continuous`
- `wightmanInner_eq_osInner_of_orderedPositive_termwise`
- `bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero`
- `bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_zero_right`
- `bvt_wightmanInner_self_nonneg_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_zero`
- finite-sum expansions of `WightmanInnerProduct`
- right-single and zero-right reduction lemmas

This is the continuity package already used by the legacy positive-time
consumer chain. It is no longer the endorsed final theorem-3 closure route.

## 3. What the OS papers require here

OS I and OS II both point to the same theorem shape:

1. identify the correct one-variable scalar holomorphic object;
2. prove equality of the Minkowski-side and OS-side scalar functions on the
   right half-plane from equality on positive reals;
3. take the `z -> 0+` limit to recover the boundary pairing identity;
4. use that scalar/boundary-value identity only inside the corrected Section
   4.3 transformed-image package, not as a same-input quadratic-form identity
   on `PositiveTimeBorchersSequence d`;
5. extend positivity to the full Borchers space by the Section 4.3 transport
   map and Hilbert-norm identity.

So the actual theorem-3 content is **not**:

- a contour-deformation theorem,
- a `K2VI1` comparison theorem,
- a new shell wrapper,
- or a raw algebraic-core theorem on `Submodule ℂ (BorchersSequence d)`.

The actual theorem-3 content is:

- positive-time semigroup identity,
- Section 4.3 transformed-image map to `OSHilbertSpace OS`,
- Hilbert-norm realization of the Wightman quadratic form on that transformed
  image, followed by density/continuity closure.

## 4. Route that is explicitly forbidden

The later Lean implementation must not drift back to any of the following:

1. `hpath` / contour-deformation / boundary-ray route.
2. `hschw` as the **target theorem shape**.
3. k=2-specific common-kernel transport as theorem-3 infrastructure.
4. defining `bvtInitialCore : Submodule ℂ (BorchersSequence d)`.
5. adding ad hoc `AddCommGroup`, `Module ℂ`, or topology instances to raw
   `BorchersSequence d` just to mimic paper notation.
6. inventing any new reduction theorem whose only purpose is to repackage the
   same positivity seam.

Historical note:

- the current production consumer theorem
  `bvt_positiveTime_self_nonneg_of_compactApprox_componentwise_schwinger_eq_bvt_W_conjTensorProduct_timeShift`
  may still be used after the positive-time semigroup bridge is proved;
- but the proof should **arrive** at that theorem from the positive-time
  semigroup route, not target `hschw` as the mathematical endpoint.

## 5. Corrected theorem package

The theorem-3 proof package should now be implemented in the following order.
This order is mathematical, not merely organizational.

### 5.1. Package A: one-variable identity theorem

The first theorem slot is:

```lean
theorem identity_theorem_right_halfplane
    (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.re})
    (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.re})
    (hagree : ∀ t : ℝ, 0 < t → f (t : ℂ) = g (t : ℂ)) :
    ∀ z : ℂ, 0 < z.re → f z = g z
```

This theorem is local complex analysis only. It should be proved once and then
reused.

Primary use in theorem 3:

- `f z = bvt_singleSplit_xiShiftHolomorphicValue ... z`
- `g z = OSInnerProductTimeShiftHolomorphicValue ... z`

### 5.2. Package B: compact positive-time single/split bridge

For compactly supported positive-time components, prove the direct one-variable
identity:

```lean
theorem bvt_singleSplit_eq_osTimeShift_on_rightHalfPlane
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hm : 0 < m) :
    ∀ z : ℂ, 0 < z.re →
      bvt_singleSplit_xiShiftHolomorphicValue (d := d) OS lgc hm
        f hf_ord hf_compact g hg_ord hg_compact z
        =
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) z
```

Proof transcript:

1. use
   `differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue`
   and
   `OSInnerProductTimeShiftHolomorphicValue_differentiableOn`;
2. use
   `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift`
   for the Wightman-side real-axis formula;
3. use
   `OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_right_single`
   specialized to a positive-time single left factor, or equivalently
   the already implemented production theorem
   `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single`;
4. check that both real-axis formulas equal the same positive-real Schwinger
   time-shift expression;
5. apply `identity_theorem_right_halfplane`.

This is the core analytic theorem. Everything after this is algebra and
continuity.

Exact current implementation note:

1. the current local production theorem for Package B is already
   `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single` in
   `OSToWightmanPositivity.lean`;
2. later work should build on that theorem, not reprove Package B under a
   slightly different wrapper unless there is a compelling API reason.

### 5.3. Package C: false legacy theorem surface

Package C is **not** a live frontier any more. It is the old positive-real
same-shell theorem surface externalized as `hschw`, and it is mathematically
false.

The legacy theorem surface was:

```lean
theorem schwinger_timeShift_eq_bvt_W_conjTensorProduct_timeShift_of_compact_positiveTime
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hm : 0 < m) :
    ∀ t : ℝ, 0 < t →
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)))
        =
      bvt_W OS lgc (n + m)
        (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))
```

This is the exact theorem externalized today as the hypothesis `hschw` in
`OSToWightmanBoundaryValueLimits.lean` and
`OSToWightmanBoundaryValuesCompactApprox.lean`.

Exact reason it is false:

1. for the free scalar field, the left-hand side evaluates to a Euclidean/OS
   Laplace-type quantity with factor `e^{-ω_p t}`;
2. the right-hand side evaluates to the reconstructed Wightman boundary-value
   pairing against a real Minkowski time translation, with oscillatory factor
   `e^{-i ω_p t}`;
3. the test functions also appear through different transforms on the two
   sides: Laplace on the OS side, Fourier on the Wightman side;
4. so the two sides do not agree on the exact intended theorem surface.

See `agents_chat.md` Entry `#283` for the exact free-field counterexample and
Entries `#285`-`#286` for the exact-surface verification against the repo
definitions.

Operational consequence:

1. the legacy `hschw` theorems may remain in production as logically valid
   implications from a false premise;
2. they should be marked deprecated/dead-end and not used to guide theorem-3
   proof work;
3. Package I is now the only endorsed theorem-3 route.

### 5.3.1. Existing theorem inventory still relevant after the correction

Existing production infrastructure already supporting this route:

1. `identity_theorem_right_halfplane` in `OSToWightmanPositivity.lean`;
2. `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single` in
   `OSToWightmanPositivity.lean`;
3. `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift` in
   `OSToWightmanBoundaryValueLimits.lean`;
4. `OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag`
   in `OSToWightmanSemigroup.lean`;
5. `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger`
   and
   `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_schwinger_eq_bvt_W_conjTensorProduct_timeShift`
   in `OSToWightmanBoundaryValueLimits.lean`.

Core Wightman-side boundary-value infrastructure already present:

1. `full_analytic_continuation_boundaryValueData`;
2. `boundary_values_tempered`;
3. `bvt_W`;
4. `bvt_F`;
5. `bvt_W_continuous`;
6. `bvt_W_linear`;
7. `bvt_F_holomorphic`;
8. `bvt_boundary_values`.

These are important because the Package-C spectral/Laplace strategy does not
only need the OS-side semigroup object; it also needs the exact theorem surfaces
that realize the reconstructed Wightman pairing as the boundary value of the
forward-tube witness `bvt_F`.

Particularly relevant BV-side spectral/Laplace bridge theorems already in
`OSToWightmanBoundaryValuesBase.lean`:

1. `bvt_selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_xiShift`;
2. `bvt_selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_xiShift_translate_spatial_right`;
3. `bvt_OSInnerProductTimeShiftHolomorphicValue_onePoint_pair_eq_xiShift_centerShear_local`;
4. `bvt_OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single_translate_spatial_right`.

These remain useful as support infrastructure for the corrected Section 4.3
transport-map route, but they should no longer be read as evidence that the old
same-shell Package-C theorem is true.

Useful transcript guides from older support files:

1. `schwinger_simpleTensor_timeShift_eq_xiShift`;
2. `OSInnerProductTimeShiftHolomorphicValueExpandBoth_single_eq_xiShift`;
3. `OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_piecewise_xiShift`.

These older theorems are valuable because they already write out the OS-side
positive-real / Euclidean-`xiShift` conversion in detail. They should be used
as proof transcripts, not as reasons to revert to an off-blueprint theorem
surface.

Zero-right and helper transport facts:

1. `bvt_eq_schwinger_of_tendsto_singleSplit_xiShift_nhdsWithin_zero_zeroRight_of_hermitian`
   still handles the `m = 0` repair only;
2. `boundary_ray_hermitian_pairing_of_F_negCanonical`,
   `bv_hermiticity_transfer_of_F_reflect`,
   `bv_timeReversal_transfer`,
   `boundary_ray_timeReversal_pairing_of_F_timeReversalCanonical`,
   and `tendsto_boundary_negReverse_pairing`
   remain helper transport theorems only.

They may assist a future proof, but they are not themselves the OS I Section 4.3
Fourier-Laplace mechanism.

### 5.3.2. What this correction means for the codebase

1. do not spend any further theorem-3 effort trying to prove the old
   `schwinger_timeShift_eq_bvt_W_conjTensorProduct_timeShift` surface;
2. do not revive a same-shell bridge
   `bvt_W (f.conjTensorProduct g) = OS.S (f.osConjTensorProduct g)`;
3. keep Packages A-B as valid support lemmas;
4. treat the current `hschw` consumer theorems as deprecated legacy
   infrastructure only;
5. move directly to Package I.

Exact current handoff theorems after the correction:

1. the `hschw`-consuming compact-approximation theorems remain compiled legacy
   infrastructure but are no longer part of the endorsed route;
2. the live theorem-3 implementation target remains Package I, with the
   current sub-blocker being the canonical shell-to-Laplace identification in
   §5.9.4a.1.ε before the separate Section-4.3 `hH_imag_os` identification;
3. the older theorems
   `bvt_wightmanInner_single_single_eq_osInner_of_tendsto_singleSplit_xiShift_nhdsWithin_zero`
   and
   `bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero`
   remain legacy consumers only and should not drive new theorem-3 production.

### 5.4. Package D: withdrawn raw positive-time sesquilinear route

The theorem surface

```lean
WightmanInnerProduct d (bvt_W OS lgc)
  (F : BorchersSequence d) (G : BorchersSequence d)
  =
OSInnerProduct d OS.S
  (F : BorchersSequence d) (G : BorchersSequence d)
```

for raw `F G : PositiveTimeBorchersSequence d` is **false** and must not be
implemented.

Reason:

1. the Wightman side uses the Borchers/Fourier involution through
   `conjTensorProduct`;
2. the OS side uses the Euclidean/Laplace involution through
   `osConjTensorProduct`;
3. these are not the same quantity even at `t = 0`;
4. therefore summing the single/split bridge theorems does **not** produce a
   same-input sesquilinear identity on the positive-time class.

Consequences:

1. `bvt_wightmanInner_eq_osInner_of_positiveTime` is withdrawn as a theorem
   target;
2. the legacy consumer theorems that look like positive-time `osInner`
   comparisons remain compiled only as historical infrastructure and should not
   drive any new theorem-3 production;
3. the corrected route moves directly from the single/split bridge to the
   Section 4.3 transformed-image / transport package.

### 5.5. Package E: withdrawn raw positive-time positivity route

The theorem surface

```lean
0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
  (F : BorchersSequence d) (F : BorchersSequence d)).re
```

for raw `F : PositiveTimeBorchersSequence d` should **not** be pursued by
rewriting to `OSInnerProduct` on the same literal input. That route depends on
the false Package-D identity and is therefore quarantined together with it.

What remains true is only:

1. some existing compiled theorems still consume old Package-D-style inputs;
2. they may remain in the codebase as deprecated legacy consumers;
3. they are not part of the endorsed theorem-3 proof route.

The analytic core now passes straight from the single/split bridge to Package I.

### 5.6. Package F: ordered-positive-time density in each degree

Important route correction:

The naive raw-density slogan

```lean
Dense {f : SchwartzNPoint d n |
  tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n}
```

is not mathematically correct on the full Schwartz space. If
`x ∉ OrderedPositiveTimeRegion d n`, then point evaluation `f ↦ f x` is a
continuous linear functional and it vanishes on every function whose support is
contained in `OrderedPositiveTimeRegion d n`. So that set cannot be dense in
all of `SchwartzNPoint d n`.

Therefore the raw theorem surface originally written in this section is
quarantined and must not be implemented as stated.

This means the older density route is withdrawn, not merely awaiting repair.
The later Lean implementation should not start from a global topology on raw
`BorchersSequence d`, and it should not attempt to resurrect Package F as a
real theorem on full Schwartz space.

Quarantined theorem slots (recorded here only so later work does not
accidentally reintroduce them as if they were valid):

```lean
theorem orderedPositiveTime_dense_schwartzNPoint
    (n : ℕ) :
    Dense
      {f : SchwartzNPoint d n |
        tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n}

theorem exists_orderedPositiveTime_seq_tendsto
    (n : ℕ) (f : SchwartzNPoint d n) :
    ∃ g : ℕ → SchwartzNPoint d n,
      (∀ k, tsupport (g k : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
        ∧ Tendsto g atTop (𝓝 f)
```

Exact current implementation status:

1. there is **no** current production theorem implementing Package F yet;
2. the existing family `compactApproxPositiveTimeBorchers` in
   `OSToWightmanSpatialMomentum.lean` is **not** Package F:
   it approximates an already positive-time Borchers sequence by compactly
   supported positive-time Borchers sequences, but it does not approximate an
   arbitrary Schwartz component by ordered-positive-time data;
3. this section is retained only as a warning / historical quarantine, not as
   endorsed implementation guidance.

### 5.7. Package G: componentwise positive-time approximation of Borchers sequences

The original Package-G statement depended on the quarantined raw Package-F
statement above. So this section is also historical only, not a currently
endorsed theorem surface.

Recommended theorem slot:

```lean
theorem exists_positiveTime_componentwise_approximation
    (F : BorchersSequence d) :
    ∃ G : ℕ → PositiveTimeBorchersSequence d,
      (∀ n, Tendsto (fun k => ((G k : BorchersSequence d).funcs n)) atTop (𝓝 (F.funcs n)))
        ∧ (∀ k, (G k : BorchersSequence d).bound = F.bound)
```

What remains fixed is only the negative guidance:

1. do not force a raw topological structure on `BorchersSequence d`;
2. do not reintroduce raw support-density claims on full Schwartz space;
3. use Package I instead of trying to revive this approximation route.

Exact current implementation status:

1. there is **no** current production theorem implementing Package G, and none
   is currently endorsed;
2. `compactApproxPositiveTimeBorchers` should be treated only as an internal
   compact-support approximation inside the positive-time class;
3. it is not the final arbitrary-`BorchersSequence` approximation theorem and
   should not be documented or used as if it were.

### 5.8. Package H: withdrawn continuity-after-density route

This section records the old continuity-after-density plan only so it is not
accidentally revived as current blueprint guidance.

Recommended theorem slots:

```lean
theorem WightmanInnerProduct_tendsto_of_componentwise_tendsto
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d)
    (G : ℕ → BorchersSequence d)
    (hbound : ∀ k, (G k).bound = F.bound)
    (hcomp : ∀ n, Tendsto (fun k => (G k).funcs n) atTop (𝓝 (F.funcs n))) :
    Tendsto
      (fun k => WightmanInnerProduct d (bvt_W OS lgc) (G k) (G k))
      atTop
      (𝓝 (WightmanInnerProduct d (bvt_W OS lgc) F F))

theorem re_WightmanInnerProduct_tendsto_of_componentwise_tendsto
    ...
```

Proof transcript:

1. expand `WightmanInnerProduct` as a finite double sum up to `F.bound`;
2. for each fixed pair `(n,m)`, use `bvt_W_continuous` and the product
   convergence of the component approximants;
3. move the limit through the finite sum.

This is where the route uses the finite-support nature of `BorchersSequence d`
instead of forcing a global topological structure.

Acceptable implementation helper:

1. if the eventual Lean code wants a helper theorem phrased as continuity of
   the real quadratic form on a **fixed-bound product space**
   `(n : Fin (B + 1)) → SchwartzNPoint d n`, that is acceptable;
2. such a theorem is still only a repackaging of the finite-sum argument above,
   because the bound `B` is fixed and the quadratic form expands to a finite
   double sum of already-continuous pairings;
3. what should still be avoided is restarting theorem 3 from a new global
   topological structure on raw `BorchersSequence d` itself.

Exact current implementation status:

1. the repo already contains a concrete model of this continuity argument for
   one specific approximation family:
   `tendsto_compactApproxPositiveTimeBorchers_term` and
   `tendsto_compactApproxPositiveTimeBorchers_wightmanInner_self` in
   `OSToWightmanBoundaryValuesCompactApprox.lean`;
2. these theorems show that the finite-sum continuity route is formally viable
   on the current encoding of `BorchersSequence d`;
3. however, they are still only special-case continuity theorems for the
   compact-support truncation family, not the final general Package-H theorem.

### 5.9. Package I: final public closure via the OS I Section 4.3 transformed-image package

After the density-route correction, the final theorem-3 closure package is no
longer the withdrawn raw positive-time approximation theorem. But it is also
not the naive raw theorem

`(WightmanInnerProduct d (bvt_W OS lgc) F F).re = ‖u(F)‖ ^ 2`

for the same raw `BorchersSequence d` on both sides.

OS I Section 4.3 itself first constructs a dense transformed image `L` of
positive-time Euclidean test functions inside the half-space Schwartz target
`L(R_+^{4n})` on the Minkowski side (Lemma 4.1), then defines `u` on that
image (Eq. (4.27)), and then proves the quadratic identity there
(Eq. (4.28)). Only afterwards does one recover the full public positivity
statement by density/continuity.

Just as importantly, the naive same-test-function identity is false even at
`t = 0`: one must transport Euclidean test functions on the Laplace side to the
positive-energy Minkowski test-function side before the Wightman quadratic form
matches the OS Hilbert norm.

So the old raw theorem slots are withdrawn. The corrected theorem slots are:

```lean
/-- The degree-`n` positive-time Euclidean domain used in OS I Section 4.3.

This is the paper's `S_+(ℝ^{4n})`: Schwartz `n`-point test functions whose
topological support lies in the ordered positive-time region. If the eventual
Lean implementation prefers an equivalent `Submodule ℂ (SchwartzNPoint d n)`
presentation rather than a subtype, that is acceptable, but it must represent
the same paper domain. -/
def EuclideanPositiveTimeComponent (d n : ℕ) [NeZero d] :=
  {f : SchwartzNPoint d n //
    tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n}

/-- The degree-`n` Section 4.3 positive-energy codomain.

This is **not** the support-restricted subtype
`{f : SchwartzNPoint d n // tsupport f ⊆ PositiveEnergyRegion}`.
It is also **not** the full ambient `SchwartzNPoint d n` equipped with a
false `DenseRange` claim.

The correct theorem surface is the paper's half-space Schwartz target
`L(R_+^{4n})`, implemented in production by the quotient model
`SchwartzNPoint d n ⧸ {f | f = 0 on section43PositiveEnergyRegion}`. The
current blueprint no longer endorses either:
- the false support-restricted subtype
  `{f : SchwartzNPoint d n // tsupport f ⊆ PositiveEnergyRegion}`, or
- a fixed global Seeley-extension choice landing in full ambient
  `SchwartzNPoint d n`.
-/
def Section43PositiveEnergyComponent (d n : ℕ) [NeZero d] := ...

/-- The degree-`n` Section 4.3 Fourier-Laplace transport
(OS I (4.19)-(4.20)) landing in the corrected half-space codomain. -/
noncomputable def os1TransportComponent
    (d n : ℕ) [NeZero d] :
    EuclideanPositiveTimeComponent d n →L[ℂ] Section43PositiveEnergyComponent d n

/-- The degree-`n` Section 4.3 transformed image. -/
def bvtTransportImage (d n : ℕ) [NeZero d] :
    Set (Section43PositiveEnergyComponent d n) :=
  Set.range (os1TransportComponent d n)

/-- Additive closure of the Section 4.3 image. -/
theorem bvtTransportImage_add
    {n : ℕ} {f g : Section43PositiveEnergyComponent d n} :
    f ∈ bvtTransportImage (d := d) n →
    g ∈ bvtTransportImage (d := d) n →
    f + g ∈ bvtTransportImage (d := d) n

/-- Scalar closure of the Section 4.3 image. -/
theorem bvtTransportImage_smul
    {n : ℕ} {c : ℂ} {f : Section43PositiveEnergyComponent d n} :
    f ∈ bvtTransportImage (d := d) n →
    c • f ∈ bvtTransportImage (d := d) n

/-- For positive degree, the current support-restricted Section 4.3 source is
not dense in the half-space quotient codomain. Degree `0` is exceptional: the
source already is the full ambient Schwartz space there. The honest
quotient-side dense map is the ambient Schwartz quotient map, not
`os1TransportComponent` itself. -/
theorem not_denseRange_os1TransportComponent_succ
    (n : ℕ) :
    ¬ DenseRange (os1TransportComponent d (n + 1))

/-- Finite Borchers data whose every component lies in the Section 4.3 image. -/
structure BvtTransportImageSequence (d : ℕ) [NeZero d] where
  toBorchers : BorchersSequence d
  image_mem : ∀ n,
    section43PositiveEnergyQuotientMap (d := d) n (toBorchers.funcs n) ∈
      bvtTransportImage (d := d) n

/-- The OS I Section 4.3 transport map on the transformed-image core. -/
noncomputable def bvt_transport_to_osHilbert_onImage
    (OS : OsterwalderSchraderAxioms d) :
    BvtTransportImageSequence d → OSHilbertSpace OS

/-- The transport map is independent of the Section 4.3 preimage choice. -/
theorem bvt_transport_to_osHilbert_onImage_wellDefined
    (OS : OsterwalderSchraderAxioms d)
    (F : BvtTransportImageSequence d) :
    ...

/-- Additivity on the transformed-image core. -/
theorem bvt_transport_to_osHilbert_onImage_add
    (OS : OsterwalderSchraderAxioms d)
    (F G : BvtTransportImageSequence d) :
    bvt_transport_to_osHilbert_onImage (d := d) OS (F + G) =
      bvt_transport_to_osHilbert_onImage (d := d) OS F +
      bvt_transport_to_osHilbert_onImage (d := d) OS G

/-- Complex-linearity on the transformed-image core. -/
theorem bvt_transport_to_osHilbert_onImage_smul
    (OS : OsterwalderSchraderAxioms d)
    (c : ℂ) (F : BvtTransportImageSequence d) :
    bvt_transport_to_osHilbert_onImage (d := d) OS (c • F) =
      c • bvt_transport_to_osHilbert_onImage (d := d) OS F

/-- Stage-5 prerequisite: multivariate quotient descent for the explicit
Section-4.3 Fourier-Laplace transform.

This is the multivariate analog of
`fourierPairingDescendsToSection43PositiveEnergy1D_partialFourierSpatial_timeSlice`.
It should identify the abstract quotient-valued transform
`os1TransportComponent` with the concrete iterated `partialFourierSpatial_fun`
/ `complexLaplaceTransform` / `fourierLaplaceExt` computation degreewise. -/
theorem section43_iteratedSlice_descendedPairing
    (n : ℕ) (f : EuclideanPositiveTimeComponent d n) :
    ... := by
  ...

Exact current-code milestone:
- the full slice-descent theorem is now formalized as the private theorem
  `section43_iteratedSlice_descendedPairing` in
  [OSToWightmanPositivity.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean);
- the earlier theorem `section43_iteratedSlice_descendedPairing_imagAxis`
  remains as the first concrete fragment, but it is no longer the live
  milestone;
- the reusable one-variable interchange step is now formalized privately as
  `one_variable_time_interchange_for_wightman_pairing`, together with the
  kernel-reduction chain down to an ambient upper-half-plane witness, in
  [OSToWightmanPositivity.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean);
- `OSToWightmanPositivity.lean` is now `sorry`-free; the active public
  theorem-3 `sorry` remains `bvt_W_positive` in
  [OSToWightmanBoundaryValues.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean);
- the slice-side vanishing package is now formalized on both pairing
  orientations, including
  `fourierInvPairingCLM_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport`
  and
  `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport`
  in
  [OSToWightmanPositivity.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean);
- the flattened spectral / dual-cone package is now closed in
  [OSToWightmanBoundaryValueLimits.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean),
  culminating in
  `bvt_W_conjTensorProduct_timeShift_hasPaleyWienerExtension_of_flattened`;
- the next honest Stage-5 blocker is therefore the actual witness-consuming
  seam: the ambient upper-half-plane witness has now been canonicalized as an
  explicit `fourierLaplaceExt` of the real-time Wightman pairing functional,
  with a concrete imaginary-axis formula; the remaining work is to identify
  those values with the semigroup-side holomorphic matrix element (spectral
  Laplace comparison), together with the canonical-shell boundary-value limit
  into those same witness values;
- the concrete Section-4.3 / Lemma-4.2 adapter
  `lemma42_matrix_element_time_interchange` and the transformed-image kernel
  theorem `bvt_W_matrixElement_onImage` remain the public theorem slots that
  consume that witness, not the immediate next step from slice descent alone;
- `lemma42_matrix_element_time_interchange` is now present in
  [OSToWightmanPositivity.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean)
  on the honest witness-consuming surface: it already turns the positive-
  imaginary-axis witness identification plus the canonical-shell limit theorem
  into the desired per-pair kernel equality, so the remaining exposed blocker
  is exactly the proof of those witness/limit hypotheses rather than another
  hidden reduction layer.

/-- Concrete Section-4.3 / Lemma-4.2 adapter: this theorem is now landed on the
current honest theorem surface. It consumes:
- an upper-half-plane witness `H`,
- identification of `H` with the semigroup-side holomorphic matrix element on
  the positive imaginary axis,
- and the canonical-shell boundary-value limit into those same witness values.

What remains is to prove those hypotheses from the spatial-Fourier / Section-8
machinery, not to invent another reduction theorem. -/
theorem lemma42_matrix_element_time_interchange
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (H : ℂ → ℂ)
    ... :
    ... := by
  -- implemented in `OSToWightmanPositivity.lean`

/-- Stage-5 prerequisite: expose the OS-II `bvt_W` quadratic form on
transformed-image inputs in the same iterated Fourier-Laplace coordinates used
by `section43_iteratedSlice_descendedPairing`, now consuming the concrete
adapter `lemma42_matrix_element_time_interchange`. -/
theorem bvt_W_matrixElement_onImage
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d)
    {n m : ℕ}
    (hn : n ≤ F.toBorchers.bound)
    (hm : m ≤ F.toBorchers.bound) :
    ... := by
  ...

/-- OS I Eq. (4.28) on the transformed-image core. -/
theorem bvt_wightmanInner_eq_transport_norm_sq_onImage
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d) :
    (WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers F.toBorchers).re =
      ‖bvt_transport_to_osHilbert_onImage (d := d) OS F‖ ^ 2

/-- Final public theorem-3 closure from the transformed image core. The closure
step uses density in the Hilbert space `H`, not a Schwartz-space density
theorem. -/
theorem bvt_W_positive_of_transportImage_density
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ F : BorchersSequence d,
      0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F F).re
```

### 5.9.0. Codomain decision: Option beta

For theorem 3, the codomain choice is now fixed:

1. the paper's Lemma 4.1 codomain is `L(R_+^{4n})`, the half-space Schwartz
   space;
2. the blueprint therefore fixes **Option beta**:
   `Section43PositiveEnergyComponent d n` is a quotient-model realization of
   that half-space Schwartz target;
3. the full-Schwartz / internal-Seeley-extension route from Iteration B is
   retracted and should not be implemented;
4. any later equivalent coding of this codomain must remain definitionally
   about functions on the half-space, not about a fixed extension to all of
   `ℝ^{4n}`.

Proof transcript:

1. define the degreewise transformed image `bvtTransportImage` exactly as in OS
   I Lemma 4.1, i.e. literally as the range of
   `os1TransportComponent d n`;
2. do **not** implement `os1TransportComponent` as the naive unrestricted
   real-axis Laplace integral by itself; the paper route factors through the
   intermediate `(4.19)` space and Lemma 8.2, and that is exactly what keeps
   the codomain on the genuine half-space Schwartz theorem surface rather than
   drifting either to a tempered-only theorem surface or to the false
   support-restricted codomain `tsupport ⊆ PositiveEnergyRegion`;
3. derive additive/scalar closure of the image from linearity of
   `os1TransportComponent`;
4. package finite-support sequences in that image as
   `BvtTransportImageSequence d`;
5. define `bvt_transport_to_osHilbert_onImage` by the Section 4.3 preimage map
   followed by the existing OS Hilbert-space construction;
6. prove preimage-independence / well-definedness using the zero-kernel part of
   OS I Lemma 4.1;
7. prove the multivariate iterated-slice descended-pairing theorem that
   identifies the abstract quotient-valued transform with the concrete
   iterated `partialFourierSpatial_fun` / Fourier-Laplace computation;
8. prove the matching `bvt_W` matrix-element bridge on transformed-image
   inputs, in the same iterated coordinates;
9. prove `bvt_wightmanInner_eq_transport_norm_sq_onImage` by matching the
   Wightman and transport double sums termwise through those two Stage-5
   prerequisites;
10. use the already-built density of positive-time vectors in `OSHilbertSpace OS`
   coming from the completion/GNS construction, not a separate density theorem
   in Schwartz space;
11. extend positivity from the transported image to arbitrary public
   `BorchersSequence d` by the resulting Hilbert-space closure plus continuity
   of `bvt_W`.

This package is the actual theorem-3 closure target.

OS I / OS II dependency note:

1. in the original paper, Eqs. (4.24)-(4.28) consume the distribution
   `\tilde W` from Eq. (4.12), so Section 4.3 is not literally independent of
   Lemma 8.8;
2. the production route must not rely on the broken OS I Lemma 8.8 itself;
3. instead, the Wightman-side kernel is supplied by the already-repaired OS II
   `bvt_F` / `bvt_W` construction built from `OSLinearGrowthCondition`;
4. the explicit Fourier-Laplace integral `(4.19)-(4.20)` still governs the
   **test-function transport** on the Section-4.3 side.

### 5.9.1. Detailed proof of `os1TransportComponent`

The production definition of

`os1TransportComponent :
  EuclideanPositiveTimeComponent d n ->L[ℂ] Section43PositiveEnergyComponent d n`

must follow the Section-4.3 paper route exactly.

Input:
- `f ∈ S_+(ℝ^{(d+1)n})`, i.e. a Schwartz test function supported in ordered
  positive Euclidean times.

Output:
- an element of the corrected Section-4.3 positive-energy codomain, i.e. the
  half-space Schwartz object determined by the Fourier-Laplace transform.

The proof must be decomposed into the following local steps.

1. Separate spatial and time transforms.
   - first apply the ordinary Schwartz Fourier transform in the spatial
     variables;
   - then apply the one-sided Laplace transform in each Euclidean time
     variable, with the sign convention of OS I `(4.19)`-`(4.20)`;
   - only after those one-variable time transforms are assembled may one regard
     the result as a function of full momentum variables `q_k = (q_k^0, q⃗_k)`.

2. Factor the implementation through a degreewise one-variable supplier.
   The production file should not define `os1TransportComponent` directly by one
   giant `n`-variable integral. The correct local supplier package is:

   ```lean
   noncomputable def os1TransportOneVar
       : EuclideanPositiveTimeTest1D →L[ℂ] Section43PositiveEnergy1D

   theorem os1TransportOneVar_restrict_Ici_eq
       (f : EuclideanPositiveTimeTest1D) :
       ...

   theorem os1TransportOneVar_injective :
       Function.Injective os1TransportOneVar

    theorem not_denseRange_os1TransportOneVar :
        ¬ DenseRange os1TransportOneVar

    theorem denseRange_section43PositiveEnergyQuotientMap1D :
        DenseRange section43PositiveEnergyQuotientMap1D
   ```

3. The exact analytic suppliers for that one-variable package are:
   - `SCV.fourierLaplaceExt`,
   - `SCV.paley_wiener_half_line`,
   - `SchwartzMap.fourierTransformCLM`,
   - the fact that Fourier transform is an automorphism of Schwartz space.

4. The mathematical use of those suppliers is:
   - the positive-time support of the Euclidean input gives one-sided Fourier
     support for the relevant time-distribution slices;
   - `SCV.paley_wiener_half_line` gives the corresponding upper-half-plane
     Fourier-Laplace representation;
   - the half-line Paley-Wiener theorem identifies the resulting object with a
     point in the corrected Section-4.3 codomain;
   - the boundary-value uniqueness part of that theorem gives the kernel-zero
     statement after restricting back to the half-line;
   - Fourier automorphism of Schwartz keeps the target on the half-space
     Schwartz side rather than only a tempered-distribution target.

5. The concrete current-code branch `3b` should be built through a companion
   support file, not monolithically inside the frontier theorem file.
   The intended support chain is:
   - `OSReconstruction/SCV/PartialFourierSpatial.lean`,
   - `nPointTimeSpatialCLE`,
   - `partialFourierSpatial_fun`,
   - differentiation-under-the-integral and seminorm bounds there,
   - then the resulting CLM imported back into `OSToWightmanPositivity.lean`.

6. Step 1 of that branch-`3b` implementation must keep the paper's transform
   explicit: `(4.19)`-`(4.20)` define `\check f` by a concrete
   Fourier-Laplace integral on test functions. It is **not** a spectral-measure
   definition.

7. Assemble the degree-`n` map by repeated one-variable transforms.
   - the production proof should introduce a theorem saying the full `n`-point
     transform is the iterated composition of the one-variable operator in each
     time coordinate together with the spatial Fourier transform;
   - this is the place where tensor-product / iterated-variable bookkeeping
     belongs;
   - no many-variable Paley-Wiener theorem is used here.

8. Package continuity and codomain characterization only after the iterated
   formula is proved.
   - continuity is obtained because each elementary one-variable transform is a
     continuous linear map on the chosen Schwartz model;
   - the essential codomain theorem is that the resulting element of the
     corrected Section-4.3 codomain agrees with the Fourier-Laplace transform
     prescribed by Section 4.3;
   - the final CLM to that codomain is defined only after those two facts are
     in place.

The implementation should therefore introduce the following local theorem slots
before the final `def` is closed:

```lean
theorem os1TransportComponent_eq_iterated_oneVar
    (f : EuclideanPositiveTimeComponent d n) :
    ...

theorem os1TransportComponent_restrict_positiveEnergy
    (f : EuclideanPositiveTimeComponent d n) :
    ...

theorem os1TransportComponent_continuous :
    Continuous (os1TransportComponent d n)
```

### 5.9.2. Lemma 4.1 density: quotient-side theorem, not the live positivity blocker

The dense-image half of OS I Lemma 4.1 cannot be implemented on the current
support-restricted subtype source. Production now proves the one-variable
counterexample `not_denseRange_os1TransportOneVar`, and the same warning applies
to the literal multivariate subtype target.

What is settled:

1. `DenseRange (os1TransportComponent d (n + 1))` on the current
   `euclideanPositiveTimeSubmodule` source should not be used as a production
   theorem slot. Degree `0` is exceptional and not part of this negative
   theorem.
2. `DenseRange (os1TransportComponent d (n + 1))` in full
   `SchwartzNPoint d (n + 1)` is false and is withdrawn.
3. A fixed Seeley extension has closed range, so no proof should aim at dense
   range in the full ambient Schwartz space.
4. The honest quotient-side dense map is the ambient Schwartz quotient map
   `section43PositiveEnergyQuotientMap`, and production already has its
   one-variable and multivariate surjective/dense-range forms.
5. If Lemma 4.1 is later formalized faithfully, it must be stated on the
   actual half-space codomain `L(R_+^{4n})` from Section 4.3, not on the
   support-restricted subtype currently used for Euclidean inputs.
6. The positivity proof for theorem 3 does not need that Schwartz-density
   theorem as a live prerequisite. What it needs is:
   - the transport-map comparison on positive-time inputs,
   - density of the resulting vectors in the Hilbert space `H`,
   - continuity/closure on the `bvt_W` side.

So the current live route should not contain either
`os1TransportOneVar_denseRange` or `os1TransportComponent_denseRange` as
production targets. The only honest dense-range theorems now on this branch are
the quotient-side maps
`denseRange_section43PositiveEnergyQuotientMap1D` and
`denseRange_section43PositiveEnergyQuotientMap`.

The file should not attempt to prove `bvtTransportImage_dense` by separate
topological arguments. The positivity route should go through injectivity /
kernel-zero on the transport side and Hilbert-space density on the OS side.

### 5.9.3. Detailed proof of the on-image transport map

The Section-4.3 Hilbert transport is **not** a map on raw `BorchersSequence d`.
It is defined only on the transformed image.

The honest current-code package is:

1. represent the transformed-image core by a finite-support sequence whose
   degree-`n` raw Schwartz component becomes a transformed-image point after
   applying `section43PositiveEnergyQuotientMap (d := d) n`;
2. choose, for each degree, a Euclidean positive-time preimage;
3. map that preimage to the existing OS vector
   `euclideanPositiveTimeSingleVector`;
4. sum over the finite degree support in `OSHilbertSpace OS`.

That is why the correct current-code structure is:

```lean
structure BvtTransportImageSequence (d : ℕ) [NeZero d] where
  toBorchers : BorchersSequence d
  image_mem : ∀ n,
    section43PositiveEnergyQuotientMap (d := d) n (toBorchers.funcs n) ∈
      bvtTransportImage (d := d) n
```

The well-definedness proof must use `os1TransportComponent_eq_zero_iff`, not
density. The exact proof is:

1. suppose two Euclidean preimages give the same transformed-image element;
2. subtract them;
3. the difference maps to zero under `os1TransportComponent` after comparing
   both preimages to the same quotient class
   `section43PositiveEnergyQuotientMap (d := d) n (F.toBorchers.funcs n)`;
4. injectivity / kernel-zero gives equality of the preimages;
5. therefore the OS Hilbert vector does not depend on the choice.

### 5.9.4. Detailed proof of Eq. `(4.28)` on the image

The theorem

`bvt_wightmanInner_eq_transport_norm_sq_onImage`

must be proved first in the diagonal norm-square form. The polarized inner
product identity, if ever wanted later, is downstream and optional.

The proof transcript is:

1. start from a transformed-image sequence `F`;
2. choose degreewise Euclidean preimages `f_n` in the positive-time domain;
3. expand the Wightman quadratic form degreewise using the current public
   `WightmanInnerProduct`;
4. for each component pair, rewrite the Wightman pairing by the
   Section-4.3 / Lemma-4.2 Fourier-Laplace computation:
   - spatial Fourier transform is handled by the ordinary tempered
     distribution Fourier calculus already used elsewhere in the repo;
   - the first direct consumer of the slice-descent theorem is the concrete
     adapter `lemma42_matrix_element_time_interchange`;
   - the purely configuration-space shell inside that adapter is already
     formalized by `conjTensorProduct_timeShift_eq_tailTimeShift` and
   `simpleTensor_timeShift_integral_eq_xiShift_conj` in
   [OSToWightman.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightman.lean);
   - inside that adapter, the reusable Section-8 one-variable theorem is now
     already formalized privately as
     `one_variable_time_interchange_for_wightman_pairing` in
     [OSToWightmanPositivity.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean);
   - do not replace that one-variable step by a naive "the canonical
     `xiShift(wickRotate(y), t * I)` shell is already pointwise inside
     `ForwardTube` for every ambient `y`" argument: that statement is false on
     the corrected ambient theorem surface, because the `xiShift` updates only
     one time-difference coordinate and the remaining Wick-rotated differences
     need not lie in the forward cone;
   - in the current repo, the honest Lean supplier for that one-variable step
     should be routed through `SCV.paley_wiener_one_step` /
     `SCV.paley_wiener_half_line`, not a fresh ad hoc many-variable
     continuation theorem;
   - more precisely: `paley_wiener_half_line` first produces the **ambient**
     witness on `SCV.upperHalfPlane`, because it is a Fourier/Laplace theorem
     for a real-line tempered pairing; it does **not** directly hand us the
     final right-half-plane witness used by the semigroup-side
     `singleSplit_xiShift` comparison;
   - so the immediate post-Paley-Wiener theorem slot is an upper-half-plane
     witness/exact-boundary-value statement for the ambient Wightman pairing;
   - in the current repo, that route has already been reduced further to the
     closed flattened spectral package ending at
     `bvt_W_conjTensorProduct_timeShift_hasPaleyWienerExtension_of_flattened`
     in
     [OSToWightmanBoundaryValueLimits.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean);
   - so the remaining live content is no longer the paired-vanishing /
     one-sided-support theorem, but the witness-consuming seam itself:
     positive-imaginary-axis identification plus the canonical-shell limit
     theorem for the actual ambient upper-half-plane witness;
   - the first direct consumer of that witness only needs the values on the
     positive imaginary axis: if the canonical shell converges to `H(i t)` and
     `H(i t)` is identified with the semigroup-side holomorphic value, the
     current kernel reduction already closes;
   - only if one wants a whole-domain comparison of holomorphic witnesses does
     one then need the existing upper-half-plane identity theorem or an
     explicit rotation bridge before invoking any right-half-plane uniqueness
     statement;
   - the common kernel is the corrected OS-II-backed analytic-continuation
     object underlying `bvt_F` / `bvt_W`, not a fresh spectral-measure
     construction in Section 4.3 itself.
5. recognize the resulting degreewise finite sum as the Hilbert norm square of
   `bvt_transport_to_osHilbert_onImage`.

No theorem in this package should claim that the raw Wightman quadratic form on
the same literal test function equals the raw OS pairing. The comparison is
only true after transport through the Section-4.3 image.

### 5.9.4a. Current shell-to-Laplace frontier: proof-doc completion target

This subsection is the current gate for the OS-route positivity work. No more
production Lean should be added to the shell-to-Laplace seam until the theorem
slots in this subsection have been made exact and implementable.

Current production facts already available:

1. In
   [OSToWightmanPositivity.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean):
   `tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue`
   proves the explicit canonical `xiShift` shell has Wightman boundary-value
   limit
   `bvt_W OS lgc (n + m)
      (φ.conjTensorProduct (timeShiftSchwartzNPoint t ψ))`.
2. In
   [OSToWightmanBoundaryValueLimits.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean):
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension`,
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_eq_fourierLaplaceIntegral`,
   and
   `tendsto_bvt_W_conjTensorProduct_timeShiftCanonicalExtension_to_imagAxis`
   give the canonical ambient upper-half-plane witness and its horizontal-line
   boundary recovery at `(t : ℂ) * Complex.I`.
3. In
   [OSToWightmanPositivity.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean):
   `tendsto_bvt_F_canonical_xiShift_shell_sub_iterated_to_timeShift_sub_canonicalExtension`
   computes the limit of the explicit shell-minus-iterated expression as

```lean
bvt_W OS lgc (n + m)
  (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ))
-
bvt_W_conjTensorProduct_timeShiftCanonicalExtension
  (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I)
```

This residual theorem is **diagnostic only**. It must not be turned into an
unconditional zero-limit target for arbitrary `φ, ψ`. Such a theorem would
identify a real-time Wightman value with an imaginary-axis Laplace value for
arbitrary test data, reproducing the old false `hschw` shape in a more
elaborate form.

The corrected target is the transported-image version required by Lemma 4.2.
The next proof must include Section-4.3 quotient hypotheses tying the ambient
Wightman representatives `φ, ψ` to positive-time Euclidean preimages `f, g`.

The theorem that actually closes the shell side is:

```lean
private theorem
    tendsto_bvt_F_canonical_xiShift_to_canonicalExtension_imagAxis_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g) :
    ∀ t : ℝ, 0 < t →
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  ↑(y k μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ)) *
              (φ.conjTensorProduct ψ) y)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I)))
```

This theorem is equivalent, by the already-proved shell boundary-value theorem
and canonical imag-axis descended-pairing theorem, to the following pointwise
Section-4.3 bridge:

```lean
private theorem
    bvt_W_timeShift_eq_descendedPsiZ_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g) :
    ∀ t : ℝ, ∀ ht : 0 < t,
      bvt_W OS lgc (n + m)
        (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
          (d := d) OS lgc φ ψ hψ_compact)
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm φ ψ hψ_compact)
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (t * Complex.I)))
            (by
              simpa [Complex.mul_im, ht.ne']
                using mul_pos Real.two_pi_pos ht)))
```

Proof transcript for the equivalence:

1. Use
   `tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue`
   to identify the shell limit with the left side of
   `bvt_W_timeShift_eq_descendedPsiZ_of_section43Transport`.
2. Use
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imagAxis_eq_fourierPairingDescendsToSection43PositiveEnergy1D_psiZ`
   to rewrite the canonical imag-axis value as the descended `ψ_z` pairing on
   the right side.
3. Apply `tendsto_nhds_unique` after rewriting both limits to the same scalar.

Once the shell side is closed, the OS matrix-element target is obtained by the
already-proved ambient/preimage canonical-to-OS reducer:

```lean
private theorem
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imag_eq_osHolomorphicValue_of_ambient_descended_psiZ_boundaryValue_eq
```

Its remaining hypothesis is the quotient/slice comparison

```lean
∀ t : ℝ, ∀ ht : 0 < t,
  fourierPairingDescendsToSection43PositiveEnergy1D
    (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
      (d := d) OS lgc φ ψ hψ_compact)
    (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
      (d := d) OS lgc hm φ ψ hψ_compact)
    (section43PositiveEnergyQuotientMap1D (ψZ t ht))
  =
  selfAdjointSpectralBoundaryValueOffdiagCLM
    (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
    (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
    xF xG
    (ψZ t ht)
```

where `ψZ t ht` abbreviates
`SCV.schwartzPsiZ (((2 * Real.pi : ℂ) * (t * Complex.I)))` with the positivity
proof `by simpa [Complex.mul_im, ht.ne'] using mul_pos Real.two_pi_pos ht`, and
`xF, xG` are the OS Hilbert vectors of
`PositiveTimeBorchersSequence.single n f.1 f.2` and
`PositiveTimeBorchersSequence.single m g.1 g.2`.

#### 5.9.4a.1. Implementation packet for the transported-image bridge

Correction status, 2026-04-13: this subsection records the older
transported-image draft. It is retained for the later `hH_imag_os` /
Section-4.3 identification, but it is not the current shell-to-Laplace
implementation route. The immediate Lean target is now the canonical
positive-height shell packet in §5.9.4a.1.ε, beginning with
`canonicalXiShift_mem_forwardTube`. The public Paley-Wiener export and the
strengthened BV/FL `Tflat` package have already been implemented and checked.

The downstream shell-minus-horizontal cancellation theorem remains part of the
consumer chain, but its proof must come from the corrected finite-height
canonical residual
`bvt_F_canonical_xiShift_shell_eq_iterated_fourierLaplaceIntegral` and the
existing reducer
`tendsto_bvt_F_canonical_xiShift_to_ambientCanonicalExtension_imagAxis_of_shell_sub_horizontal_tendsto_zero`.
The older Section-4.3 residual names displayed below are historical
transported-image drafts and must not be used to bypass the canonical-shell
packet.

```lean
private theorem
    tendsto_bvt_F_canonical_xiShift_shell_sub_horizontal_to_zero_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t : ℝ} (ht : 0 < t) :
    let ψZ : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y) -
        (∫ x : ℝ,
          bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc φ ψ hψ_compact (↑x + ↑ε * Complex.I) *
          (SchwartzMap.fourierTransformCLM ℂ ψZ) x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0)
```

This historical theorem shape is allowed only as a transported-image
specialization because the hypotheses `hφf` and `hψg` are part of the
statement. It is not the current shell-to-Laplace theorem, and it must not be
used as a substitute for the canonical-shell residual packet.

For Lean execution, do **not** prove the residual theorem by an unnamed
analytic lemma. The non-subtracted `singleSplit` shell theorem displayed next
is downstream diagnostic/assembly work retained for older reducers; it is not
an implementation target for the live `lemma42` consumer. The first irreducible
theorem for the live shell-to-Laplace seam is the finite-height canonical
shell-to-iterated-Fourier-Laplace equality in §5.9.4a.1.ε.

```lean
private theorem
    tendsto_bvt_F_canonical_xiShift_to_singleSplitXiShift_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (f.1.osConjTensorProduct g.1) y))
```

For the Lean implementation, introduce these private local abbreviations before
the theorem. They are not route-changing wrappers; they name the two exact
scalars already displayed above so the zero-residual proof has a stable target.

```lean
private noncomputable def bvtCanonicalXiShiftShell
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (t : ℝ) : ℝ → ℂ := fun ε =>
  ∫ y : NPointDomain d (n + m),
    bvt_F OS lgc (n + m)
      (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
        (fun k μ =>
          ↑(y k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
              Complex.I)
        (t : ℂ)) *
      (φ.conjTensorProduct ψ) y

private noncomputable def bvtSingleSplitXiShiftScalar
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (t : ℝ) : ℂ :=
  ∫ y : NPointDomain d (n + m),
    bvt_F OS lgc (n + m)
      (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
        (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
      (f.osConjTensorProduct g) y
```

Withdrawn pointwise-first surface:

```lean
private theorem
    bvt_W_timeShift_sub_descendedPsiZ_zero_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t : ℝ} (ht : 0 < t) :
    bvt_W OS lgc (n + m)
        (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) -
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
          (d := d) OS lgc φ ψ hψ_compact)
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm φ ψ hψ_compact)
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (t * Complex.I)))
            (by
              simpa [Complex.mul_im, ht.ne']
                using mul_pos Real.two_pi_pos ht))) =
      0
```

This statement is not false on the transported surface, but it must **not** be
the first implementation target. Its left side contains the bare pointwise
Wightman time-shift value
`bvt_W OS lgc (n + m)
  (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ))`.
A direct proof would require a separate point-evaluation normal form for the
time-shift distribution. The existing production infrastructure is shaped for
Schwartz-tested boundary values and horizontal-line pairings, so this theorem
is downstream only. After
`bvt_W_timeShift_eq_descendedPsiZ_of_section43Transport` is obtained from the
limit-level zero residual, the subtractive form is the one-line formal corollary
`sub_eq_zero.mpr`.

Do not attach any slice/Fubini proof transcript to this pointwise theorem. The
slice-kernel zero lemmas are consumed first by the positive-height
shell/interchange theorem below, where both sides remain under integral signs.

Exact route decision after the 2026-04-12 scalar-normal-form audit:

The pointwise-first theorem
`bvt_W_timeShift_sub_descendedPsiZ_zero_of_section43Transport` is withdrawn as
the first hard Lean target. It has a bare value
`bvt_W(... timeShift t ...)`, so a direct proof would require an additional
Schwartz approximate-identity or point-evaluation normal form. That is the
wrong first implementation surface for the code we already have.

The later 2026-04-13 correction sharpens this decision: the first hard theorem
for the live shell-to-Laplace seam is the **canonical positive-height
shell/interchange normal form** in §5.9.4a.1.ε, not the transported
single-split normal form below. This keeps both sides as honest pairings
against Schwartz tests and uses the existing production theorem
`tendsto_bvt_F_canonical_xiShift_shell_sub_iterated_to_timeShift_sub_canonicalExtension`
to recover the pointwise scalar equality only after the zero residual has been
proved. The older Section-4.3 finite-height theorem below is retained as a
historical transported-image draft, not as an implementation target for the
current blocker.

The selected right-block time coordinate is still

```lean
let rψ : Fin m := ⟨0, hm⟩
let r : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
```

where `r` is the embedded right-block coordinate and `rψ` is the corresponding
coordinate on the isolated right factor. This is a code-level convention, not
just paper notation: in
[OSToWightman.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightman.lean),
`xiShift j 0` updates every tail coordinate `i` with `j.val ≤ i.val`. The
comment above its definition explains why this is the correct single
cumulative-difference time variable: shifting only one absolute coordinate
would alter two adjacent difference variables. Therefore the one-variable
time-shift in Lemma 4.2 is the tail-gap coordinate `r = ⟨n, ...⟩`, while the
same variable appears on the isolated right factor as `rψ = 0`.

The finite-height theorem statement must expose the exact measure variables,
frozen background-time maps, and spatial Fourier variables whose integrand is a
linear combination of the two scalar kernels already present in
`OSToWightmanPositivity.lean`:

```lean
fourierInvPairingCLM_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport
  (d := d) (n := n) (m := m) hφf
  rφ tφ htφ ξφ rψ tψ htψ ξψ

fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport
  (d := d) (n := n) (m := m) hφf hψg
  rφ tφ htφ ξφ rψ tψ htψ ξψ
```

Here `tφ`, `tψ` are the frozen background-time maps produced by the expanded
time-shift/conj-tensor-product normal form, `htφ` and `htψ` are exactly the
nonnegative frozen-time obligations needed by
`tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime`,
and `ξφ`, `ξψ` are the two spatial Fourier variables.

The precise finite-height theorem that implements OS I p. 96
`(4.23) -> (4.24)` is the following. This is **not** the withdrawn pointwise
Wightman theorem above: both sides are positive-height / Schwartz-tested
quantities. It is also not an arbitrary same-shell Euclidean/Wightman equality;
the Section-4.3 transport hypotheses `hφf` and `hψg` are part of the statement.

```lean
private theorem
    bvt_F_canonical_xiShift_shell_sub_iterated_fourierLaplaceIntegral_eq_zero_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    (∫ y : NPointDomain d (n + m),
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
        (φ.conjTensorProduct ψ) y) -
    (∫ x : ℝ,
      (∫ τ : ℝ,
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (SCV.schwartzPsiZ
            ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
            (by
              have hscaled : 0 < (2 * Real.pi) *
                  (((x : ℂ) + ε * Complex.I).im) :=
                mul_pos Real.two_pi_pos (by simpa using hε)
              simpa [Complex.mul_im] using hscaled))) τ) *
      (SchwartzMap.fourierTransformCLM ℂ ψZt) x) =
    0
```

The proof of this finite-height theorem must be factored through one exact
normal-form helper, not through a wrapper. That helper names the scalar before
the Wightman time-shift pairing is unfolded:

```lean
private theorem
    bvt_F_canonical_xiShift_shell_eq_integrated_descendedPsiZ_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    let TW : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
      bvt_W_conjTensorProduct_timeShiftTemperedFunctional
        (d := d) OS lgc φ ψ hψ_compact
    let hTW :
      SCV.HasOneSidedFourierSupport TW :=
      bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
        (d := d) OS lgc hm φ ψ hψ_compact
    (∫ y : NPointDomain d (n + m),
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
        (φ.conjTensorProduct ψ) y) =
    ∫ x : ℝ,
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        TW hTW
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
            (by
              have hscaled : 0 < (2 * Real.pi) *
                  (((x : ℂ) + ε * Complex.I).im) :=
                mul_pos Real.two_pi_pos (by simpa using hε)
              simpa [Complex.mul_im] using hscaled))) *
      (SchwartzMap.fourierTransformCLM ℂ ψZt) x
```

Mandatory `Fin 1` adapter before applying `schwartz_clm_fubini_exchange`:

Do **not** instantiate `schwartz_clm_fubini_exchange` directly with

```lean
TW : SchwartzMap ℝ ℂ →L[ℂ] ℂ
```

The Fubini axiom is stated for functionals on
`SchwartzMap (Fin m → ℝ) ℂ`, so the normal-form helper must first pass through
the following local one-coordinate adapter. This is type-level infrastructure,
not a theorem-surface wrapper: it is exactly the change from the paper's
one real time variable to the production axiom's `Fin 1 → ℝ` parameter.

```lean
let e1 : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ

let toFin1 : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap (Fin 1 → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1

let fromFin1 : SchwartzMap (Fin 1 → ℝ) ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1.symm

let T1 : SchwartzMap (Fin 1 → ℝ) ℂ →L[ℂ] ℂ :=
  TW.comp fromFin1

let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
  SCV.schwartzPsiZ
    ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
    (by
      have hscaled : 0 < (2 * Real.pi) *
          (((x : ℂ) + ε * Complex.I).im) :=
        mul_pos Real.two_pi_pos (by simpa using hε)
      simpa [Complex.mul_im] using hscaled)

let f1 : SchwartzMap (Fin 1 → ℝ) ℂ :=
  toFin1 ((SchwartzMap.fourierTransformCLM ℂ) ψZt)

let g1 : (Fin 1 → ℝ) → SchwartzMap (Fin 1 → ℝ) ℂ := fun x1 =>
  toFin1 ((SchwartzMap.fourierTransformCLM ℂ) (ψZxε (e1 x1)))
```

The only reindex simplifications allowed here are:

```lean
have h_from_to (χ : SchwartzMap ℝ ℂ) :
    fromFin1 (toFin1 χ) = χ := by
  ext x
  simp [fromFin1, toFin1, e1]

have h_to_apply (χ : SchwartzMap ℝ ℂ) (x1 : Fin 1 → ℝ) :
    toFin1 χ x1 = χ (e1 x1) := by
  simp [toFin1]

have h_fin1_volume (F : ℝ → ℂ) :
    (∫ x1 : Fin 1 → ℝ, F (e1 x1)) = ∫ x : ℝ, F x := by
  simpa [e1] using
    (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).integral_comp'
      (g := F)
```

The corresponding local consequence for the Fubini output is:

```lean
have h_outer_real :
    (∫ x1 : Fin 1 → ℝ, T1 (g1 x1) * f1 x1) =
      ∫ x : ℝ,
        TW ((SchwartzMap.fourierTransformCLM ℂ) (ψZxε x)) *
          (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
  let F : ℝ → ℂ := fun x =>
    TW ((SchwartzMap.fourierTransformCLM ℂ) (ψZxε x)) *
      (SchwartzMap.fourierTransformCLM ℂ ψZt) x
  calc
    (∫ x1 : Fin 1 → ℝ, T1 (g1 x1) * f1 x1)
        = ∫ x1 : Fin 1 → ℝ, F (e1 x1) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with x1
            simp [F, T1, g1, f1, h_from_to, h_to_apply]
    _ = ∫ x : ℝ, F x := h_fin1_volume F
    _ = ∫ x : ℝ,
        TW ((SchwartzMap.fourierTransformCLM ℂ) (ψZxε x)) *
          (SchwartzMap.fourierTransformCLM ℂ ψZt) x := rfl
```

No Fourier-transform/reindex commutation theorem is required in this package:
`SchwartzMap.fourierTransformCLM ℂ` is applied on `SchwartzMap ℝ ℂ` first, and
only the already transformed test is transported by `toFin1`.

If Lean asks for the two side hypotheses of `schwartz_clm_fubini_exchange`, the
first helper statements must be exactly these, with no stronger theorem surface:

```lean
private theorem
    continuous_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal
    {ε : ℝ} (hε : 0 < ε) :
    Continuous
      (fun x1 : Fin 1 → ℝ =>
        let e1 : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
          ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
        let toFin1 : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap (Fin 1 → ℝ) ℂ :=
          SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1
        toFin1
          ((SchwartzMap.fourierTransformCLM ℂ)
            (SCV.schwartzPsiZ
              ((((2 * Real.pi : ℝ) : ℂ) * ((e1 x1 : ℂ) + ε * Complex.I)))
              (by
                have hscaled : 0 < (2 * Real.pi) *
                    (((e1 x1 : ℂ) + ε * Complex.I).im) :=
                  mul_pos Real.two_pi_pos (by simpa using hε)
                simpa [Complex.mul_im] using hscaled))))

private theorem
    seminorm_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal_growth
    {ε : ℝ} (hε : 0 < ε) :
    ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ (x1 : Fin 1 → ℝ),
        SchwartzMap.seminorm ℝ k n
          (let e1 : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
            ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
           let toFin1 : SchwartzMap ℝ ℂ →L[ℂ]
                SchwartzMap (Fin 1 → ℝ) ℂ :=
            SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1
           toFin1
            ((SchwartzMap.fourierTransformCLM ℂ)
              (SCV.schwartzPsiZ
                ((((2 * Real.pi : ℝ) : ℂ) * ((e1 x1 : ℂ) + ε * Complex.I)))
                (by
                  have hscaled : 0 < (2 * Real.pi) *
                      (((e1 x1 : ℂ) + ε * Complex.I).im) :=
                    mul_pos Real.two_pi_pos (by simpa using hε)
                  simpa [Complex.mul_im] using hscaled)))) ≤
          C * (1 + ‖x1‖) ^ N
```

These side helpers are the public versions of the already-used Paley-Wiener
horizontal continuity/growth estimates, transported through `toFin1`. They are
allowed only because they discharge the exact `hg_cont` and `hg_bound` premises
of `schwartz_clm_fubini_exchange`; they must not introduce a new comparison
between Wightman and OS scalars.

Implementation transcript for the two `Fin 1` side helpers:

1. Put these helpers in
   [SCV/PaleyWiener.lean](/Users/xiyin/OSReconstruction/OSReconstruction/SCV/PaleyWiener.lean),
   or in a small imported Paley-Wiener support file, not in the theorem-3
   positivity frontier. They are one-variable Schwartz/PW facts and should be
   available before the OS-specific normal-form helper is attempted.
2. First expose the underlying real-line continuity theorem:

```lean
theorem continuous_schwartzPsiZ_twoPi_horizontal
    {η : ℝ} (hη : 0 < η) :
    Continuous
      (fun x : ℝ =>
        SCV.schwartzPsiZ
          ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + η * Complex.I)))
          (by
            have hscaled : 0 < (2 * Real.pi) *
                (((x : ℂ) + η * Complex.I).im) :=
              mul_pos Real.two_pi_pos (by simpa using hη)
            simpa [Complex.mul_im] using hscaled))
```

   Proof: in `PaleyWiener.lean`, reuse the existing private probe
   calculations
   `continuous_weightedDerivToBCFCLM_scaledHorizontal` and the definition
   `scaledHorizontalSchwartzPsi`. The only algebraic rewrite is
   `((2 * Real.pi : ℂ) * ((x : ℂ) + η * Complex.I))
      = ((2 * Real.pi * x : ℝ) : ℂ) +
        (2 * Real.pi * η : ℝ) * Complex.I`.
   If those probe lemmas remain private, this theorem must be placed in the
   same file below them; do not copy the whole probe development into
   `OSToWightmanPositivity.lean`.
3. Derive
   `continuous_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal` by
   composition:

```lean
let e1 : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
let toFin1 : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap (Fin 1 → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1
let L : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap (Fin 1 → ℝ) ℂ :=
  toFin1.comp (SchwartzMap.fourierTransformCLM ℂ)
exact
  L.continuous.comp
    ((continuous_schwartzPsiZ_twoPi_horizontal hε).comp e1.continuous)
```

4. Prove the growth helper by the same seminorm-bound pattern as
   `SCV.schwartzCLM_seminorm_horizontal_growth` in
   [FourierLaplaceCore.lean](/Users/xiyin/OSReconstruction/OSReconstruction/SCV/FourierLaplaceCore.lean),
   but with target space `SchwartzMap (Fin 1 → ℝ) ℂ`:

```lean
let L : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap (Fin 1 → ℝ) ℂ :=
  toFin1.comp (SchwartzMap.fourierTransformCLM ℂ)
let q : Seminorm ℂ (SchwartzMap ℝ ℂ) :=
  (schwartzSeminormFamily ℂ (Fin 1 → ℝ) ℂ (k, n)).comp L.toLinearMap
have hq_cont : Continuous q := by
  change Continuous (fun φ : SchwartzMap ℝ ℂ =>
    schwartzSeminormFamily ℂ (Fin 1 → ℝ) ℂ (k, n) (L φ))
  exact
    ((schwartz_withSeminorms ℂ (Fin 1 → ℝ) ℂ).continuous_seminorm
      (k, n)).comp L.continuous
obtain ⟨s, D, hD_ne, hq_bound⟩ :=
  Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) q hq_cont
```

   Then finish exactly as `SCV.schwartzCLM_seminorm_horizontal_growth` does,
   using `SCV.schwartzPsiZ_seminorm_horizontal_bound` on the real-line family
   with horizontal height `2 * Real.pi * ε` and real coordinate
   `2 * Real.pi * e1 x1`. The final polynomial rewrite uses continuity of
   `e1` to dominate `|e1 x1|` by a constant multiple of `‖x1‖`, then absorbs
   constants into `C` and `N`. If this final norm-domination step is not
   already a local `simp` consequence of `ContinuousLinearEquiv.funUnique`,
   the only permitted auxiliary lemma is:

```lean
private theorem funUnique_abs_le_norm
    (x1 : Fin 1 → ℝ) :
    |(ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ) x1| ≤ ‖x1‖ := by
  simpa [Real.norm_eq_abs] using (norm_le_pi_norm x1 0)
```

   No OS, Wightman, quotient, or semigroup object may appear in this growth
   helper or its auxiliaries.

Implementation-readiness gate for the normal-form helper:

The statement
`bvt_F_canonical_xiShift_shell_eq_integrated_descendedPsiZ_of_section43Transport`
is the correct consumer surface, but it is **not** allowed as the first Lean
edit until the shell-side slice normal form below is available. The words
"rewrite by the ordered-product split" are not a proof. They must be replaced
by a concrete local theorem whose left side is the canonical `bvt_F`
time-shifted shell and whose right side is the real-line `TW` pairing against
`ψ_Z`.

The first non-Paley-Wiener theorem in this packet is therefore the following
more local normal form. It is not a wrapper: it removes only the already-proved
`xiShift` shell algebra and exposes the genuine OS I `(4.23) -> (4.24)`
interchange target.

```lean
private theorem
    bvt_F_canonical_conjTensorProduct_timeShift_shell_eq_integrated_TW_psiZ
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
      SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
        (by
          have hscaled : 0 < (2 * Real.pi) *
              (((x : ℂ) + ε * Complex.I).im) :=
            mul_pos Real.two_pi_pos (by simpa using hε)
          simpa [Complex.mul_im] using hscaled)
    let TW : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
      bvt_W_conjTensorProduct_timeShiftTemperedFunctional
        (d := d) OS lgc φ ψ hψ_compact
    (∫ y : NPointDomain d (n + m),
      bvt_F OS lgc (n + m)
        (fun k μ =>
          ↑(y k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
              Complex.I) *
        (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) y) =
    ∫ x : ℝ,
      TW ((SchwartzMap.fourierTransformCLM ℂ) (ψZxε x)) *
        (SchwartzMap.fourierTransformCLM ℂ ψZt) x
```

Historical note: this was the earlier proposed shell-side theorem name. For the
current route it is superseded by
`bvt_F_canonical_xiShift_shell_eq_iterated_fourierLaplaceIntegral` in
§5.9.4a.1.ε, where the shell and horizontal sides are compared through the
common `Tflat`. In the older draft, the larger displayed helper was then
obtained formally:

1. rewrite its left side by
   `(bvt_F_canonical_conjTensorProduct_timeShift_eq_xiShift ... t ε).symm`;
2. apply
   `bvt_F_canonical_conjTensorProduct_timeShift_shell_eq_integrated_TW_psiZ`;
3. rewrite the right side pointwise by
   `fourierPairingDescendsToSection43PositiveEnergy1D_apply` using the local
   `TW` and `hTW`.

Proof transcript for
`bvt_F_canonical_conjTensorProduct_timeShift_shell_eq_integrated_TW_psiZ`:

1. Introduce `ψZt`, `ψZxε x`, `TW`, `hTW`, `rψ`, and
   `r : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩`. The positivity proof
   for `ψZxε x` is `mul_pos Real.two_pi_pos (by simpa using hε)`. The
   positivity proof for `ψZt` is `mul_pos Real.two_pi_pos ht`.
2. Do not use fresh `xiShift` algebra inside this theorem. Its left side is
   already the time-shifted canonical shell. The existing configuration-space
   theorem `bvt_F_canonical_conjTensorProduct_timeShift_eq_xiShift` is used
   only outside this theorem, when deriving the larger `xiShift` helper from
   this local normal form.
3. Apply `partialFourierSpatial_fun_eq_integral` to the left and right
   configuration factors before any Section-4.3 quotient rewrite. Spatial
   constants may be rewritten only by `partialFourierSpatial_fun_eq_integral`,
   `partialFourierSpatial_fun_eq_integral_realProd`, and
   `physicsFourierFlatCLM_integral`.
4. Frozen-slice coordinate packet. After the product/time-shift split, the
   variables feeding a slice bridge must be organized as follows:

```lean
let rψ : Fin m := ⟨0, hm⟩

-- `rφ` is not fixed by the tail-shift convention. It is the left-factor
-- one-variable slice chosen by the current frozen integrand.
variable (rφ : Fin n)

-- Full time vectors after applying `nPointTimeSpatialCLE` to the split factors.
variable (aφ : Fin n → ℝ)
variable (aψ : Fin m → ℝ)

-- Frozen maps are the full vectors themselves; evaluating at their selected
-- coordinate recovers the original partial-Fourier value by `Function.update`.
let tφ : Fin n → ℝ := aφ
let tψ : Fin m → ℝ := aψ
let sφ : ℝ := tφ rφ
let sψ : ℝ := tψ rψ
```

   The corresponding self-update rewrites are mandatory local normal forms:

```lean
have hφ_update :
    Function.update tφ rφ sφ = tφ := by
  ext i
  by_cases hi : i = rφ
  · subst hi
    simp [sφ]
  · simp [sφ, hi]

have hψ_update :
    Function.update tψ rψ sψ = tψ := by
  ext i
  by_cases hi : i = rψ
  · subst hi
    simp [sψ]
  · simp [sψ, hi]
```

   Hence the exact slice-to-full-time rewrites are:

```lean
have hφ_slice_eval :
    partialFourierSpatial_timeSliceSchwartz
        (d := d) (n := n) φ rφ tφ ξφ sφ =
      OSReconstruction.partialFourierSpatial_fun
        (d := d) (n := n) φ (tφ, ξφ) := by
  simp [partialFourierSpatial_timeSliceSchwartz, sφ, hφ_update]

have hψ_slice_eval :
    partialFourierSpatial_timeSliceSchwartz
        (d := d) (n := m) ψ rψ tψ ξψ sψ =
      OSReconstruction.partialFourierSpatial_fun
        (d := d) (n := m) ψ (tψ, ξψ) := by
  simp [partialFourierSpatial_timeSliceSchwartz, sψ, hψ_update]
```

   Do not set `rφ := 0`, `rφ := Fin.last _`, or any other special left index
   unless a later expansion theorem explicitly produces that choice. The
   existing transport lemmas are generic in `rφ`, and the only fixed coordinate
   forced by the live shell is `rψ = 0` on the right factor.

   Important zero-arity branch: this packet is only available in the branch
   `hn : 0 < n`. The live theorem surface has only `hm : 0 < m`, so the
   eventual proof must start with:

```lean
by_cases hn : 0 < n
```

   In the `hn` branch, choose or bind `rφ : Fin n` and use the four slice
   bridge lemmas displayed below. In the `¬ hn` branch, `n = 0`, so no
   `rφ : Fin n` exists and no left one-variable slice theorem can be
   instantiated. That branch must be discharged by a separate zero-left
   quotient lemma:

```lean
private theorem section43_zero_left_repr_eq_transport_pointwise
    {φ : SchwartzNPoint d 0}
    {f : euclideanPositiveTimeSubmodule (d := d) 0}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) 0 φ =
        os1TransportComponent d 0 f) :
    φ = (EuclideanPositiveTimeComponent.ofSubmodule f).1 := by
  ext x
  have hq :
      section43PositiveEnergyQuotientMap (d := d) 0 φ =
        section43PositiveEnergyQuotientMap (d := d) 0 f.1 := by
    simpa [os1TransportComponent_apply] using hφf
  have hEqOn :=
    eqOn_region_of_section43PositiveEnergyQuotientMap_eq
      (d := d) (n := 0) hq
  exact hEqOn (by intro i; exact Fin.elim0 i)
```

   The proof is not a new analytic ingredient: `section43PositiveEnergyRegion
   d 0` is the whole zero-point domain because the `Fin 0` time condition is
   vacuous, so the quotient equality gives pointwise equality on the unique
   zero-point configuration. If Lean does not already expose this as a local
   simp consequence of `eqOn_region_of_section43PositiveEnergyQuotientMap_eq`,
   this exact zero-left lemma is the only permitted auxiliary for the `n = 0`
   branch. Do not add a `0 < n` hypothesis to the main theorem.
5. The slice-pairing expansion must expose only these four one-variable
   Schwartz functions for frozen data `rφ tφ ξφ rψ tψ ξψ`:

```lean
let φSlice :=
  partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ rφ tφ ξφ
let ψSlice :=
  partialFourierSpatial_timeSliceSchwartz (d := d) (n := m) ψ rψ tψ ξψ
let fSlice :=
  partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
    (EuclideanPositiveTimeComponent.ofSubmodule f).1 rφ tφ ξφ
let gSlice :=
  partialFourierSpatial_timeSliceSchwartz (d := d) (n := m)
    (EuclideanPositiveTimeComponent.ofSubmodule g).1 rψ tψ ξψ
```

   The only allowed transport rewrites at this level are:

```lean
fourierInvPairingCLM_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport
  (d := d) (n := n) (m := m) hφf
  rφ tφ htφ ξφ rψ tψ htψ ξψ

fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport
  (d := d) (n := n) (m := m) hφf hψg
  rφ tφ htφ ξφ rψ tψ htψ ξψ
```

   After these rewrites, no ambient slice `φSlice` or `ψSlice` may remain in
   the surviving scalar. If one remains, the slice expansion is incomplete and
   the proof must return to this document.
6. Time-shift quotient caveat. The Section-4.3 quotient equalities
   `hφf` and `hψg` compare the **unshifted** ambient representatives with their
   positive-time preimages on the nonnegative time region. They do not commute
   for free with the real-time shift on the right factor:

```lean
timeShiftSchwartzNPoint (d := d) t ψ x =
  ψ (fun i => x i - timeShiftVec d t)
```

   Therefore, for `0 < t`, equality of `ψ` and `g.1` on nonnegative
   configurations does **not** imply equality of
   `timeShiftSchwartzNPoint t ψ` and `timeShiftSchwartzNPoint t g` on the
   Section-4.3 nonnegative region: the shifted preimage point
   `x i - timeShiftVec d t` can have negative time. The support theorem
   `timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_nonneg` proves
   only that a shifted **positive-time preimage** still has ordered positive
   support; it does not justify replacing a shifted ambient representative by
   the shifted preimage representative.

   Consequence: the full-orthant packet below is only an unshifted local
   slice-descent tool. It may be used after the shell/Paley-Wiener expansion has
   separated the real-time shift into the external one-variable `ψ_Z` kernel
   and exposed unshifted Section-4.3 slice representatives. It must never be
   used to prove a pointwise equality involving
   `φ.conjTensorProduct (timeShiftSchwartzNPoint t ψ)` by replacing the shifted
   `ψ` directly. The actual shifted comparison has to be a
   positive-support time-shift distribution theorem, i.e. an equality of the
   descended one-variable pairing against `ψ_Z`, not an equality of shifted
   representatives.
7. Tail-gap gate before any frozen slice theorem is used. The hypotheses
   `htφ` and `htψ` for the one-variable transport lemmas are **not** produced
   by the slice support theorem and must not be assumed for arbitrary frozen
   background data. They are available only after the current integrand has
   already been restricted to positive cumulative tail gaps and those gaps have
   been converted to full nonnegative absolute time vectors on the corresponding
   factor:

```lean
have hφ_nonneg : ∀ i : Fin n, 0 ≤ tφ i := by
  -- supplied by positive tail gaps plus `absTimesOfTailGaps_nonneg`, not by the slice lemma
  exact ...

have hψ_nonneg : ∀ i : Fin m, 0 ≤ tψ i := by
  -- supplied by positive tail gaps plus `absTimesOfTailGaps_nonneg`, not by the slice lemma
  exact ...

have htφ : ∀ i : Fin n, i ≠ rφ → 0 ≤ tφ i := by
  intro i hi
  exact hφ_nonneg i

have htψ : ∀ i : Fin m, i ≠ rψ → 0 ≤ tψ i := by
  intro i hi
  exact hψ_nonneg i
```

   These obligations are **not** supplied by `ht`, `hε`, `hf_compact`, or
   `hg_compact`. They are also not the support theorem
   `tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime`:
   that theorem gives one-sided Fourier support for positive-time preimage
   slices, while `htφ` and `htψ` are the separate nonnegative-background-time
   assumptions needed to move ambient representatives to their positive-time
   preimages on the Section-4.3 quotient surface.

   Therefore the next unshifted local theorem before the frozen-slice scalar
   bridge is a **full absolute-time adapter packet**, not another one-variable
   wrapper. This packet supplies the nonnegative-background hypotheses for
   unshifted slice representatives only after the global tail-gap descent has
   produced them; it is not the shifted `ψ` comparison.
   The packet has two local facts that are already implementation-level from
   current code:

```lean
private theorem partialFourierSpatial_fun_eq_of_repr_eq_transport_on_nonneg
    {n : ℕ}
    {φ : SchwartzNPoint d n}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (τ : Fin n → ℝ)
    (hτ : ∀ i : Fin n, 0 ≤ τ i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) φ (τ, ξ) =
      OSReconstruction.partialFourierSpatial_fun (d := d) (n := n)
        (EuclideanPositiveTimeComponent.ofSubmodule f).1 (τ, ξ) := by
  have hregion :
      Set.EqOn (φ : NPointDomain d n → ℂ)
        ((f : euclideanPositiveTimeSubmodule (d := d) n) :
          NPointDomain d n → ℂ)
        (section43PositiveEnergyRegion d n) := by
    have hq :
        section43PositiveEnergyQuotientMap (d := d) n φ =
          section43PositiveEnergyQuotientMap (d := d) n f.1 := by
      simpa [os1TransportComponent_apply] using hφf
    exact eqOn_region_of_section43PositiveEnergyQuotientMap_eq
      (d := d) (n := n) (f := φ) (g := f.1) hq
  exact
    partialFourierSpatial_fun_eq_of_eqOn_section43PositiveEnergyRegion
      (d := d) (n := n) hregion τ hτ ξ

private theorem partialFourierSpatial_fun_eq_zero_of_not_nonneg_time
    {n : ℕ}
    (f : EuclideanPositiveTimeComponent d n)
    (τ : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (hneg : ∃ r : Fin n, τ r < 0) :
    OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f.1 (τ, ξ) = 0 := by
  obtain ⟨r, hr⟩ := hneg
  let s : ℝ := τ r
  have hupdate : Function.update τ r s = τ := by
    ext i
    by_cases hi : i = r
    · subst hi
      simp [s]
    · simp [s, hi]
  simpa [s, hupdate] using
    partialFourierSpatial_fun_eq_zero_of_neg_time
      (d := d) (n := n) f r τ ξ hr
```

   The Lean-ready full-orthant slice adapter is:

```lean
private theorem
    unshifted_full_timeOrthant_descended_pairing_eq_of_section43Transport
    {n m : ℕ}
    {φ : SchwartzNPoint d n} {ψ : SchwartzNPoint d m}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    {g : euclideanPositiveTimeSubmodule (d := d) m}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    (rφ : Fin n) (tφ : Fin n → ℝ)
    (hφ_nonneg : ∀ i : Fin n, 0 ≤ tφ i)
    (ξφ : EuclideanSpace ℝ (Fin n × Fin d))
    (rψ : Fin m) (tψ : Fin m → ℝ)
    (hψ_nonneg : ∀ i : Fin m, 0 ≤ tψ i)
    (ξψ : EuclideanSpace ℝ (Fin m × Fin d)) :
    fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := m)
          (EuclideanPositiveTimeComponent.ofSubmodule g).1 rψ tψ ξψ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ rφ tφ ξφ)) =
      fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 rφ tφ ξφ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := m) ψ rψ tψ ξψ)) := by
  have htφ : ∀ i : Fin n, i ≠ rφ → 0 ≤ tφ i := by
    intro i _
    exact hφ_nonneg i
  have htψ : ∀ i : Fin m, i ≠ rψ → 0 ≤ tψ i := by
    intro i _
    exact hψ_nonneg i
  exact
    fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport
      (d := d) (n := n) (m := m) hφf hψg
      rφ tφ htφ ξφ rψ tψ htψ ξψ
```

   This adapter is not the global support theorem. It merely packages the
   already-proved one-variable slice bridge once the proof has a full
   nonnegative absolute time vector. The tail-gap theorem
   `bvt_W_flattened_tailGapOrbit_pairing_eq_of_eqOn_positiveGapOrthant`
   displayed below remains a useful special case, but the live Section-4.3
   hard theorem now consumes the more general Fourier-side support statement
   `tflat_pairing_eq_of_eqOn_dualCone`. The
   Positivity-side expanded normal form must instantiate the full-kernel
   `KAmbient`, `KTransport`, and dual-cone EqOn hypothesis only after the
   time-shift has already been moved into the one-variable Paley-Wiener kernel.
   It is **not** valid to integrate the one-variable slice lemmas over arbitrary
   background times, and it is also **not** valid to apply this packet directly
   to a shifted ambient
   representative.

   Important support-interface correction. The global support theorem must not
   be phrased as a direct application of
   `SCV.hasFourierSupportIn_eqOn` to restrict primal frozen time variables.
   That theorem is a **frequency-side** equality principle for a distribution
   already supported in `DualConeFlat C`; production uses it, for example, to
   remove a dual-cone cutoff that is equal to `1` on `DualConeFlat C`.
   It does not by itself say that a configuration/time test can be replaced by
   its restriction to the nonnegative time orthant.

   The correct Lean shape mirrors the already-compiled one-variable theorem
   `hasOneSidedFourierSupport_bvt_W_conjTensorProduct_timeShift`: first derive
   an appropriate one-/multi-sided Fourier-support statement from the full
   flattened `Tflat` package, then use the resulting Fourier-support pairing
   theorem to prove dependence only on the nonnegative time region. In other
   words, the orthant descent theorem is the multivariable analogue of
   `SCV.fourier_pairing_eq_of_eqOn_nonneg`, not a naked call to
   `SCV.hasFourierSupportIn_eqOn`.

   Coordinate correction for that descent. The primitive one-sided variables
   are **cumulative tail-gap variables**, not independent absolute time
   coordinates. This follows from the same `xiShift` convention recorded
   above: changing one difference coordinate shifts all later absolute
   coordinates. Therefore the global support theorem must first restrict the
   expanded kernel to the positive **tail-gap sector** and only then convert
   those nonnegative gaps to nonnegative absolute time vectors for the
   Section-4.3 adapter.

   The support geometry needed for implementation is the following finite
   family of tail directions:

```lean
private abbrev flatTailTimeShiftDirection (d q : ℕ) (j : Fin q) :
    Fin (q * (d + 1)) → ℝ :=
  fun a =>
    if j.val ≤ (finProdFinEquiv.symm a).1.val ∧
        (finProdFinEquiv.symm a).2 = (0 : Fin (d + 1)) then
      (-1 : ℝ)
    else
      0

private theorem flatTailTimeShiftDirection_zero
    {q : ℕ} (hq : 0 < q) :
    flatTailTimeShiftDirection d q ⟨0, hq⟩ =
      flatTimeShiftDirection d q := by
  ext a
  simp [flatTailTimeShiftDirection, flatTimeShiftDirection]
```

Lean status, 2026-04-13: `flatTailTimeShiftDirection` and
`flatTailTimeShiftDirection_zero` are implemented in
`OSToWightmanBoundaryValueLimits.lean` and exact-checked.

   The sign lemma generalizes the existing
   `flatTimeShiftDirection_pairing_nonpos_of_mem_dualCone`. For each tail
   index `j`, dual-cone membership implies
   `∑_{i ≥ j} ξ_{i,0} ≥ 0`, hence the negative tail-shift direction pairs
   nonpositively:

```lean
private theorem flatTailTimeShiftDirection_pairing_nonpos_of_mem_dualCone
    {q : ℕ} (j : Fin q)
    {ξ : Fin (q * (d + 1)) → ℝ}
    (hξ :
      ξ ∈ DualConeFlat ((flattenCLEquivReal q (d + 1)) '' ForwardConeAbs d q)) :
    ∑ a, flatTailTimeShiftDirection d q j a * ξ a ≤ 0
```

Lean status, 2026-04-13: this theorem is implemented in
`OSToWightmanBoundaryValueLimits.lean` and exact-checked by

```bash
lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean
```

The implementation uses the Lean order `k < j` on `Fin q` for the before-jump
branch. This is definitionally friendlier than repeatedly normalizing
`k.val < j.val`; the final `flatTailTimeShiftDirection` sum is still rewritten
from the theorem's `j.val ≤ k.val` condition to the complementary `¬ k < j`
branch.

   Proof transcript for `flatTailTimeShiftDirection_pairing_nonpos_of_mem_dualCone`:

   1. Work classically and set
      `S : ℝ := ∑ k : Fin q, (if j.val ≤ k.val then 1 else 0) *
        ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))`.
   2. Prove `hS_nonneg : 0 ≤ S` by contradiction. If `S < 0`, set
      `W : ℝ := ∑ k : Fin q,
        (if k.val < j.val then (k : ℝ) + 1 else (k : ℝ)) *
        ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))` and
      `ε := (-S) / (2 * (|W| + 1))`; then `0 < ε`.
   3. Define the pure-time test point
      `yε : Fin q → Fin (d + 1) → ℝ` by
      `yε k μ = 0` for `μ ≠ 0`, and
      `yε k 0 = if k.val < j.val then ((k : ℝ) + 1) * ε
        else 1 + (k : ℝ) * ε`.
   4. Prove `yε ∈ ForwardConeAbs d q`.
      For `k = 0`, the first difference is either `ε • e0` if `0 < j.val`
      or `1 • e0` if `j.val = 0`; both are in `InOpenForwardCone d`.
      For `k > 0`, the successive difference is:
      `ε • e0` when both `k-1` and `k` are on the same side of `j`;
      `1 • e0` when `k.val = j.val`; again both are in the open forward cone.
      The required scalar equalities are the same `Nat.sub_add_cancel` and
      `nlinarith` arithmetic used in the existing
      `flatTimeShiftDirection_pairing_nonpos_of_mem_dualCone` proof.
   5. Apply `mem_dualConeFlat.mp hξ` to
      `(flattenCLEquivReal q (d + 1)) yε`, obtaining
      `0 ≤ ∑ a, (flattenCLEquivReal q (d + 1) yε) a * ξ a`.
   6. Rewrite that sum with `sum_over_flat_timeSlots` as `S + ε * W`.
      The coefficient of `S` is the indicator `j.val ≤ k.val`; the remaining
      time-slot coefficient is `(k : ℝ) + 1` before the jump and `(k : ℝ)`
      after the jump, exactly as in the definition of `W`. Do not use the
      old `j = 0` choice `W = ∑ k, (k : ℝ) * ξ_k`; that misses the
      pre-jump `+1` terms and would not justify the displayed `yε` for
      arbitrary `j`.
   7. Prove `ε * W ≤ (-S) / 2` exactly as in the existing proof:
      `ε * W ≤ ε * |W|`,
      `ε * |W| = ((-S) / 2) * (|W| / (|W| + 1))`, and
      `|W| / (|W| + 1) ≤ 1`.
   8. The inequalities `0 ≤ S + ε * W`, `ε * W ≤ -S / 2`, and `S < 0`
      contradict by `linarith`.
   9. Finally rewrite
      `∑ a, flatTailTimeShiftDirection d q j a * ξ a` with
      `sum_over_flat_timeSlots` using the coefficient
      `fun k => if j.val ≤ k.val then (-1 : ℝ) else 0`; the result is `-S`,
      hence nonpositive by `hS_nonneg`.

   The right-block version used by the actual `φ ⊗ ψ` flattened surface should
   be derived by vector equality, not reproved from scratch.

   Implementation note, 2026-04-13: a naive
   `ext a; simp [flatTailTimeShiftDirection, zeroHeadBlockShift]` attempt is
   **not** implementation-ready. Lean exposes the cast/reindex coordinates as
   `a / (d+1)` and `a.modNat`, so the equality must follow the compiled
   split-block pattern already used by
   `zeroHeadBlockShift_flatTimeShiftDirection_pairing_eq_neg_tailTimeSum`:

   1. Define
      `xSplit := zeroHeadBlockShift (m := n*(d+1)) (n := m*(d+1))
        (flatTailTimeShiftDirection d m j)`.
   2. Define
      `vEff := (castFinCLE (by ring : (n+m)*(d+1)=n*(d+1)+m*(d+1))).symm xSplit`
      and `y := (flattenCLEquivReal (n+m) (d+1)).symm vEff`.
   3. Reuse `splitFirst_reindex_flatten_symm_eq` to prove
      `splitFirst n m y = 0`.
   4. Reuse `splitLast_reindex_flatten_symm_eq` to prove
      `splitLast n m y =
        (flattenCLEquivReal m (d+1)).symm (flatTailTimeShiftDirection d m j)`.
   5. Prove the full coordinate formula

```lean
have hy_formula :
  ∀ k : Fin (n + m), ∀ μ : Fin (d + 1),
    y k μ =
      if μ = 0 then
        if (k : ℕ) < n + j.val then 0 else (-1 : ℝ)
      else 0 := by
  intro k μ
  by_cases hk_head : (k : ℕ) < n
  · -- use `hsplitFirst`; RHS is `0` since `k < n ≤ n+j.val`
  · -- set `r : Fin m := ⟨(k : ℕ) - n, by omega⟩`
    -- use `hsplitLast`
    -- prove `j ≤ r ↔ n + j.val ≤ k.val` by `Fin.ext`/`omega`
```

   6. Convert `hy_formula` back through
      `flattenCLEquivReal.apply_symm_apply`, exactly as in the existing
      zero-head full-tail proof, obtaining

```lean
have hvEff_formula :
  ∀ a,
    vEff a =
      if (finProdFinEquiv.symm a).2 = 0 then
        if ((finProdFinEquiv.symm a).1 : Fin (n + m)).val < n + j.val
        then 0 else (-1 : ℝ)
      else 0
```

   7. Use `hvEff_formula` to prove the vector equality below. Only then should
      the sign corollary rewrite to the already checked base lemma.

```lean
private theorem zeroHeadBlockShift_flatTailTimeShiftDirection_eq
    {n m : ℕ} (j : Fin m) :
    (OSReconstruction.castFinCLE
      (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1)))
      (OSReconstruction.zeroHeadBlockShift
        (m := n * (d + 1)) (n := m * (d + 1))
        (flatTailTimeShiftDirection d m j)) =
      flatTailTimeShiftDirection d (n + m) (Fin.natAdd n j) := by
  -- Do not use bare `simp`; use the split-block coordinate proof above.

private theorem zeroHeadBlockShift_flatTailTimeShiftDirection_pairing_nonpos_of_mem_dualCone
    {n m : ℕ} (j : Fin m)
    {ξ : Fin ((n + m) * (d + 1)) → ℝ}
    (hξ :
      ξ ∈ DualConeFlat
        ((flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m))) :
    ∑ a,
      (((OSReconstruction.castFinCLE
          (by ring : n * (d + 1) + m * (d + 1) = (n + m) * (d + 1)))
        (OSReconstruction.zeroHeadBlockShift
          (m := n * (d + 1)) (n := m * (d + 1))
          (flatTailTimeShiftDirection d m j))) a) * ξ a ≤ 0 := by
  rw [zeroHeadBlockShift_flatTailTimeShiftDirection_eq]
  exact flatTailTimeShiftDirection_pairing_nonpos_of_mem_dualCone
    (d := d) (q := n + m) (j := Fin.natAdd n j) hξ
```

   The multi-gap positive sector is then:

```lean
private def positiveGapOrthant (q : ℕ) : Set (Fin q → ℝ) :=
  {u | ∀ j : Fin q, 0 ≤ u j}

private def absTimesOfTailGaps {q : ℕ} (u : Fin q → ℝ) : Fin q → ℝ :=
  fun i => ∑ j : Fin q, if j.val ≤ i.val then u j else 0

private theorem absTimesOfTailGaps_nonneg
    {q : ℕ} {u : Fin q → ℝ}
    (hu : u ∈ positiveGapOrthant q) :
    ∀ i : Fin q, 0 ≤ absTimesOfTailGaps u i := by
  intro i
  dsimp [absTimesOfTailGaps, positiveGapOrthant] at hu ⊢
  exact Finset.sum_nonneg (by
    intro j _
    by_cases hj : j.val ≤ i.val
    · simpa [hj] using hu j
    · simp [hj])

private noncomputable def absTimesOfTailGapsSplitLeft
    {n m : ℕ} (u : Fin (n + m) → ℝ) : Fin n → ℝ :=
  fun i => absTimesOfTailGaps u (Fin.castAdd m i)

private noncomputable def absTimesOfTailGapsSplitRight
    {n m : ℕ} (u : Fin (n + m) → ℝ) : Fin m → ℝ :=
  fun j => absTimesOfTailGaps u (Fin.natAdd n j)

private noncomputable def absTimesOfTailGapsSplitLeftRev
    {n m : ℕ} (u : Fin (n + m) → ℝ) : Fin n → ℝ :=
  fun i => absTimesOfTailGapsSplitLeft (n := n) (m := m) u (Fin.rev i)

private theorem absTimesOfTailGapsSplitLeft_nonneg
    {n m : ℕ} {u : Fin (n + m) → ℝ}
    (hu : u ∈ positiveGapOrthant (n + m)) :
    ∀ i : Fin n, 0 ≤ absTimesOfTailGapsSplitLeft (n := n) (m := m) u i := by
  intro i
  exact absTimesOfTailGaps_nonneg (q := n + m) hu (Fin.castAdd m i)

private theorem absTimesOfTailGapsSplitRight_nonneg
    {n m : ℕ} {u : Fin (n + m) → ℝ}
    (hu : u ∈ positiveGapOrthant (n + m)) :
    ∀ j : Fin m, 0 ≤ absTimesOfTailGapsSplitRight (n := n) (m := m) u j := by
  intro j
  exact absTimesOfTailGaps_nonneg (q := n + m) hu (Fin.natAdd n j)

private theorem absTimesOfTailGapsSplitLeftRev_nonneg
    {n m : ℕ} {u : Fin (n + m) → ℝ}
    (hu : u ∈ positiveGapOrthant (n + m)) :
    ∀ i : Fin n, 0 ≤ absTimesOfTailGapsSplitLeftRev (n := n) (m := m) u i := by
  intro i
  exact absTimesOfTailGapsSplitLeft_nonneg (n := n) (m := m) hu (Fin.rev i)

private def firstRightComponent {m : ℕ} (hm : 0 < m) : Fin m :=
  ⟨0, hm⟩

private def firstRightIndex {n m : ℕ} (hm : 0 < m) : Fin (n + m) :=
  ⟨n, Nat.lt_add_of_pos_right hm⟩
```

   Thus the global descent theorem must say "agreement on the positive
   tail-gap sector" rather than "agreement on arbitrary independent absolute
   time coordinates." This is stronger than needed for Section 4.3 in the
   right way: if `u ∈ positiveGapOrthant (n + m)`, then
   `absTimesOfTailGapsSplitLeft u`,
   `absTimesOfTailGapsSplitRight u`, and, when `φ.borchersConj` exposes the
   left factor, `absTimesOfTailGapsSplitLeftRev u` are all nonnegative. The
   local adapter receives its `hφ_nonneg` and `hψ_nonneg` hypotheses by these
   displayed cumulative-sum lemmas, not by support of the one-variable slices.

   The SCV support step required for the multi-gap theorem is a finite-dimensional
   version of the one-variable phase evaluation:

```lean
private theorem integral_tailGap_phase_mul_inverseFourierFlat_eq_eval
    {q : ℕ}
    (χ : SchwartzMap (Fin q → ℝ) ℂ)
    (lam : Fin q → ℝ) :
    ∫ u : Fin q → ℝ,
      Complex.exp (-(Complex.I *
        ((∑ j, (lam j : ℂ) * (u j : ℂ))))) *
        inverseFourierFlatCLM χ u =
      χ (fun j => -lam j / (2 * Real.pi))

private theorem integral_tailGap_phase_mul_inverseFourierFlat_eq_zero_of_eqOn_positiveGapOrthant
    {q : ℕ}
    (χ : SchwartzMap (Fin q → ℝ) ℂ)
    (hχ_zero :
      Set.EqOn (χ : (Fin q → ℝ) → ℂ) 0 (positiveGapOrthant q))
    {lam : Fin q → ℝ}
    (hlam : ∀ j : Fin q, lam j ≤ 0) :
    ∫ u : Fin q → ℝ,
      Complex.exp (-(Complex.I *
        ((∑ j, (lam j : ℂ) * (u j : ℂ))))) *
        inverseFourierFlatCLM χ u = 0 := by
  rw [integral_tailGap_phase_mul_inverseFourierFlat_eq_eval (χ := χ) lam]
  exact hχ_zero (fun j => -lam j / (2 * Real.pi)) (by
    intro j
    exact div_nonneg (by linarith [hlam j]) Real.two_pi_pos.le)
```

   Proof transcript for `integral_tailGap_phase_mul_inverseFourierFlat_eq_eval`:

   1. Put `p : Fin q → ℝ := fun j => -lam j / (2 * Real.pi)`.
   2. Transport `χ` to `EuclideanSpace ℝ (Fin q)` through
      `EuclideanSpace.equiv (Fin q) ℝ`, exactly as in the definition of
      `inverseFourierFlatCLM`.
   3. Use `FourierTransform.fourierInv_fourier_eq` for that transported
      Schwartz function, evaluated at the transported point `p`.
   4. Rewrite the inverse Fourier value by the multidimensional analogue of
      `fourierInv_eq_cexp_integral_local`:
      `FourierTransform.fourierInv φ p =
        ∫ u, Complex.exp (2 * Real.pi * Complex.I *
          (∑ j, (p j : ℂ) * (u j : ℂ))) * φ u`.
      If this helper is not already public, add it beside
      `inverseFourierFlatCLM` in `SCV/PaleyWienerSchwartz.lean`; it is a
      non-OS Fourier-normalization lemma.
   5. Show the exponent equality pointwise:
      `2 * Real.pi * Complex.I * ∑ j, (p j : ℂ) * (u j : ℂ)
        = -(Complex.I * ∑ j, (lam j : ℂ) * (u j : ℂ))`.
      This is `rw [Finset.mul_sum]` followed by the scalar identity
      `(2 * Real.pi) * (-lam j / (2 * Real.pi)) = -lam j`.
   6. Transport back through the same continuous linear equivalence; the
      result is the displayed flat integral equality.

   This avoids an invalid partition-of-unity argument over the complement of
   the orthant. The proof uses direct multivariable Fourier inversion with the
   Mathlib-convention flat transform `inverseFourierFlatCLM`: a test that is
   zero on the positive gap sector evaluates to zero at the frequency point
   forced by the dual-cone sign inequalities. Do not replace this by
   `physicsFourierFlatCLM`; that would introduce the wrong normalization for
   the gap-test side. The spacetime flattened Wightman test still uses
   `physicsFourierFlatCLM`, exactly as in the existing `Tflat` representation.

   Fubini padding correction. The axiom
   `schwartz_clm_fubini_exchange` requires the parameter space dimension to
   match the Schwartz-space dimension of `Tflat`. In the existing one-variable
   proof this is why the real variable is inserted as the first coordinate of
   a full `Fin M → ℝ` test and all remaining coordinates are integrated against
   `normedUnitBumpSchwartzPi`. The multi-tail-gap proof must do the same for
   `q := n + m` gap variables inside
   `M := (n + m) * (d + 1)` flattened spacetime variables.

   Required padding helper:

```lean
private noncomputable def tailGapPadSchwartz
    {q M : ℕ} (h : q ≤ M)
    (χ : SchwartzMap (Fin q → ℝ) ℂ) :
    SchwartzMap (Fin M → ℝ) ℂ :=
  OSReconstruction.reindexSchwartzFin (Nat.add_sub_of_le h)
    (χ.tensorProduct (normedUnitBumpSchwartzPi (M - q)))

private theorem tailGapPadSchwartz_apply
    {q M : ℕ} (h : q ≤ M)
    (χ : SchwartzMap (Fin q → ℝ) ℂ)
    (x : Fin M → ℝ) :
    tailGapPadSchwartz h χ x =
      χ (fun j : Fin q =>
          ((OSReconstruction.castFinCLE (Nat.add_sub_of_le h).symm) x)
            (Fin.castAdd (M - q) j)) *
        normedUnitBumpSchwartzPi (M - q)
          (fun k : Fin (M - q) =>
            ((OSReconstruction.castFinCLE (Nat.add_sub_of_le h).symm) x)
              (Fin.natAdd q k)) := by
  simp [tailGapPadSchwartz, OSReconstruction.reindexSchwartzFin_apply,
    SchwartzMap.tensorProduct_apply]

private theorem tailGapPadSchwartz_integral
    {q M : ℕ} (h : q ≤ M)
    (χ : SchwartzMap (Fin q → ℝ) ℂ)
    (P : (Fin q → ℝ) → ℂ) :
    (∫ x : Fin M → ℝ,
      P (fun j : Fin q => x (Fin.castLE h j)) *
        tailGapPadSchwartz h χ x) =
      ∫ u : Fin q → ℝ, P u * χ u
```

   Proof transcript for `tailGapPadSchwartz_integral`:

   1. Change variables by `integral_comp_castFinCLE_eq` with
      `(Nat.add_sub_of_le h).symm`, reducing the left integral to
      `Fin (q + (M-q)) → ℝ`.
   2. Apply `OSReconstruction.integral_fin_add_split q (M - q)` from
      `GeneralResults/FinProductIntegral.lean`.
   3. Use `tailGapPadSchwartz_apply` and the definitions of `Fin.castAdd` and
      `Fin.natAdd` to rewrite the split integrand as
      `(P u * χ u) * normedUnitBumpSchwartzPi (M - q) v`.
   4. Apply `MeasureTheory.integral_prod_mul`.
   5. Rewrite `∫ v, normedUnitBumpSchwartzPi (M - q) v` by
      `integral_normedUnitBumpSchwartzPi`, then close by `ring`.
   6. No support or QFT input is used in this helper. If Lean does not solve
      the reindexing by `simp`, copy the existing `hPair_repr` proof in
      `integral_bvt_W_flattened_translate_mul_fourierTransform_eq_zero_of_negSupport`
      with `integral_fin_add_split q (M - q)` replacing
      `integral_finSucc_cons_eq`.

   The same helper is used twice in the `hΦ_vanish` proof: once to identify
   the padded `Tflat` pairing integral with the genuine `q`-gap pairing, and
   once pointwise to rewrite the Fubini-exchanged `Φ ξ` as the `q`-gap phase
   integral evaluated by
   `integral_tailGap_phase_mul_inverseFourierFlat_eq_zero_of_eqOn_positiveGapOrthant`.

   Implementation-location guard. The flattened witness
   `exists_flattened_bvt_W_dualCone_distribution` is currently private to
   `OSToWightmanBoundaryValueLimits.lean`. The existing right-block theorem
   `integral_bvt_W_flattened_translate_mul_fourierTransform_eq_zero_of_negSupport`
   is the one-variable special case and is a proof pattern, not the correct
   primitive for the global Section-4.3 descent: the global theorem must
   translate the full flattened `(n + m)`-point test along all cumulative
   tail-gap directions. Therefore the tail-gap support theorem that needs
   direct access to the full `Tflat` witness must be proved/exported from
   `OSToWightmanBoundaryValueLimits.lean` (or from a small support companion
   that deliberately exposes a public, non-wrapper theorem).
   `OSToWightmanPositivity.lean` should consume only the resulting public
   tail-gap pairing/descent statement; it must not duplicate the `Tflat`
   reconstruction or attempt to rely on a private theorem from another module.

   Full flattened orbit. This is the public BVLimits theorem surface that
   should replace the schematic "global support" placeholder:

```lean
private noncomputable def flatTailGapOrbit (d q : ℕ)
    (u : Fin q → ℝ) : Fin (q * (d + 1)) → ℝ :=
  ∑ j : Fin q, u j • flatTailTimeShiftDirection d q j

private theorem flatTailGapOrbit_pairing_nonpos_of_mem_dualCone
    {q : ℕ} (u : Fin q → ℝ)
    (hu : u ∈ positiveGapOrthant q)
    {ξ : Fin (q * (d + 1)) → ℝ}
    (hξ :
      ξ ∈ DualConeFlat ((flattenCLEquivReal q (d + 1)) '' ForwardConeAbs d q)) :
    ∑ a, flatTailGapOrbit d q u a * ξ a ≤ 0 := by
  calc
    ∑ a, flatTailGapOrbit d q u a * ξ a
        = ∑ j : Fin q,
            u j * (∑ a, flatTailTimeShiftDirection d q j a * ξ a) := by
            simp [flatTailGapOrbit, Finset.mul_sum, Finset.sum_mul,
              Pi.smul_apply, mul_assoc, mul_left_comm, mul_comm]
    _ ≤ 0 := by
        exact Finset.sum_nonpos (by
          intro j _
          have huj : 0 ≤ u j := by
            simpa [positiveGapOrthant] using hu j
          exact mul_nonpos_of_nonneg_of_nonpos huj
            (flatTailTimeShiftDirection_pairing_nonpos_of_mem_dualCone
              (d := d) (q := q) j hξ))

theorem bvt_W_flattened_tailGapOrbit_pairing_eq_of_eqOn_positiveGapOrthant
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {q : ℕ}
    (Ψ : SchwartzMap (Fin (q * (d + 1)) → ℝ) ℂ)
    {χ₁ χ₂ : SchwartzMap (Fin q → ℝ) ℂ}
    (hχ :
      Set.EqOn (χ₁ : (Fin q → ℝ) → ℂ) χ₂ (positiveGapOrthant q)) :
    (∫ u : Fin q → ℝ,
      bvt_W OS lgc q
          (unflattenSchwartzNPoint (d := d)
            (SCV.translateSchwartz (flatTailGapOrbit d q u) Ψ)) *
        inverseFourierFlatCLM χ₁ u) =
    (∫ u : Fin q → ℝ,
      bvt_W OS lgc q
          (unflattenSchwartzNPoint (d := d)
            (SCV.translateSchwartz (flatTailGapOrbit d q u) Ψ)) *
        inverseFourierFlatCLM χ₂ u)
```

   Proof transcript for
   `bvt_W_flattened_tailGapOrbit_pairing_eq_of_eqOn_positiveGapOrthant`:

   1. Set `χ := χ₁ - χ₂`. From `hχ`, derive
      `hχ_zero : Set.EqOn (χ : (Fin q → ℝ) → ℂ) 0 (positiveGapOrthant q)`
      by pointwise subtraction.
   2. By linearity of `inverseFourierFlatCLM` and `MeasureTheory.integral_sub`
      reduce the equality to the zero statement for `χ`.
   3. Obtain `⟨Tflat, hTflat_supp, hTflat_repr⟩` from
      `exists_flattened_bvt_W_dualCone_distribution (d := d) OS lgc q`.
      Do not use the right-block witness here; it cannot move the left frozen
      times.
   4. Let `M := q * (d + 1)` and prove `hqM : q ≤ M` by `nlinarith`/`omega`
      from `Nat.succ_pos d`. Define
      `ψgap := inverseFourierFlatCLM χ` and
      `fpad := tailGapPadSchwartz hqM ψgap`.
   5. Define the Fubini family
      `gFamily : (Fin M → ℝ) → SchwartzMap (Fin M → ℝ) ℂ` by
      `gFamily x =
        physicsFourierFlatCLM
          (SCV.translateSchwartz
            (flatTailGapOrbit d q
              (fun j : Fin q => x (Fin.castLE hqM j))) Ψ)`.
      The continuity and seminorm-growth helpers are direct multi-parameter
      analogues of
      `continuous_physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift`
      and
      `exists_bound_seminorm_physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift`,
      with `flatTailGapOrbit` a continuous finite linear map
      `(Fin q → ℝ) →L[ℝ] (Fin M → ℝ)`.
   6. Apply `schwartz_clm_fubini_exchange Tflat gFamily fpad` to obtain
      `Φ`, `hΦ_eval`, and `hΦ_pair`.
   7. Use `hTflat_repr` and `tailGapPadSchwartz_integral` to identify
      `∫ x, Tflat (gFamily x) * fpad x` with the desired gap integral.
   8. To prove `Φ` vanishes on the dual cone, fix
      `ξ ∈ DualConeFlat ((flattenCLEquivReal q (d + 1)) '' ForwardConeAbs d q)`.
      Set
      `lam ξ j := ∑ a, flatTailTimeShiftDirection d q j a * ξ a`.
      The sign lemma gives `∀ j, lam ξ j ≤ 0`.
   9. Rewrite the translated orbit by the full-tail version of
      `physicsFourierFlatCLM_translateSchwartz_apply`; the phase is
      `Complex.exp (-(Complex.I * ∑ j, (lam ξ j : ℂ) * (u j : ℂ)))`.
      Remove the padded dummy variables by `tailGapPadSchwartz_integral`.
   10. Apply
      `integral_tailGap_phase_mul_inverseFourierFlat_eq_zero_of_eqOn_positiveGapOrthant`
      with `hχ_zero` and `lam ξ`.
   11. Feed the resulting `hΦ_vanish` into `hTflat_supp` exactly as in
      `integral_bvt_W_flattened_translate_mul_fourierTransform_eq_zero_of_negSupport`,
      then convert `Tflat Φ = 0` back to the gap integral using `hΦ_pair`.

   The production proof pattern for the public BVLimits theorem is the
   compiled one-variable proof
   `integral_bvt_W_flattened_translate_mul_fourierTransform_eq_zero_of_negSupport`,
   with three deliberate changes:

   1. obtain `Tflat` from the full
      `exists_flattened_bvt_W_dualCone_distribution (d := d) OS lgc q`;
   2. use `flatTailGapOrbit d q u` instead of the right-block
      `zeroHeadBlockShift (t • flatTimeShiftDirection d m)`;
   3. pad `inverseFourierFlatCLM χ`, not a physics-convention Fourier
      transform, because the finite gap variable is evaluated by
      `integral_tailGap_phase_mul_inverseFourierFlat_eq_eval`.

   For the current finite-height proof, do **not** add a new wrapper named
   `unshifted_global_tailGap_quotient_descent_of_section43Transport` unless it
   constructs the exact expanded kernels and their EqOn proof. The reusable
   theorem is the BVLimits theorem above. The Positivity proof should call it
   directly after the shell/Paley-Wiener expansion has produced the following
   exact normal-form data:

```lean
private theorem
    finiteHeight_expanded_tailGap_descent_instantiation
    {n m : ℕ}
    {φ : SchwartzNPoint d n} {ψ : SchwartzNPoint d m}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    {g : euclideanPositiveTimeSubmodule (d := d) m}
    (Ψ : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ)
    (χAmbient χTransport :
      SchwartzMap (Fin (n + m) → ℝ) ℂ)
    (hχ :
      Set.EqOn
        (χAmbient : (Fin (n + m) → ℝ) → ℂ)
        χTransport
        (positiveGapOrthant (n + m))) :
    (∫ u : Fin (n + m) → ℝ,
      bvt_W OS lgc (n + m)
          (unflattenSchwartzNPoint (d := d)
            (SCV.translateSchwartz
              (flatTailGapOrbit d (n + m) u) Ψ)) *
        inverseFourierFlatCLM χAmbient u) =
    (∫ u : Fin (n + m) → ℝ,
      bvt_W OS lgc (n + m)
          (unflattenSchwartzNPoint (d := d)
            (SCV.translateSchwartz
              (flatTailGapOrbit d (n + m) u) Ψ)) *
        inverseFourierFlatCLM χTransport u) := by
  exact
    bvt_W_flattened_tailGapOrbit_pairing_eq_of_eqOn_positiveGapOrthant
      (d := d) (OS := OS) (lgc := lgc) (Ψ := Ψ) hχ
```

   Required BVLimits side helpers for this theorem:

```lean
private theorem translateSchwartz_add
    {M : ℕ} (a b : Fin M → ℝ)
    (Ψ : SchwartzMap (Fin M → ℝ) ℂ) :
    SCV.translateSchwartz (a + b) Ψ =
      SCV.translateSchwartz a (SCV.translateSchwartz b Ψ) := by
  ext x
  simp [SCV.translateSchwartz_apply, Pi.add_apply, add_assoc]

private theorem continuous_translateSchwartz_flatTailGapOrbit
    {q : ℕ}
    (Ψ : SchwartzMap (Fin (q * (d + 1)) → ℝ) ℂ) :
    Continuous (fun u : Fin q → ℝ =>
      SCV.translateSchwartz (flatTailGapOrbit d q u) Ψ)

private theorem continuous_physicsFourierFlatCLM_translate_flatTailGapOrbit
    {q : ℕ}
    (Ψ : SchwartzMap (Fin (q * (d + 1)) → ℝ) ℂ) :
    Continuous (fun u : Fin q → ℝ =>
      physicsFourierFlatCLM
        (SCV.translateSchwartz (flatTailGapOrbit d q u) Ψ)) := by
  exact physicsFourierFlatCLM.continuous.comp
    (continuous_translateSchwartz_flatTailGapOrbit (d := d) Ψ)

private theorem norm_flatTailGapOrbit_le
    {q : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : Fin q → ℝ, ‖flatTailGapOrbit d q u‖ ≤ C * ‖u‖

private theorem exists_bound_seminorm_physicsFourierFlatCLM_translate_flatTailGapOrbit
    {q : ℕ}
    (Ψ : SchwartzMap (Fin (q * (d + 1)) → ℝ) ℂ)
    (k l : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧
      ∀ u : Fin q → ℝ,
        SchwartzMap.seminorm ℝ k l
          (physicsFourierFlatCLM
            (SCV.translateSchwartz (flatTailGapOrbit d q u) Ψ)) ≤
          C * (1 + ‖u‖) ^ N
```

   Proof transcript for these side helpers:

   1. `translateSchwartz_add` is an `ext x; simp` proof from
      `SCV.translateSchwartz_apply`.
   2. Prove `continuous_translateSchwartz_flatTailGapOrbit` by induction on
      the finite index set `Fin q`. Write
      `flatTailGapOrbit d q u` as the finite sum of
      `u j • flatTailTimeShiftDirection d q j`, use
      `continuous_translateSchwartz_smul_local` for each coordinate function
      `fun u => u j`, and compose with `translateSchwartz_add`.
   3. `continuous_physicsFourierFlatCLM_translate_flatTailGapOrbit` is the
      displayed one-line composition with the continuous linear map
      `physicsFourierFlatCLM`.
   4. Prove `norm_flatTailGapOrbit_le` by
      `‖∑ j, u j • v j‖ ≤ ∑ j, |u j| * ‖v j‖`, then bound every
      `|u j|` by `‖u‖` with `norm_le_pi_norm`; take
      `C := ∑ j, ‖flatTailTimeShiftDirection d q j‖`.
   5. Prove the seminorm growth helper by copying
      `exists_bound_seminorm_physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift`
      with `η` replaced by `flatTailGapOrbit d q u`. The only changed estimate
      is
      `1 + ‖flatTailGapOrbit d q u‖ ≤ (1 + C) * (1 + ‖u‖)`,
      which follows from `norm_flatTailGapOrbit_le`; all remaining
      `Seminorm.bound_of_continuous`, `SCV.seminorm_translateSchwartz_le`,
      finite-sup, and constant-absorption lines are identical.

   Here `finiteHeight_expanded_tailGap_descent_instantiation` is a documentation
   name only and should now be treated as a special-case lemma, not as the live
   hard-theorem gate. In production, the hard theorem should instead construct
   the concrete full Fourier-side kernels `KAmbient` and `KTransport` from:

   1. `partialFourierSpatial_fun_eq_integral`;
   2. the public Paley-Wiener kernel formula `psiZ_twoPi_pairing_formula`;
   3. the flatten/reindex/tensor rewrite to the full `Tflat` surface.

   The EqOn proof for the concrete kernels is no longer schematic. For
   `u ∈ positiveGapOrthant (n + m)`, set

```lean
let tabs : Fin (n + m) → ℝ := absTimesOfTailGaps u
let tφ : Fin n → ℝ := absTimesOfTailGapsSplitLeft (n := n) (m := m) u
let tψ : Fin m → ℝ := absTimesOfTailGapsSplitRight (n := n) (m := m) u
```

   Then

```lean
have htabs_nonneg : ∀ i : Fin (n + m), 0 ≤ tabs i :=
  absTimesOfTailGaps_nonneg (q := n + m) hu
have hφ_nonneg : ∀ i : Fin n, 0 ≤ tφ i :=
  absTimesOfTailGapsSplitLeft_nonneg (n := n) (m := m) hu
have hψ_nonneg : ∀ j : Fin m, 0 ≤ tψ j :=
  absTimesOfTailGapsSplitRight_nonneg (n := n) (m := m) hu
```

   These are the exact hypotheses needed to call
   `partialFourierSpatial_fun_eq_of_eqOn_section43PositiveEnergyRegion`,
   `partialFourierSpatial_timeSlice_eqOn_nonneg_of_repr_eq_transport`, or the
   already-packaged scalar slice lemmas. This is where the Section-4.3
   hypotheses `hφf` and `hψg` enter. They do **not** enter the BVLimits
   support theorem.

   Left-factor reversal guard. If the expanded normal form exposes the left
   Wightman factor as `φ.borchersConj`, the Section-4.3 EqOn proof is applied
   to `φ` after the `Fin.rev` argument reversal from
   `SchwartzMap.borchersConj_apply`. The required nonnegative vector is
   `absTimesOfTailGapsSplitLeftRev (n := n) (m := m) u`, with proof
   `absTimesOfTailGapsSplitLeftRev_nonneg (n := n) (m := m) hu`.
   Do not change the positive tail-gap
   theorem for this: reversal is a local left-factor bookkeeping step in the
   Positivity instantiation, not part of the BVLimits support theorem.

   The global support theorem is a necessary mathematical blocker for
   implementation readiness, but it is no longer sufficient by itself. It
   handles the unshifted Section-4.3 descent inside the expanded normal form;
   the shifted right factor still has to be handled by the separate
   positive-support time-shift distribution theorem recorded in the `hPsi`
   section below. This is a real theorem, not a wrapper: it is precisely the
   missing bridge from Section-4.3 equality on the full positive-energy region
   to the unshifted integrated time/spatial Fourier pairing used after the
   Paley-Wiener expansion.
8. Use `schwartz_clm_fubini_exchange` only after the mandatory `Fin 1`
   adapter above:

```lean
obtain ⟨Φ1, hΦ1_point, hΦ1_apply⟩ :=
  schwartz_clm_fubini_exchange
    (m := 1) T1 g1 f1
    (continuous_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal hε)
    (seminorm_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal_growth hε)
```

   Then rewrite `hΦ1_apply` by `h_outer_real`. Do not use `hTW` in this Fubini
   call; `hTW` is reserved for the Section-4.3 quotient descent on the
   original real-line functional `TW`. If Lean exposes a side goal not literally
   discharged by the two displayed side helpers, record the exact side goal
   here before adding another helper.
9. The scalar kernel identity inside the Fubini proof uses the public
   Paley-Wiener `ψ_Z` pairing formula already available in
   [SCV/PaleyWiener.lean](/Users/xiyin/OSReconstruction/OSReconstruction/SCV/PaleyWiener.lean):

```lean
theorem psiZ_twoPi_pairing_formula
    (φ : SchwartzMap ℝ ℂ) (η ξ : ℝ) :
    ∫ x : ℝ,
      SCV.psiZ ((2 * Real.pi : ℂ) * (x + η * Complex.I)) ξ * φ x =
        SCV.smoothCutoff ξ *
          Complex.exp (-(2 * Real.pi * η : ℂ) * ξ) *
          FourierTransform.fourierInv φ ξ
```

   This is a kernel formula, not an OS/Wightman comparison theorem. It may be
   proved by renaming the existing private theorem or by a short public wrapper
   in the same file if namespace/export constraints require it.
10. After the two slice replacements and the `ψ_Z` kernel computation, the
   remaining one-variable upper-half-plane value is exactly the Section-4.3
   class of `ψZxε x`; use `section43_iteratedSlice_descendedPairing` only at
   this final one-variable stage, with `hw` proved by `by simpa using hε`.

This gate changes the readiness status for the older Section-4.3 finite-height
draft: the two `Fin 1` side helpers are now Lean-ready, the coordinate policy
for the frozen slices is fixed, and the zero-left branch is documented.

2026-04-13 correction after the horizontal scalar computation:
the raw canonical-shell/horizontal dual-cone EqOn target is **withdrawn as an
active implementation target**. The checked horizontal scalar has the damping
factor

```lean
base ξ *
  Complex.exp ((ε : ℂ) * (lam ξ : ℂ)) *
  Complex.exp ((t : ℂ) * (lam ξ : ℂ))
```

where `lam ξ` is the zero-head right-time-shift pairing. The positive-height
canonical shell, however, uses `xiShift ... (t : ℂ)` as a real tube shift and
the canonical imaginary direction `ε • canonicalForwardConeDirection`. On the
dual cone its pointwise exponential has the schematic scalar

```lean
base ξ *
  Complex.exp (-(ε : ℂ) * ηCanonicalPair ξ) *
  Complex.exp (-(Complex.I * (t : ℂ) * (lam ξ : ℂ)))
```

up to the already-fixed sign convention
`lam ξ = - tailTimePair ξ`. These two scalars are not equal on the full dual
cone: the shell has an oscillatory real-time factor, while the horizontal
imaginary-axis witness has Laplace damping. Therefore an arbitrary-`φ,ψ`
theorem named

```lean
canonicalShell_horizontal_kernel_eqOn_dualCone
```

would prove the false generic identity between real-time Wightman values and
positive-imaginary-axis Laplace values. Do not implement it, and do not use the
horizontal `KHorizontal` packet to prove a zero residual for arbitrary
ambient representatives.

The sound live implementation order is instead:

1. keep the already-checked canonical shell tube/Fubini package as a diagnostic
   and as support for the actual shell limit;
2. keep the already-checked horizontal Paley/Fubini package as the canonical
   Wightman witness normal form;
3. prove the Section-4.3 transported scalar bridge with hypotheses `hφf` and
   `hψg`;
4. use that transported bridge to supply the `hlimit` hypothesis of
   `kernel_eq_of_tendsto_bvt_F_canonical_xiShift_to_osHolomorphicValue_on_positiveReals`
   or the upper-half-plane witness variant;
5. use the existing `lemma42_matrix_element_time_interchange` consumer.

The raw transport/cutoff packet
`zSplit_mem_forwardTube_of_osConjTensorProduct_support`,
`exists_transportTubeCutoff`,
`exists_transportKernel_pairing_singleSplitXiShiftScalar`, and
`hardSingleSplit_psiZ_timeShift_expands_to_dualCone_eq_kernel_pairing` is
retired for the current route. Do not implement or consume it unless a separate
future correction supplies a valid tube representative.

These theorem transcripts replace the earlier unspecified "same-`Ψ`" and
"put into `χAmbient`/`χTransport`" gates. Production Lean should follow this
order and stop only on concrete compiler goals, not on a missing mathematical
blueprint.

Proof transcript for the finite-height theorem:

1. Let `hNF` be
   `bvt_F_canonical_xiShift_shell_eq_integrated_descendedPsiZ_of_section43Transport`
   at `t ε ht hε`.
2. For each `x`, rewrite the descended pairing in the right side of `hNF` by
   `OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D_apply`.
3. Rewrite `TW ((SchwartzMap.fourierTransformCLM ℂ) (ψZxε x))` by
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply`.
4. Use `MeasureTheory.integral_congr_ae` for the outer `x` integral and `simpa`
   with the local abbreviations `ψZt`, `ψZxε`, `TW`, and `hTW`.
5. Convert the equality of the two non-subtracted scalars to the displayed
   subtractive statement with `sub_eq_zero.mpr`.

The limit-level theorem consumed by the existing shell-minus-horizontal
eventual-normal-form lemma is now formal from the finite-height theorem. Its
displayed function is exactly the guarded iterated residual already exposed by
production Lean.

```lean
private theorem
    tendsto_bvt_F_canonical_xiShift_section43Transport_iterated_residual_zero
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t : ℝ} (ht : 0 < t) :
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y) -
        if hε : 0 < ε then
          ∫ x : ℝ,
            (∫ τ : ℝ,
              bvt_W OS lgc (n + m)
                (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
              (SchwartzMap.fourierTransformCLM ℂ
                (SCV.schwartzPsiZ
                  ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
                  (by
                    have hscaled : 0 < (2 * Real.pi) *
                        (((x : ℂ) + ε * Complex.I).im) :=
                      mul_pos Real.two_pi_pos (by simpa using hε)
                    simpa [Complex.mul_im] using hscaled))) τ) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x
        else
          0)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0)
```

Proof transcript:

1. Prove eventual equality of the displayed guarded residual with the constant
   zero function. Use `filter_upwards [self_mem_nhdsWithin] with ε hε`.
2. Under the filter, rewrite the guard by `rw [dif_pos hε]`.
3. Apply
   `bvt_F_canonical_xiShift_shell_sub_iterated_fourierLaplaceIntegral_eq_zero_of_section43Transport`
   at the same `t ε ht hε`.
4. Close the `Tendsto` goal by
   `Filter.Tendsto.congr' hEventuallyZero tendsto_const_nhds`.
5. No dominated-convergence or limit-interchange theorem is used at this stage;
   all analytic content is confined to the finite-height normal-form helper
   above.

Now the actual shell-minus-horizontal theorem is formal:

```lean
private theorem
    tendsto_bvt_F_canonical_xiShift_shell_sub_horizontal_to_zero_of_section43Transport
    -- same hypotheses as above
```

Proof transcript:

1. Use
   `bvt_F_canonical_xiShift_shell_sub_horizontal_eventually_eq_shell_sub_iterated_fourierLaplaceIntegral`
   to replace the shell-minus-horizontal function by the guarded iterated
   residual on `nhdsWithin 0 (Set.Ioi 0)`.
2. Apply
   `tendsto_bvt_F_canonical_xiShift_section43Transport_iterated_residual_zero`.
3. Close by `Filter.Tendsto.congr'`.

Finally, the pointwise transported `ψ_Z` bridge is downstream rather than
first-order proof work. Combine
`tendsto_bvt_F_canonical_xiShift_section43Transport_iterated_residual_zero`
with the existing production theorem

```lean
tendsto_bvt_F_canonical_xiShift_shell_sub_horizontal_to_timeShift_sub_canonicalExtension
```

and `tendsto_nhds_unique` to prove
`bvt_W_timeShift_eq_descendedPsiZ_of_section43Transport`. This is the only
place where the pointwise equality is introduced; it is never proved by an
implicit delta/evaluation functional.

Concrete source anchors for the preferred limit-level route:

1. configuration-space shell rewrite:
   `bvt_F_canonical_conjTensorProduct_timeShift_eq_xiShift` and
   `tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue`;
2. canonical horizontal normal form:
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_horizontal_eq_fourierLaplaceIntegral` and
   `integral_bvt_W_conjTensorProduct_timeShiftCanonicalExtension_horizontal_eq_iterated_fourierLaplaceIntegral`;
3. Fubini/CLM exchange source:
   `schwartz_clm_fubini_exchange`, but only through the displayed `Fin 1`
   adapter `T1`, `f1`, `g1`, `h_outer_real`, and the two exact
   continuity/growth helpers
   `continuous_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal` and
   `seminorm_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal_growth`;
4. one-variable slice transport:
   `partialFourierSpatial_timeSlice_eqOn_nonneg_of_repr_eq_transport`,
   `fourierPairingDescendsToSection43PositiveEnergy1D_eq_of_repr_eq_transport`,
   and the two `fourierInvPairingCLM...sub_eq_zero...` lemmas;
5. OS I Section-8 time interchange:
   the production one-variable Paley-Wiener/Laplace ingredients
   `complexLaplaceTransform_hasPaleyWienerExtension`,
   `fourierLaplaceExt_partialFourierSpatial_timeSlice_eq_complexLaplaceTransform`,
   `partialFourierSpatial_timeSliceCanonicalExtension_imagAxis_eq_fourierPairingDescendsToSection43PositiveEnergy1D_psiZ`,
   and `SCV.psiZ_eq_exp_of_nonneg`.
6. Shift handling source:
   the shift is handled only at the level of the real-time distribution paired
   with `(SchwartzMap.fourierTransformCLM ℂ) ψ_Z`. The proof must use the
   Paley-Wiener `ψ_Z` kernel formula and positive-support distribution
   interchange before applying unshifted Section-4.3 slice descent. It must not
   infer any equality of shifted representatives from `hψg`.

The route choice in this older subsection is retained only for the separate
Section-4.3 OS-identification work. It is no longer the live shell-to-Laplace
blocker. For the shell-to-Laplace seam, production implementation must follow
the corrected canonical positive-height shell packet in §5.9.4a.1.ε. In
particular, do not attempt the raw `singleSplit` transport/cutoff packet, and
do not reopen the pointwise/evaluation-normal-form route unless this
subsection is rewritten with an explicit approximate-identity theorem.

The equality form consumed by the shell-limit theorem is formal:

```lean
private theorem
    bvt_W_timeShift_eq_descendedPsiZ_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g) :
    ∀ t : ℝ, ∀ ht : 0 < t,
      bvt_W OS lgc (n + m)
        (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
          (d := d) OS lgc φ ψ hψ_compact)
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm φ ψ hψ_compact)
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (t * Complex.I)))
            (by
              simpa [Complex.mul_im, ht.ne']
                using mul_pos Real.two_pi_pos ht)))
```

Proof transcript for the equality form:

1. Fix `t ht`.
2. Let `hZero` be
   `tendsto_bvt_F_canonical_xiShift_shell_sub_horizontal_to_zero_of_section43Transport`
   at `t ht`.
3. Let `hResidual` be the already-proved obstruction-limit theorem
   `tendsto_bvt_F_canonical_xiShift_shell_sub_horizontal_to_timeShift_sub_canonicalExtension`
   at the same `t ht`.
4. Use `tendsto_nhds_unique hResidual hZero` to obtain
   `bvt_W OS lgc (n + m)
      (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) =
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension
      (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I)`.
5. Rewrite the canonical imag-axis value with
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imagAxis_eq_fourierPairingDescendsToSection43PositiveEnergy1D_psiZ`.
6. Close by `simpa` with the local `ψZt` abbreviation. This theorem is
   downstream of the zero residual; it does not prove a pointwise scalar normal
   form directly.

The pointwise transported `singleSplit` scalar bridge is downstream of both the
descended-`ψ_Z` theorem and the `hPsi` spectral identification:

```lean
private theorem
    bvt_W_timeShift_eq_singleSplitXiShiftScalar_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t : ℝ} (ht : 0 < t) :
    bvt_W OS lgc (n + m)
      (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) =
    bvtSingleSplitXiShiftScalar (d := d) OS lgc hm f.1 g.1 t
```

Proof transcript for the downstream `singleSplit` scalar bridge:

1. Rewrite the left side by
   `bvt_W_timeShift_eq_descendedPsiZ_of_section43Transport`.
2. Rewrite the descended `ψ_Z` pairing by
   `descendedPsiZ_boundaryValue_eq_osSpectral_of_section43Transport`.
3. Rewrite the spectral boundary value by
   `selfAdjointSpectralBoundaryValueOffdiag_eq_selfAdjointSpectralLaplaceOffdiag_psiZ`
   and then
   `OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag`.
4. Rewrite the OS holomorphic value by
   `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single`.
5. Rewrite the resulting `singleSplit` value with
   `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`.

After the shell-minus-horizontal zero residual has supplied
`bvt_W_timeShift_eq_descendedPsiZ_of_section43Transport`, the shell-limit
theorem needed by `lemma42_matrix_element_time_interchange` is direct assembly:

```lean
private theorem
    tendsto_bvt_F_canonical_xiShift_to_canonicalExtension_imagAxis_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g) :
    ∀ t : ℝ, 0 < t →
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  ↑(y k μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ)) *
              (φ.conjTensorProduct ψ) y)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I)))
```

Proof transcript for the direct shell-limit theorem:

1. For fixed `t ht`, let `hShell` be
   `tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue`
   specialized to `φ ψ t`.
2. Let `hDesc` be
   `bvt_W_timeShift_eq_descendedPsiZ_of_section43Transport` at `t ht`.
3. Let `hCanon` be
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imagAxis_eq_fourierPairingDescendsToSection43PositiveEnergy1D_psiZ`
   specialized to `φ ψ hψ_compact ht`.
4. Rewrite the target of `hShell` first by `hDesc`, then by `hCanon.symm`.
5. Close with `simpa`. This theorem itself is formal; the shell-minus-
   horizontal content is isolated entirely in the preceding zero-residual
   theorem.

The zero-residual `Tendsto` theorem toward the positive-time `singleSplit`
scalar is downstream diagnostic/assembly work. It is formal after the
`singleSplit` scalar bridge above, not the first implementation target:

```lean
private theorem
    tendsto_bvtCanonicalXiShiftShell_sub_singleSplitXiShiftScalar_zero_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto
      (fun ε : ℝ =>
        bvtCanonicalXiShiftShell (d := d) OS lgc hm φ ψ t ε -
          bvtSingleSplitXiShiftScalar (d := d) OS lgc hm f.1 g.1 t)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0)
```

The displayed `tendsto_bvt_F_canonical_xiShift_to_singleSplitXiShift_of_section43Transport`
is then formal:

1. Let `hzero` be
   `tendsto_bvtCanonicalXiShiftShell_sub_singleSplitXiShiftScalar_zero_of_section43Transport`.
2. Let `hconst` be `tendsto_const_nhds` for
   `bvtSingleSplitXiShiftScalar (d := d) OS lgc hm f.1 g.1 t`.
3. Use `hzero.add hconst`, then `simpa [bvtCanonicalXiShiftShell,
   bvtSingleSplitXiShiftScalar, sub_eq_add_neg, add_comm, add_left_comm,
   add_assoc]`.

Proof transcript for the zero-residual theorem:

1. Let `hShell` be
   `tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue`
   specialized to `φ ψ t`.
2. Let `hScalar` be
   `bvt_W_timeShift_eq_singleSplitXiShiftScalar_of_section43Transport` at
   `t ht`.
3. Rewrite the target of `hShell` by `hScalar`, obtaining convergence of the
   source function `bvtCanonicalXiShiftShell (d := d) OS lgc hm φ ψ t` to the
   scalar `bvtSingleSplitXiShiftScalar (d := d) OS lgc hm f.1 g.1 t`.
4. Subtract the constant target with `hShell'.sub tendsto_const_nhds`.
5. Close by `simpa [bvtCanonicalXiShiftShell, bvtSingleSplitXiShiftScalar]`.

Paper and code dependency inventory for the finite-height normal-form helper
`bvt_F_canonical_xiShift_shell_eq_integrated_descendedPsiZ_of_section43Transport`:

1. Paper target:
   OS I Lemma 4.2, specifically the passage from `(4.23)` to `(4.24)` on p. 96.
   The spatial variables are handled by the existing
   `partialFourierSpatial_fun` / `partialFourierSpatial_timeSliceSchwartz`
   normal forms and the `fourierInvPairingCLM` slice-pairing lemmas listed
   below. The time variable is the one-variable positive-support boundary
   theorem cited there as Lemma 8.4. The current proof uses the OS-II
   correction only through the already-built `OSLinearGrowthCondition` /
   boundary-value construction; it must not invoke the false many-variable
   OS-I Lemma 8.8.
2. Wightman time-shift functional expansion and support:
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply` and
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport`
   in `OSToWightmanBoundaryValueLimits.lean`.
3. One-variable quotient descent:
   `section43PositiveEnergyQuotientMap1D_eq_of_eqOn_nonneg` and
   `fourierPairingDescendsToSection43PositiveEnergy1D_apply` in
   `Section43Codomain.lean`.
4. Ambient-to-preimage slice bridge:
   `partialFourierSpatial_timeSlice_eqOn_nonneg_of_repr_eq_transport`,
   `section43PositiveEnergyQuotientMap1D_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`,
   and
   `fourierPairingDescendsToSection43PositiveEnergy1D_eq_of_repr_eq_transport`
   in `OSToWightmanPositivity.lean`.
5. Scalar slice-pairing bridge:
   `fourierInvPairingCLM_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`,
   `fourierInvPairingCLM_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport`,
   `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`,
   and
   `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport`
   in `OSToWightmanPositivity.lean`.
6. Positive-support facts for slices:
   `tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime`,
   `partialFourierSpatial_timeSliceTest`, and
   `fourierInvPairing_hasOneSidedFourierSupport` in
   `OSToWightmanPositivity.lean`.
7. One-variable analytic and canonical-slice comparison used after quotient
   rewriting:
   `complexLaplaceTransform_hasPaleyWienerExtension`,
   `fourierLaplaceExt_partialFourierSpatial_timeSlice_eq_complexLaplaceTransform`,
   `partialFourierSpatial_timeSliceCanonicalExtension_imagAxis_eq_fourierPairingDescendsToSection43PositiveEnergy1D_psiZ`,
   `section43_iteratedSlice_descendedPairing_imagAxis`, and
   `section43_iteratedSlice_descendedPairing` in
   `OSToWightmanPositivity.lean`.
8. Kernel-zero support facts:
   `SCV.fourier_pairing_vanishes_of_eqOn_nonneg` in `SCV/PaleyWiener.lean`
   and `SCV.psiZ_eq_exp_of_nonneg` in `SCV/FourierLaplaceCore.lean`.

Hidden obligations for
`bvt_F_canonical_xiShift_shell_eq_integrated_descendedPsiZ_of_section43Transport`:

1. The `ψ_Z` constructor positivity proof comes from
   `mul_pos Real.two_pi_pos ht`; the nonnegativity needed to evaluate
   `ψ_Z` pointwise by `SCV.psiZ_eq_exp_of_nonneg` comes from the positive-time
   slice support theorem. These two positivity proofs must not be interchanged.
2. The selected time slice is the right-block index
   `⟨n, Nat.lt_add_of_pos_right hm⟩`; any helper with a different selected
   coordinate is off-surface for this theorem.
3. Every call to a one-variable quotient theorem needs a proof
   `∀ i, i ≠ r → 0 ≤ t i` for the frozen background times. Those proofs must
   come from the dual-cone pointwise EqOn proof produced by
   `tflat_pairing_eq_of_eqOn_dualCone`
   plus the concrete tail-direction nonpositivity calculation above, and then
   be fed into
   `unshifted_full_timeOrthant_descended_pairing_eq_of_section43Transport`,
   not from `f.2`/`g.2` alone and not from an ambient support assertion about
   `φ` or `ψ`. The support hypotheses `f.2` and `g.2` only prove vanishing of
   the positive-time preimage side outside the orthant; they do not make an
   arbitrary ambient frozen background nonnegative.
4. `hφf` and `hψg` may be used only through
   `section43PositiveEnergyQuotientMap` and the slice bridge theorems above.
   Directly rewriting `(φ : NPointDomain d n → ℂ)` to `f.1` or
   `(ψ : NPointDomain d m → ℂ)` to `g.1` is forbidden.
5. `hf_compact` and `hg_compact` are carried here so this theorem has the same
   surface as the final `lemma42` adapter and the optional `singleSplit`
   diagnostic bridge. They should not be used to rewrite ambient representatives
   directly. `hψ_compact` is the compactness hypothesis actually needed by the
   canonical Wightman time-shift functional and witness.
6. The descended pairing may be expanded only with
   `fourierPairingDescendsToSection43PositiveEnergy1D_apply` and
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply`; do not unfold
   quotient constructions or choose representatives by hand.
7. Integrability source is the existing Wightman time-shift tempered functional,
   one-sided Fourier-support package, and slice-pairing package. Before adding
   any integrability helper, record the exact Lean side goal in this subsection
   and make the helper prove precisely that goal under the displayed
   `φ ψ f g hφf hψg t ht` hypotheses.
8. The Fubini exchange must be applied to
   `T1 : SchwartzMap (Fin 1 → ℝ) ℂ →L[ℂ] ℂ`, never directly to
   `TW : SchwartzMap ℝ ℂ →L[ℂ] ℂ`. The conversion back to the real-line
   outer integral is exactly `h_outer_real`; do not introduce a Fourier
   transform / reindex commutation lemma for this step.
9. No step may infer equality of
   `timeShiftSchwartzNPoint (d := d) t ψ` and
   `timeShiftSchwartzNPoint (d := d) t (EuclideanPositiveTimeComponent.ofSubmodule g).1`
   from `hψg`. The shift samples `ψ` at `x - timeShiftVec d t`, so the
   Section-4.3 nonnegative-region equality for the unshifted representatives
   is insufficient. The shifted right factor can only be compared after the
   time-shift distribution has been paired with the Paley-Wiener kernel and
   reduced to unshifted positive-support slice data.

Once a transported shell-limit theorem and the OS holomorphic identification are
available, the semigroup-target version is purely formal. The transported
shell-limit theorem must not be proved by the withdrawn arbitrary
shell-minus-horizontal EqOn; it must use the Section-4.3 hypotheses `hφf` and
`hψg` inside the scalar comparison.

```lean
private theorem
    tendsto_bvt_F_canonical_xiShift_to_osHolomorphicValue_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f.1 f.2)
          (PositiveTimeBorchersSequence.single m g.1 g.2) (t : ℂ)))
```

Proof transcript:

1. Prove the transported scalar bridge
   `tendsto_bvt_F_canonical_xiShift_to_osHolomorphicValue_of_section43Transport`
   directly from Section-4.3 slice descent, or prove the canonical-extension
   variant under the same `hφf`/`hψg` hypotheses and then rewrite by the
   OS-holomorphic identification.
2. If using the canonical-extension variant, let `hCanonLimit` be
   `tendsto_bvt_F_canonical_xiShift_to_canonicalExtension_imagAxis_of_section43Transport`
   specialized to the fixed `t ht`, and let `hCanonOS` be
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imag_eq_osHolomorphicValue_of_section43Transport`
   specialized to the same `t ht`.
3. Rewrite the target of `hCanonLimit` by `hCanonOS` and close with `simpa`.
   No same-shell Euclidean/Wightman equality is used in this direct route.

Do not prove the normalized iterated-residual theorem from the semigroup shell
limit or from the canonical witness's OS identification. That would be circular
on the current route. Also do not attempt to prove the arbitrary
shell-minus-horizontal zero theorem: after the horizontal scalar computation it
is diagnostic only, not live route work. The remaining live route work is the
transported Section-4.3 scalar comparison.

The OS-side comparison needed by the same consumer is the following exact
hypothesis supplier for the already-proved ambient/preimage reducer:

```lean
private theorem
    descendedPsiZ_boundaryValue_eq_osSpectral_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g) :
    let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single n f.1 f.2⟧)) : OSHilbertSpace OS))
    let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single m g.1 g.2⟧)) : OSHilbertSpace OS))
    ∀ t : ℝ, ∀ ht : 0 < t,
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
          (d := d) OS lgc φ ψ hψ_compact)
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm φ ψ hψ_compact)
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (t * Complex.I)))
            (by
              simpa [Complex.mul_im, ht.ne']
                using mul_pos Real.two_pi_pos ht))) =
      selfAdjointSpectralBoundaryValueOffdiagCLM
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        xF xG
        (SCV.schwartzPsiZ
          (((2 * Real.pi : ℂ) * (t * Complex.I)))
          (by
            simpa [Complex.mul_im, ht.ne']
              using mul_pos Real.two_pi_pos ht))
```

Proof transcript for this OS-side theorem:

1. Expand the descended Wightman pairing with
   `OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D_apply`
   and `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply`.
2. Prove or invoke the off-diagonal core helper
   `descendedPsiZ_boundaryValue_eq_selfAdjointSpectralLaplaceOffdiag_of_section43Transport`.
   This is the only hard comparison inside `hPsi`: it converts the descended
   Wightman `ψ_Z` boundary value directly to
   `ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag`.
3. Rewrite the OS spectral boundary side with
   `selfAdjointSpectralBoundaryValueOffdiagCLM_apply` and
   `selfAdjointSpectralBoundaryValueOffdiag_eq_selfAdjointSpectralLaplaceOffdiag_psiZ`,
   using `spectrum_osTimeShiftHilbert_subset_Icc`.
4. Close by transitivity through the common off-diagonal spectral Laplace
   scalar. Do not introduce Wightman-side diagonal polarization and do not add
   a compactness hypothesis for `φ`.

Dependency inventory for `descendedPsiZ_boundaryValue_eq_osSpectral_of_section43Transport`:

1. Wightman-side pairing expansion:
   `fourierPairingDescendsToSection43PositiveEnergy1D_apply` in
   `Section43Codomain.lean` and
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply` in
   `OSToWightmanBoundaryValueLimits.lean`.
2. Wightman-side support:
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport`
   in `OSToWightmanBoundaryValueLimits.lean`.
3. OS spectral boundary conversion:
   `selfAdjointSpectralBoundaryValueOffdiagCLM_apply` in
   `OSToWightmanSemigroup.lean` and
   `selfAdjointSpectralBoundaryValueOffdiag_eq_selfAdjointSpectralLaplaceOffdiag_psiZ`
   in `OSToWightmanSemigroup.lean`.
4. Positive spectral support for the semigroup:
   `spectrum_osTimeShiftHilbert_subset_Icc` in `OSToWightmanSemigroup.lean`.
5. The `ψ_Z` kernel evaluation:
   `SCV.psiZ_eq_exp_of_nonneg` in `SCV/FourierLaplaceCore.lean`, used only after the
   spectral variable has been restricted to the nonnegative half-line.
6. The semigroup scalar identity used in the off-diagonal core helper:
   `OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag`
   in `OSToWightmanSemigroup.lean`.
7. The full-kernel dual-cone descent plus unshifted full-orthant slice adapter
   listed for the finite-height normal-form helper supplies only the unshifted
   ambient-to-positive-time reduction after the time-shift distribution has
   been paired with `ψ_Z`. The one-variable slice bridge inventory is used only
   inside the dual-cone pointwise EqOn proof, after the tail-direction
   nonpositivity lemmas have supplied nonnegative cumulative times and those
   times have been converted to nonnegative absolute background times. No
   additional ambient equality principle is permitted here, and in particular
   `hψg` must not be applied directly to `timeShiftSchwartzNPoint t ψ`.

Hidden obligations for this `hPsi` theorem:

1. The `let xF` and `let xG` vectors must remain exactly the OS Hilbert classes
   of `PositiveTimeBorchersSequence.single n f.1 f.2` and
   `PositiveTimeBorchersSequence.single m g.1 g.2`; do not replace them by
   ambient representatives.
2. The preferred proof does not expand the OS offdiag boundary into four
   diagonal terms; it converts it to the off-diagonal spectral Laplace scalar
   by the existing `..._psiZ` theorem. If a local simplification temporarily
   exposes the four diagonal terms, they must stay in the order expected by
   `selfAdjointSpectralBoundaryValueOffdiag`, and the Wightman side must still
   remain off-diagonal.
3. Every use of `SCV.psiZ_eq_exp_of_nonneg` needs the nonnegativity proof coming
   from the spectral support theorem, not from the sign of the external
   positive real parameter `t`.
4. The Wightman functional is
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional (d := d) OS lgc φ ψ hψ_compact`;
   its `φ ψ` arguments are not rewritten directly. Only the one-variable slice
   quotient classes are transported using `hφf` and `hψg`.
5. This theorem supplies only the `hPsi` hypothesis for the existing
   canonical-to-OS reducer. It should not also rewrite the canonical witness or
   the OS holomorphic value; those steps belong to
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imag_eq_osHolomorphicValue_of_section43Transport`.

Critical hPsi correction: do **not** polarize the Wightman side diagonally.
The live Wightman functional

```lean
bvt_W_conjTensorProduct_timeShiftTemperedFunctional
  (d := d) OS lgc φ ψ hψ_compact
```

only requires compactness of the right-shifted factor `ψ`. A diagonal
polarization proof on the Wightman side would also require functionals with
`φ` as a right-shifted factor, hence a compactness hypothesis for `φ`, which is
not part of the theorem surface and should not be added. The hPsi proof must
therefore stay genuinely off-diagonal on the Wightman side.

The positive-support time-shift distribution theorem is the expanded integral
form of the off-diagonal core. It is the place where the shifted right factor
is handled, and it is the exact Lean surface that must be proved before the
descended `ψ_Z` theorem can be a one-line quotient expansion.

Important correction: the active theorem must land directly on the
off-diagonal spectral Laplace scalar. It must **not** land first on
`bvtSingleSplitXiShiftScalar`. The raw single-split tube route has been
retired, and using the single-split scalar as the hard target would smuggle the
invalid `zSplit` surface back into the proof. The semigroup scalar is already
available on the correct OS Hilbert vectors, so the non-circular transported
comparison is:

```lean
private theorem
    integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_selfAdjointSpectralLaplaceOffdiag_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g) :
    let A : OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS :=
      osTimeShiftHilbert (d := d) OS lgc 1 one_pos
    let hA : IsSelfAdjoint A :=
      osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos
    let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single n f.1 f.2⟧)) : OSHilbertSpace OS))
    let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single m g.1 g.2⟧)) : OSHilbertSpace OS))
    ∀ t : ℝ, ∀ ht : 0 < t,
      let ψZ : SchwartzMap ℝ ℂ :=
        SCV.schwartzPsiZ
          (((2 * Real.pi : ℂ) * (t * Complex.I)))
          (by
            simpa [Complex.mul_im, ht.ne']
              using mul_pos Real.two_pi_pos ht)
      (∫ τ : ℝ,
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          (SchwartzMap.fourierTransformCLM ℂ ψZ) τ) =
        ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag A hA xF xG (t : ℂ)
```

This is the hard theorem. It is off-diagonal on both sides, uses the ambient
Wightman representatives only through the time-shift functional paired against
`𝓕ψ_Z`, and uses the Section-4.3 transport hypotheses only through quotient /
slice descent. It does not require compactness of `φ`.

Lean-ready proof transcript for this active theorem:

1. Fix `t ht` and introduce `ψZ`, `A`, `hA`, `xF`, and `xG`.
2. Rewrite the left side as
   `OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D TW hTW
      (section43PositiveEnergyQuotientMap1D ψZ)`
   using the already-proved production theorem
   `integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_fourierPairingDescendsToSection43PositiveEnergy1D`.
3. Apply the Section-4.3 transported slice comparison on the quotient class of
   `ψZ`. This is the remaining mathematical core: after expanding the
   one-variable quotient by `fourierPairingDescendsToSection43PositiveEnergy1D_apply`,
   the proof must use the full positive-energy slice bridge, not a pointwise
   rewrite of `timeShiftSchwartzNPoint t ψ`.
4. Convert the resulting OS-side slice scalar to
   `ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag A hA xF xG (t : ℂ)`
   by
   `OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag`
   only after the Section-4.3 quotient comparison has supplied the OS Hilbert
   vectors `xF` and `xG`.
5. Close by `simpa [ψZ, A, hA, xF, xG]`. If Lean exposes an additional side
   goal, record that exact goal in this subsection before adding support
   lemmas.

Optional downstream scalar-normalization packet. The local abbreviation
`bvtSingleSplitXiShiftScalar` is the explicit real-axis integral from
`bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`; it may still be useful as
a diagnostic after the main route is closed, but it is not an active
implementation target for hPsi or shell-to-Laplace.

Retired proof transcript for the old single-split integral theorem:

The following transcript is superseded by the canonical-shell correction in
§5.9.4a.1.ε. It is retained only to explain why the frequency-side `Tflat`
idea was introduced; it is not an implementation target on the current route.

1. Fix `t ht` and abbreviate `ψZ`.
2. Expand the left side only far enough to expose the Wightman time-shift
   distribution paired with `(SchwartzMap.fourierTransformCLM ℂ) ψZ`; do not
   replace the shifted ambient representative pointwise.
3. Obtain one common frequency-side distribution `Tflat` from the strengthened
   BVLimits package
   `exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr`
   below. This single package supplies both:
   the boundary representation
   `bvt_W ... = Tflat (physicsFourierFlatCLM ...)` for the ambient side, and
   the tube representation
   `bvt_F ... = fourierLaplaceExtMultiDim ... Tflat ...` for the transported
   single-split side. This is the non-circular bridge: `KTransport` must be
   built from the Fourier-Laplace representation of `bvt_F`, not by postulating
   another Wightman boundary pairing.
4. Construct `KAmbient` by applying `schwartz_clm_fubini_exchange` to the
   real-time translated Wightman orbit, exactly in the style of
   `integral_bvt_W_flattened_translate_mul_fourierTransform_eq_zero_of_negSupport`.
   The parameter space is `Fin M → ℝ`, where `M = (n + m) * (d + 1)`, with
   first coordinate the real shift `τ` and the remaining coordinates integrated
   against the normalized bump `β`; the scalar test factor is the padded
   `χhat = (SchwartzMap.fourierTransformCLM ℂ) ψZ`.
5. Construct `KTransport` by a different Fubini application. Its parameter is
   the flattened Euclidean configuration `yflat : Fin M → ℝ`; its scalar test
   factor is
   `flattenSchwartzNPoint (d := d) (f.1.osConjTensorProduct g.1)`, not the
   padded `χhat`; and its Schwartz-family value is the tube-safe
   Fourier-Laplace kernel at the flattened `xiShift` point. The FL
   representation rewrites the pointwise scalar
   `bvt_F ... (xiShift ... (wickRotatePoint y) ((t : ℂ) * Complex.I))`
   to `Tflat (multiDimPsiZDynamic ... (zSplitFlat y))` on the support of this
   positive-time test. The support-safe extension/cutoff packet below supplies
   the global continuity and polynomial-growth side conditions required by
   `schwartz_clm_fubini_exchange`.
6. Use `psiZ_twoPi_pairing_formula` only in the pointwise evaluation of
   `KAmbient`, after `hKAmbient_eval ξ` has reduced the Fubini output to the
   real-time integral in `τ`. This is the only place where the shifted variable
   `τ` is integrated out. Do not use `SCV.psiZ_eq_exp_of_nonneg`.
7. Prove the full-kernel EqOn:
   `Set.EqOn KAmbient KTransport dualCone`.
   For `ξ` in the dual cone, rewrite both sides by the Fubini pointwise fields.
   Then expand `physicsFourierFlatCLM` on the ambient side and
   `multiDimPsiZDynamic` on the transported side. On the dual cone, the
   dynamic radius/cutoff is irrelevant by
   `fourierLaplaceExtMultiDim_eq_dynamic` and
   `multiDimPsiZR_eval_eq_of_support`, so both sides reduce to the same
   OS I `(4.23) -> (4.24)` slice comparison after the Section-4.3 transport
   equalities are applied.
8. Extract nonnegative frozen background times from the dual-cone hypothesis by
   `flatTailTimeShiftDirection_pairing_nonpos_of_mem_dualCone` for each tail
   index. These nonnegative cumulative times replace the old positive-gap
   variable `u` in the EqOn proof.
9. Use the unshifted local adapter
   `unshifted_full_timeOrthant_descended_pairing_eq_of_section43Transport`
   pointwise in the remaining spatial variables. If the expanded formula has
   already isolated one side of the one-variable pairing, use the existing
   scalar forms
   `fourierInvPairingCLM_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
   and
   `fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport`
   instead; these are equivalent after the full nonnegative background times
   have been supplied.
10. Apply
   `tflat_pairing_eq_of_eqOn_dualCone` to identify the two `Tflat` pairings.
11. Collapse the transported expanded formula back to
   `bvtSingleSplitXiShiftScalar (d := d) OS lgc hm f.1 g.1 t` using the
   reverse of the same `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`,
   Fourier-Laplace representation, Fubini, and flatten/reindex normal forms.
   The transported collapse does not use `psiZ_twoPi_pairing_formula`; that
   formula belongs to the ambient real-time pairing.
12. The `n = 0` branch uses
   `section43_zero_left_repr_eq_transport_pointwise` before any left slice is
   introduced. Do not add `0 < n` to this theorem.

The old proof transcript had one non-mechanical phrase:
"put that expanded kernel into `χAmbient` / `χTransport`." The current audit of
the existing flattened support proof shows that this phrasing is too narrow for
the actual Section-4.3 transport step.

In `integral_bvt_W_flattened_translate_mul_fourierTransform_eq_zero_of_negSupport`
the representative data `φ`, `ψ` enter the **full flattened Fourier-side
Schwartz kernel** through `physicsFourierFlatCLM (flattenSchwartzNPoint ...)`;
they are not carried only by a one-dimensional time-gap test. Therefore the
production blocker must not require a "same `Ψ`, different `χ`" certificate
unless a scratch expansion has already proved that strong factorization. For the
live OS-route theorem, the correct certificate is:

1. construct two full flattened Fourier-side Schwartz kernels `KAmbient` and
   `KTransport` in the domain of the chosen `Tflat`;
2. expand the Wightman `ψ_Z`-paired scalar and the transported single-split
   scalar as pairings against those kernels;
3. prove that those kernels agree on the full dual cone;
4. use the Wightman dual-cone support package to identify the pairings.

This is still exactly OS I `(4.23) -> (4.24)`: the difference is only that the
Lean support theorem should act on the full Fourier-side kernel, not on an
artificial same-`Ψ` tail-gap special case.

The required support theorem is the following general Fourier-side statement.
It can be implemented as a pure support lemma in `SCV/FourierSupportCone.lean`,
or locally in `OSToWightmanBoundaryValueLimits.lean` if we want to avoid opening
a stable SCV file:

```lean
theorem tflat_pairing_eq_of_eqOn_dualCone
    {M : ℕ} {S : Set (Fin M → ℝ)}
    (Tflat : SchwartzMap (Fin M → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_supp : HasFourierSupportInDualCone S Tflat)
    (KAmbient KTransport : SchwartzMap (Fin M → ℝ) ℂ)
    (hEq :
      Set.EqOn
        (KAmbient : (Fin M → ℝ) → ℂ)
        (KTransport : (Fin M → ℝ) → ℂ)
        (DualConeFlat S)) :
    Tflat KAmbient = Tflat KTransport
```

Proof transcript for
`tflat_pairing_eq_of_eqOn_dualCone`:

1. Work classically and set `Δ := KAmbient - KTransport`.
2. Prove `Δ` vanishes on the dual cone by
   `intro ξ hξ; exact sub_eq_zero.mpr (hEq hξ)`.
3. Unfold `HasFourierSupportInDualCone` and `HasFourierSupportIn` in
   `hTflat_supp`, apply it to `Δ`, and discharge the support-disjointness goal:
   if `ξ ∈ Function.support Δ` and `ξ` is in the dual cone, then the previous
   pointwise vanishing contradicts `Function.mem_support.mp`.
4. Use linearity of `Tflat`: from `Tflat (KAmbient - KTransport) = 0`, obtain
   `Tflat KAmbient = Tflat KTransport` by `map_sub` and `sub_eq_zero.mp`.

This theorem is not a wrapper. It is the exact support principle already used
inside the current one-variable Stage-5 proof, but exposed for the full
frequency-side kernels produced by `schwartz_clm_fubini_exchange`.

The common `Tflat` used by both kernels must also carry the Fourier-Laplace
representation of the interior OS holomorphic function. The existing
`exists_flattened_bvt_W_dualCone_distribution` exposes only the boundary
pairing

```lean
bvt_W OS lgc q (unflattenSchwartzNPoint φ) =
  Tflat (physicsFourierFlatCLM φ)
```

That is enough for `KAmbient`, but it is not enough for `KTransport`, whose
source scalar is the interior single-split shell built from `bvt_F`. The
following BVLimits package is therefore the next required support theorem. It
does not add a new axiom; it is a repackaging of the same
`bv_implies_fourier_support` witness together with the already-available
`fl_representation_from_bv`.

```lean
private theorem
    exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (q : ℕ) :
    let C : Set (Fin q → Fin (d + 1) → ℝ) := ForwardConeAbs d q
    let Cflat : Set (Fin (q * (d + 1)) → ℝ) :=
      (flattenCLEquivReal q (d + 1)) '' C
    ∃ Tflat : SchwartzMap (Fin (q * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ,
    ∃ hCflat_open : IsOpen Cflat,
    ∃ hCflat_conv : Convex ℝ Cflat,
    ∃ hCflat_cone : IsCone Cflat,
    ∃ hCflat_salient : IsSalientCone Cflat,
      HasFourierSupportInDualCone Cflat Tflat ∧
      (∀ φ : SchwartzMap (Fin (q * (d + 1)) → ℝ) ℂ,
        bvt_W OS lgc q (unflattenSchwartzNPoint (d := d) φ) =
          Tflat (physicsFourierFlatCLM φ)) ∧
      (∀ z : Fin q → Fin (d + 1) → ℂ, z ∈ TubeDomainSetPi C →
        bvt_F OS lgc q z =
          fourierLaplaceExtMultiDim Cflat
            hCflat_open hCflat_conv hCflat_cone hCflat_salient
            Tflat (flattenCLEquiv q (d + 1) z))
```

Proof transcript for
`exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr`:

1. Copy the initial setup of
   `exists_flattened_bvt_W_dualCone_distribution`: define
   `Wcl : SchwartzNPoint d q →L[ℂ] ℂ` from `bvt_W OS lgc q`, prove
   `hWcl`, and reuse `hC_open`, `hC_conv`, `hC_cone`, `hC_salient`,
   `hF_holo`, `hF_growth`, and `hF_bv`.
2. Set `Cflat := (flattenCLEquivReal q (d + 1)) '' ForwardConeAbs d q` and
   prove the four flattened cone facts by the same lines used in
   `vladimirov_tillmann`:
   `eR.toHomeomorph.isOpenMap _ hC_open`,
   `hC_conv.linear_image eR.toLinearEquiv.toLinearMap`, the direct cone-image
   proof using `eR.map_smul`, and the salient proof using
   `(eR.toHomeomorph.image_closure C).symm` plus `eR.injective`.
3. Apply `bv_implies_fourier_support` once, obtaining
   `⟨Tflat, hTflat_supp, hTflat_eq⟩`.
4. Before simplifying `hTflat_eq` into the `bvt_W` boundary representation,
   feed that exact equality into `fl_representation_from_bv`:

```lean
have hFL_repr :
    ∀ z ∈ TubeDomainSetPi (ForwardConeAbs d q),
      bvt_F OS lgc q z =
        fourierLaplaceExtMultiDim Cflat
          hCflat_open hCflat_conv hCflat_cone hCflat_salient
          Tflat (flattenCLEquiv q (d + 1) z) :=
  fl_representation_from_bv
    (ForwardConeAbs d q) hC_open hC_conv hC_cone hC_salient
    (bvt_F OS lgc q) hF_holo Wcl hF_bv
    Cflat rfl hCflat_open hCflat_conv hCflat_cone hCflat_salient
    Tflat hTflat_supp hTflat_eq
```

5. Return `Tflat`, the flattened cone witnesses, `hTflat_supp`, the boundary
   representation
   `by intro φ; simpa [Wcl, unflattenSchwartzNPoint] using hTflat_eq φ`,
   and `hFL_repr`.

Implementation placement: put this theorem immediately after
`exists_flattened_bvt_W_dualCone_distribution` in
`OSToWightmanBoundaryValueLimits.lean`, or replace that theorem's local proof
body by this stronger package and recover the old theorem as a short
projection. The theorem is not a wrapper because it exposes the interior
Fourier-Laplace identity that `KTransport` must consume.

#### 5.9.4a.1.ε Correction: the raw single-split tube-support packet is retired

The transported Fubini side must **not** be implemented from the raw
`singleSplit` surface displayed in the previous draft. The tempting theorem

```lean
zSplit_mem_forwardTube_of_osConjTensorProduct_support
```

is false as stated. In the simplest `n = 1`, `m = 1` case, a point in the
support of `f.osConjTensorProduct g` has its left block in the OS-reflected
support of `f`, hence its first Euclidean time is negative. The raw expression

```lean
xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)
```

does not change the first left point when `n > 0`, so the imaginary part of the
first absolute coordinate has negative time component. But
`ForwardConeAbs d (n + m)` requires the first absolute imaginary increment to
lie in `InOpenForwardCone d`, in particular to have positive time component.
Thus the raw point is not in the forward tube in general.

Operational consequence:

1. Do not invoke the strengthened multivariable Fourier-Laplace representation
   on the raw `singleSplit` integrand at `ε = 0`.
2. Do not implement `exists_transportTubeCutoff`,
   `continuous_transportPsiZFamily_with_cutoff`,
   `seminorm_transportPsiZFamily_with_cutoff_bound`, or
   `exists_transportKernel_pairing_singleSplitXiShiftScalar` from the raw
   `zSplit` surface below. Those names are retained only as historical markers
   for the rejected route.
3. The corrected shell-to-Laplace proof must stay on the canonical
   positive-height shell
   `x + ε * canonicalForwardConeDirection * I`, with `ε > 0`, until after the
   Fourier-Laplace/Fubini comparison has been performed. Only then may the
   already-proved boundary-value limit send `ε → 0+`.

This correction aligns the blueprint with the production theorem surface already
present in `OSToWightmanPositivity.lean`:

```lean
bvt_F_canonical_xiShift_shell_sub_horizontal_eq_shell_sub_iterated_fourierLaplaceIntegral
tendsto_bvt_F_canonical_xiShift_shell_sub_iterated_to_timeShift_sub_canonicalExtension
tendsto_bvt_F_canonical_xiShift_to_ambientCanonicalExtension_imagAxis_of_shell_sub_horizontal_tendsto_zero
```

The next hard theorem is therefore not a raw equality with
`bvtSingleSplitXiShiftScalar`. It is the finite-height canonical residual
identity:

```lean
private theorem
    bvt_F_canonical_xiShift_shell_eq_iterated_fourierLaplaceIntegral
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    (∫ y : NPointDomain d (n + m),
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
        (φ.conjTensorProduct ψ) y) =
    (∫ x : ℝ,
      (∫ τ : ℝ,
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (SCV.schwartzPsiZ
            ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
            (by
              have hscaled : 0 < (2 * Real.pi) *
                  (((x : ℂ) + ε * Complex.I).im) :=
                mul_pos Real.two_pi_pos (by simpa using hε)
              simpa [Complex.mul_im] using hscaled))) τ) *
      (SchwartzMap.fourierTransformCLM ℂ
        (SCV.schwartzPsiZ
          (((2 * Real.pi : ℂ) * (t * Complex.I)))
          (by
            simpa [Complex.mul_im, ht.ne']
              using mul_pos Real.two_pi_pos ht))) x)
```

This theorem is purely the shell-to-Laplace/Fubini comparison for the ambient
representatives `φ, ψ`. It does not mention the positive-time preimages `f, g`
and it does not use Section-4.3 transport. Section-4.3 transport is needed in
the separate `hH_imag_os` theorem identifying the canonical witness on the
positive imaginary axis with the OS holomorphic matrix element.

The finite-height proof is Lean-ready in the following smaller packets.

First, the canonical shell is genuinely in the forward tube for every real
configuration, precisely because the imaginary part is the fixed positive
canonical direction and the `ξ`-shift parameter `t : ℂ` is real:

```lean
private theorem canonicalXiShift_mem_forwardTube
    {n m : ℕ} (hm : 0 < m)
    {t ε : ℝ} (hε : 0 < ε)
    (y : NPointDomain d (n + m)) :
    xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      (fun k μ =>
        ↑(y k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
            Complex.I)
      (t : ℂ) ∈ TubeDomainSetPi (ForwardConeAbs d (n + m))
```

Proof transcript:

1. Unfold `TubeDomainSetPi`.
2. Prove the imaginary part is exactly
   `ε • canonicalForwardConeDirection (d := d) (n + m)`.
   The `xiShift` adds the real scalar `(t : ℂ)`, so it contributes no imaginary
   part.
3. Convert `canonicalForwardConeDirection_mem (d := d) (n + m)` to membership
   in `ForwardConeAbs d (n + m)` using
   `inForwardCone_iff_mem_forwardConeAbs`.
4. Apply `forwardConeAbs_smul d (n + m) ε hε`.

The shell-side Fubini package also needs the flattened tube bridge already used
locally in `VladimirovTillmann.lean`. Promote it as reusable support before the
Fubini theorem:

```lean
theorem flattenCLEquiv_mem_tubeDomain_image
    {n r : ℕ} {C : Set (Fin n → Fin (r + 1) → ℝ)}
    {z : Fin n → Fin (r + 1) → ℂ}
    (hz : z ∈ TubeDomainSetPi C) :
    flattenCLEquiv n (r + 1) z ∈
      SCV.TubeDomain ((flattenCLEquivReal n (r + 1)) '' C)

theorem flattenCLEquiv_symm_mem_tubeDomainSetPi_of_mem_tubeDomain_image
    {n r : ℕ} {C : Set (Fin n → Fin (r + 1) → ℝ)}
    {w : Fin (n * (r + 1)) → ℂ}
    (hw : w ∈ SCV.TubeDomain ((flattenCLEquivReal n (r + 1)) '' C)) :
    (flattenCLEquiv n (r + 1)).symm w ∈ TubeDomainSetPi C
```

Both proofs are one-line imaginary-part transport after
`flattenCLEquiv_im`, `flattenCLEquiv_apply`, and
`flattenCLEquivReal_apply`. They are not route wrappers: they expose the exact
SCV/Pi-domain bridge needed to use the flattened Fourier-Laplace theorem on the
canonical shell.

Second, package the shell side as a `Tflat` pairing at fixed `ε > 0`:

```lean
private theorem
    exists_shellKernel_pairing_canonicalXiShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    {t ε : ℝ} (hε : 0 < ε)
    (hCflat_open :
      IsOpen
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_conv :
      Convex ℝ
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_cone :
      IsCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_salient :
      IsSalientCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hFL :
      ∀ z : Fin (n + m) → Fin (d + 1) → ℂ,
        z ∈ TubeDomainSetPi (ForwardConeAbs d (n + m)) →
          bvt_F OS lgc (n + m) z =
            fourierLaplaceExtMultiDim
              ((flattenCLEquivReal (n + m) (d + 1)) ''
                ForwardConeAbs d (n + m))
              hCflat_open hCflat_conv hCflat_cone hCflat_salient
              Tflat (flattenCLEquiv (n + m) (d + 1) z)) :
    ∃ KShell : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
      (∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)) *
          (φ.conjTensorProduct ψ) y) =
        Tflat KShell
```

Proof transcript:

1. First apply `canonicalShellPsiZExtFamily_pairing` with
   `fFlat := flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ)`.
   This gives `KShell` and the flat identity

```lean
∫ yflat, Tflat (multiDimPsiZExt Cflat ... (zShellFlat yflat)) *
  flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ) yflat
= Tflat KShell
```

2. Use `integral_flatten_change_of_variables (n + m) (d + 1)` for the flat
   integrand

```lean
fun yflat =>
  Tflat (multiDimPsiZExt Cflat ... (zShellFlat yflat)) *
    flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ) yflat
```

   so the flat integral is the same as the integral over
   `NPointDomain d (n+m)` after substituting
   `yflat = flattenCLEquivReal (n + m) (d + 1) y`.

3. In that substituted integrand, simplify
   `(flattenCLEquivReal ...).symm (flattenCLEquivReal ... y)` to `y` and use
   `flattenSchwartzNPoint_apply` to turn the flat test factor into
   `(φ.conjTensorProduct ψ) y`.

4. Use `canonicalXiShift_mem_forwardTube` to rewrite each shell value by `hFL`.
5. Rewrite `fourierLaplaceExtMultiDim` to
   `Tflat (multiDimPsiZExt ...)` using
   `fourierLaplaceExtMultiDim_eq_ext`. Do **not** use
   `fourierLaplaceExtMultiDim_eq_dynamic` here: the existing public continuity
   API is for the fixed-radius `multiDimPsiZ` / `multiDimPsiZExt` family, and
   the boundary-value proof already contains the exact fixed-radius Fubini
   pattern needed here.
6. Apply `schwartz_clm_fubini_exchange` only through the already-checked
   `canonicalShellPsiZExtFamily_pairing` to the family
   `yflat ↦ multiDimPsiZExt Cflat ... (zShellFlat yflat)`, where

```lean
let zShell (yflat : Fin ((n + m) * (d + 1)) → ℝ) :
    Fin (n + m) → Fin (d + 1) → ℂ :=
  xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
    (fun k μ =>
      (((flattenCLEquivReal (n + m) (d + 1)).symm yflat k μ : ℝ) : ℂ) +
        ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
          Complex.I)
    (t : ℂ)

let zShellFlat (yflat : Fin ((n + m) * (d + 1)) → ℝ) :
    Fin ((n + m) * (d + 1)) → ℂ :=
  flattenCLEquiv (n + m) (d + 1) (zShell yflat)
```

   The continuity proof copies the `hFubini` continuity block in
   `fourierLaplaceExtMultiDim_boundaryValue`: define
   `ι yflat : SCV.TubeDomain Cflat` by pairing `zShellFlat yflat` with tube
   membership from `canonicalXiShift_mem_forwardTube` and
   `flattenCLEquiv_mem_tubeDomain_image`; then write the family as
   a direct application of the public helper
   `continuous_multiDimPsiZExt_comp_of_mem_tube`.
4. The seminorm-growth proof also copies the fixed-radius growth block in
   `fourierLaplaceExtMultiDim_boundaryValue`, not the dynamic-radius theorem.
   This should not be copied directly into Positivity, because the existing
   proof uses private Paley-Wiener internals such as `multiDimPsiExpCLM`.
   Instead, first promote the reusable analytic estimate inside
   `PaleyWienerSchwartz.lean`:

```lean
theorem multiDimPsiZExt_fixedImaginary_seminorm_bound
    {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    {η : Fin m → ℝ} (hη : η ∈ C)
    (k n : ℕ) :
    ∃ (B : ℝ) (N : ℕ), 0 < B ∧
      ∀ x : Fin m → ℝ,
        SchwartzMap.seminorm ℝ k n
          (multiDimPsiZExt C hC_open hC_conv hC_cone hC_salient
            (fun i => (x i : ℂ) + (η i : ℂ) * Complex.I)) ≤
          B * (1 + ‖x‖) ^ N
```

   Proof transcript for this public helper:

   1. Set `χ := fixedConeCutoff_exists ...`, `y₀ := η`, and obtain
      `c₀ > 0` from `dualConeFlat_coercivity hC_open hC_cone hη`.
   2. For `z x i := (x i : ℂ) + (η i : ℂ) * Complex.I`, show
      `z x ∈ SCV.TubeDomain C` and
      `(fun i => (z x i).im) = η`.
   3. Use `cexp_bound_on_support` with the fixed coercivity `c₀`, support
      radius `1`, and
      `A₀ := c₀ + ((Fintype.card (Fin m) : ℝ)^2) * ‖η‖`.
   4. Apply `schwartz_seminorm_cutoff_exp_bound_affine_uniform` to obtain the
      pointwise derivative bound for the fixed-radius raw kernel.
   5. Convert the pointwise bound to a Schwartz seminorm by
      `SchwartzMap.seminorm_le_bound` and `multiDimPsiZExt_eq`.
   6. Bound
      `‖multiDimPsiExpCLM (z x)‖ ≤ mR * (‖x‖ + ‖η‖)` by
      `multiDimPsiExpCLM_norm_le` plus the componentwise estimate
      `‖z x‖ ≤ ‖x‖ + ‖η‖`.
   7. Absorb the affine term into a polynomial:
      with `Cpoly := 1 + mR * ‖η‖ + mR`,
      `(1 + ‖multiDimPsiExpCLM (z x)‖)^n
        ≤ Cpoly^n * (1 + ‖x‖)^n`.

   Then specialize this helper in Positivity. The shell imaginary part is the
   fixed vector

```lean
ηShell :=
  flattenCLEquivReal (n + m) (d + 1)
    (ε • canonicalForwardConeDirection (d := d) (n + m))
```

   and `ηShell ∈ Cflat` follows from
   `forwardConeAbs_smul` plus the flattening image. The shell real part is

```lean
xShell yflat i := (zShellFlat yflat i).re
```

   and `zShellFlat yflat` is definitionally equal, coordinatewise by real and
   imaginary parts, to
   `fun i => (xShell yflat i : ℂ) + (ηShell i : ℂ) * Complex.I`.
   The only Positivity-specific estimate needed for the Fubini side condition
   is the affine norm bound

```lean
∃ A > 0, ∀ yflat,
  ‖xShell yflat‖ ≤ A * (1 + ‖yflat‖)
```

   A concrete choice is
   `A := 1 + |t|`: each coordinate of the real part is either the corresponding
   flattened real coordinate or that coordinate plus `t` in the shifted
   time-component region, so
   `|xShell yflat i| ≤ ‖yflat‖ + |t| ≤ (1 + |t|) * (1 + ‖yflat‖)`.
   After applying the public helper to `xShell yflat`, absorb
   `(1 + ‖xShell yflat‖)^N` into a constant multiple of
   `(1 + ‖yflat‖)^N`.
7. Conclude by transitivity with the flat identity from Step 1.

Implementation helpers to write before the shell package, all copied from the
existing `fourierLaplaceExtMultiDim_boundaryValue` proof skeleton:

```lean
theorem continuous_multiDimPsiZExt_comp_of_mem_tube ...        -- implemented
private theorem continuous_canonicalShellPsiZExtFamily ...     -- implemented
private theorem seminorm_canonicalShellPsiZExtFamily_bound ...
private theorem canonicalShellPsiZExtFamily_pairing ...
```

The public continuity helper is already the reusable form of the
`multiDimPsiZExt` continuity block. The two shell-specific helpers discharge
the `schwartz_clm_fubini_exchange` side conditions.

The next implementation should first prove the flat Fubini packet, because it
is the direct consumer of those two side conditions and does not yet need the
boundary-value representation hypothesis:

```lean
private theorem canonicalShellPsiZExtFamily_pairing
    {n m : ℕ} (hm : 0 < m)
    {t ε : ℝ} (hε : 0 < ε)
    (hCflat_open : IsOpen Cflat)
    (hCflat_conv : Convex ℝ Cflat)
    (hCflat_cone : IsCone Cflat)
    (hCflat_salient : IsSalientCone Cflat)
    (Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (fFlat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ) :
    ∃ KShell : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
      (∫ yflat : Fin ((n + m) * (d + 1)) → ℝ,
        Tflat (multiDimPsiZExt Cflat ... (zShellFlat yflat)) *
          fFlat yflat) =
        Tflat KShell
```

Proof transcript:

1. Define
   `gFamily yflat := multiDimPsiZExt Cflat ... (zShellFlat yflat)`.
2. Use `continuous_canonicalShellPsiZExtFamily` for the `hg_cont` hypothesis.
3. Use `seminorm_canonicalShellPsiZExtFamily_bound` for the `hg_bound`
   hypothesis.
4. Apply
   `schwartz_clm_fubini_exchange Tflat gFamily fFlat hg_cont hg_bound`.
5. Return the produced `KShell`; the axiom gives
   `Tflat KShell = ∫ yflat, Tflat (gFamily yflat) * fFlat yflat`, so the
   desired displayed equality is its symmetric form.

Only after this flat packet is checked should the route prove
`exists_shellKernel_pairing_canonicalXiShift`, which adds:

1. `hFL` to rewrite
   `bvt_F OS lgc ... shellZ = Tflat (multiDimPsiZExt Cflat ... zShellFlat)`;
2. `integral_flatten_change_of_variables` plus the
   `flattenSchwartzNPoint_apply` normal form for the change from
   `NPointDomain d (n+m)` to flat coordinates;
3. `fFlat := flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ)`.

These helpers are genuine analytic/Fubini content and are permitted; a
one-line wrapper around `hFL` alone is not.

Third, package the horizontal/iterated Fourier-Laplace side as a `Tflat`
pairing using the same `Tflat`:

```lean
private theorem
    exists_horizontalKernel_pairing_iteratedFourierLaplace
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε)
    (Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_bv :
      ∀ φflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
        bvt_W OS lgc (n + m) (unflattenSchwartzNPoint (d := d) φflat) =
          Tflat (physicsFourierFlatCLM φflat)) :
    ∃ KHorizontal : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
      (∫ x : ℝ,
        (∫ τ : ℝ,
          bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          (SchwartzMap.fourierTransformCLM ℂ
            (SCV.schwartzPsiZ
              ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
              (by
                have hscaled : 0 < (2 * Real.pi) *
                    (((x : ℂ) + ε * Complex.I).im) :=
                  mul_pos Real.two_pi_pos (by simpa using hε)
                simpa [Complex.mul_im] using hscaled))) τ) *
        (SchwartzMap.fourierTransformCLM ℂ
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (t * Complex.I)))
            (by
              simpa [Complex.mul_im, ht.ne']
                using mul_pos Real.two_pi_pos ht))) x) =
        Tflat KHorizontal
```

Implementation-readiness refinement.

Do not attempt the displayed double integral as the first Lean theorem. The
safe implementation route factors it through an arbitrary one-variable
time-shift test. This is the missing reusable rung between the shell-side
`KShell` theorem and the full horizontal kernel:

```lean
theorem exists_timeShiftKernel_pairing_fourierTest
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (χ : SchwartzMap ℝ ℂ)
    (Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_bv :
      ∀ φflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
        bvt_W OS lgc (n + m) (unflattenSchwartzNPoint (d := d) φflat) =
          Tflat (physicsFourierFlatCLM φflat)) :
    ∃ Kχ : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
      (∀ ξ : (Fin ((n + m) * (d + 1)) → ℝ),
        Kχ ξ =
          (∫ τ : ℝ,
            timeShiftFlatOrbit (d := d) φ ψ τ ξ * χ τ)) ∧
      ((∫ τ : ℝ,
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          χ τ) =
        Tflat Kχ)
```

This theorem is implemented in `OSToWightmanBoundaryValueLimits.lean`, not in the
positivity frontier, because its proof is exactly the existing flat
translation/Fubini proof pattern with the negative-support vanishing step
removed. Its statement mentions no private BVLimits constants; the proof may
reuse the private local flattening algebra already in that file.

Proof transcript for `exists_timeShiftKernel_pairing_fourierTest`:

1. Set `M := (n + m) * (d + 1)`. Since `0 < d` is in scope, `0 < M` follows
   from `hm : 0 < m`. Define
   `k := M - 1`, `hk : k + 1 = M`, `β := normedUnitBumpSchwartzPi k`,
   `fpad0 := χ.prependField β`, and
   `fpad := OSReconstruction.reindexSchwartzFin hk fpad0`.
2. Define the public orbit abbreviation

```lean
timeShiftFlatOrbit (d := d) φ ψ τ
```

   for the full expression
   `physicsFourierFlatCLM (reindexSchwartzFin ...
     (SCV.translateSchwartz (zeroHeadBlockShift (τ • flatTimeShiftDirection d m))
       Ψ))`. This keeps the theorem statement parse-stable and gives the
   downstream EqOn proof a canonical name for the horizontal orbit. Here
   `Ψ := (flattenSchwartzNPoint (d := d) φ.borchersConj).tensorProduct
     (flattenSchwartzNPoint (d := d) ψ)`,
   `orbit τ := timeShiftFlatOrbit (d := d) φ ψ τ`,
   `headCoord x := ((OSReconstruction.castFinCLE hk).symm x) 0`, and
   `gFamily x := orbit (headCoord x)`.
3. Prove `Continuous gFamily` using
   `continuous_physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift`
   composed with `headCoord`.
4. Prove the polynomial seminorm bound for `gFamily` from
   `exists_bound_seminorm_physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift`
   and `|headCoord x| ≤ ‖x‖`, exactly as in
   `integral_bvt_W_flattened_translate_mul_fourierTransform_eq_zero_of_negSupport`.
5. Apply `schwartz_clm_fubini_exchange Tflat gFamily fpad` and call the
   produced kernel `Kχ`.
6. Rewrite its pointwise formula from the full flat integral to the displayed
   one-variable integral using `integral_comp_castFinCLE_eq`,
   `integral_finSucc_cons_eq`, `MeasureTheory.integral_prod_mul`, and
   `integral_normedUnitBumpSchwartzPi`.
7. Rewrite the scalar pairing field by `hTflat_bv`, the local
   `timeShiftSchwartzNPoint`/flattening translation identity, and the same
   padded-integral calculation. The final result is the displayed equality
   `(∫ τ, bvt_W ... * χ τ) = Tflat Kχ`.

After this theorem is available, the horizontal packet is no longer a raw
double-Fubini problem. It should be assembled in two explicit steps:

1. Build a one-dimensional horizontal Paley kernel `χHorizontal ε t` by applying
   `schwartz_clm_fubini_exchange` on `Fin 1` to the family
   `x ↦ (SchwartzMap.fourierTransformCLM ℂ) (ψZ_{2π(x+εi)})`, using the already
   documented side conditions
   `continuous_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal` and
   `seminorm_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal_growth`.
   Its pointwise formula is
   `χHorizontal τ = ∫ x, (𝓕 ψZ_{2π(x+εi)}) τ * (𝓕 ψZ_{2πit}) x`.
2. Apply `exists_timeShiftKernel_pairing_fourierTest` with
   `χ := χHorizontal`. The resulting `Kχ` is the desired
   `KHorizontal`, and its pointwise formula is suitable for the later
   dual-cone EqOn calculation against `KShell`.

The older direct double-Fubini proof transcript is superseded by the
two-stage transcript above. In particular, do not build `KHorizontal` by first
choosing a family of existential inner kernels depending on `x`; that loses the
continuity/growth data needed for the outer Fubini step. The safe Lean order is:
first prove the arbitrary-test flat time-shift theorem, then build the
one-dimensional `χHorizontal`, then apply the arbitrary-test theorem with
`χ := χHorizontal`.

Implementation-ready statement for the one-dimensional horizontal Paley kernel:

```lean
private theorem exists_horizontalPaleyKernel_pairing_fourierTransform
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (TW : SchwartzMap ℝ ℂ →L[ℂ] ℂ) :
    ∃ χHorizontal : SchwartzMap ℝ ℂ,
      (∀ τ : ℝ,
        χHorizontal τ =
          ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ
              (SCV.schwartzPsiZ
                ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
                ...)) τ *
            (SchwartzMap.fourierTransformCLM ℂ
              (SCV.schwartzPsiZ
                (((2 * Real.pi : ℂ) * (t * Complex.I)))
                ...)) x) ∧
      TW χHorizontal =
        ∫ x : ℝ,
          TW
            ((SchwartzMap.fourierTransformCLM ℂ)
              (SCV.schwartzPsiZ
                ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
                ...)) *
          (SchwartzMap.fourierTransformCLM ℂ
            (SCV.schwartzPsiZ
              (((2 * Real.pi : ℂ) * (t * Complex.I)))
              ...)) x
```

Lean proof transcript:

1. Set

```lean
let e1 : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
let toFin1 : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap (Fin 1 → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1
let fromFin1 : SchwartzMap (Fin 1 → ℝ) ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1.symm
let T1 : SchwartzMap (Fin 1 → ℝ) ℂ →L[ℂ] ℂ := TW.comp fromFin1
let ψZt : SchwartzMap ℝ ℂ :=
  SCV.schwartzPsiZ (((2 * Real.pi : ℂ) * (t * Complex.I))) ...
let f1 : SchwartzMap (Fin 1 → ℝ) ℂ :=
  toFin1 ((SchwartzMap.fourierTransformCLM ℂ) ψZt)
let g1 : (Fin 1 → ℝ) → SchwartzMap (Fin 1 → ℝ) ℂ := fun x1 =>
  toFin1
    ((SchwartzMap.fourierTransformCLM ℂ)
      (SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((e1 x1 : ℂ) + ε * Complex.I)))
        ...))
```

2. Apply `schwartz_clm_fubini_exchange T1 g1 f1` with
   `SCV.continuous_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal hε`
   and
   `SCV.seminorm_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal_growth hε`.
   Let the produced `Fin 1` kernel be `χ1`.
3. Define `χHorizontal := fromFin1 χ1`.
4. Pointwise formula:
   `χHorizontal τ = χ1 (e1.symm τ)`, then use the Fubini pointwise formula.
   Rewrite
   `toFin1 φ x1 = φ (e1 x1)` and `e1 (e1.symm τ) = τ`.
   Convert the remaining `Fin 1` integral to the real-line integral using
   the measure-preserving equivalence
   `MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ`.
5. Pairing formula:
   `TW χHorizontal = T1 χ1`, use the Fubini pairing equality, rewrite
   `fromFin1 (toFin1 φ) = φ`, and again convert the `Fin 1` integral to the
   real-line integral.
6. Immediately derive the universal form:

```lean
private theorem exists_horizontalPaleyKernel_universal_pairing
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := ...
    let ψZt : SchwartzMap ℝ ℂ := ...
    ∃ χHorizontal : SchwartzMap ℝ ℂ,
      (∀ τ : ℝ,
        χHorizontal τ =
          ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x) ∧
      ∀ TW : SchwartzMap ℝ ℂ →L[ℂ] ℂ,
        TW χHorizontal =
          ∫ x : ℝ,
            TW (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x
```

   Proof: choose `χHorizontal` from
   `exists_horizontalPaleyKernel_pairing_fourierTransform hε ht 0`. For an
   arbitrary `TW`, apply
   `exists_horizontalPaleyKernel_pairing_fourierTransform hε ht TW`, obtaining
   `χTW`. Prove `χTW = χHorizontal` by `ext τ` from the identical pointwise
   formula. Transport the `TW` pairing identity across this equality.

   This universal theorem is essential for the dual-cone EqOn proof: at fixed
   flattened frequency `ξ`, instantiate `TW` as the one-variable continuous
   functional

```lean
χ ↦ ∫ τ, timeShiftFlatOrbit (d := d) φ ψ τ ξ * χ τ
```

   after rewriting `timeShiftFlatOrbit` to its oscillatory phase form. This
   avoids a raw ad hoc scalar Fubini step in the EqOn proof.

7. Keep these theorems in `OSToWightmanPositivity.lean` near the existing
   horizontal canonical-witness normal forms. It is generic in `TW`, so it is
   not a wrapper over the Wightman theorem; the immediate next consumer
   instantiates
   `TW := bvt_W_conjTensorProduct_timeShiftTemperedFunctional ...`.

Implementation-ready statement for the immediate Wightman/full-flat consumer:

```lean
private theorem exists_horizontalKernel_pairing_iteratedFourierLaplace
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_bv :
      ∀ φflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
        bvt_W OS lgc (n + m) (unflattenSchwartzNPoint (d := d) φflat) =
          Tflat (physicsFourierFlatCLM φflat)) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := ...
    let ψZt : SchwartzMap ℝ ℂ := ...
    ∃ χHorizontal : SchwartzMap ℝ ℂ,
      (∀ τ : ℝ,
        χHorizontal τ =
          ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x) ∧
      ∃ KHorizontal : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
        (∀ ξ : Fin ((n + m) * (d + 1)) → ℝ,
          KHorizontal ξ =
            ∫ τ : ℝ,
              timeShiftFlatOrbit (d := d) φ ψ τ ξ * χHorizontal τ) ∧
        (∫ x : ℝ,
          bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc φ ψ hψ_compact ((x : ℂ) + ε * Complex.I) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x) =
          Tflat KHorizontal
```

Proof transcript:

1. Let
   `TW := bvt_W_conjTensorProduct_timeShiftTemperedFunctional
     (d := d) OS lgc φ ψ hψ_compact`.
2. Apply
   `exists_horizontalPaleyKernel_pairing_fourierTransform hε ht TW`,
   obtaining `χHorizontal`, its pointwise formula, and
   `TW χHorizontal = ∫ x, TW (𝓕 ψZxε x) * (𝓕 ψZt) x`.
3. Apply `exists_timeShiftKernel_pairing_fourierTest` to this
   `χHorizontal`, `Tflat`, and `hTflat_bv`, obtaining `KHorizontal`,
   its pointwise formula, and
   `∫ τ, bvt_W(φ ⊗ timeShift τ ψ) * χHorizontal τ = Tflat KHorizontal`.
4. Prove the horizontal scalar equality by the chain

```lean
∫ x, H(x + ε i) * (𝓕 ψZt) x
  = ∫ x, TW (𝓕 ψZxε x) * (𝓕 ψZt) x
  = TW χHorizontal
  = ∫ τ, bvt_W(φ ⊗ timeShift τ ψ) * χHorizontal τ
  = Tflat KHorizontal
```

The first equality is pointwise integral congruence using
`bvt_W_conjTensorProduct_timeShiftCanonicalExtension_horizontal_eq_fourierLaplaceIntegral`
together with
`bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply`.
The third equality is exactly
`bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply` applied to
`χHorizontal`.

Withdrawn fourth step: the finite-height full-kernel equality below is not a
valid arbitrary-`φ,ψ` target. It is retained only to document the exact theorem
shape that must **not** be implemented without additional transported
Section-4.3 hypotheses:

```lean
private theorem
    canonicalShell_horizontal_kernel_eqOn_dualCone
    ...
    Set.EqOn
      (KShell : (Fin ((n + m) * (d + 1)) → ℝ) → ℂ)
      KHorizontal
      (DualConeFlat
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
```

The reason is explicit after the horizontal scalar calculation. On the dual
cone the horizontal packet gives Laplace damping in `t`, while the canonical
shell has a real `xiShift ... (t : ℂ)` and therefore an oscillatory phase.
This mismatch is not a Lean inconvenience; it is the mathematical obstruction
that prevents an unconditional shell-to-canonical-imaginary-axis theorem.

The following support lemma remains sound and useful for shell normal-form
diagnostics, and it is already implemented in `SCV/PaleyWienerSchwartz.lean`.
It should not be followed by the withdrawn raw EqOn theorem.

Implementation-ready support lemma:

```lean
theorem multiDimPsiZExt_apply_of_mem_dualCone {m : ℕ}
    (C : Set (Fin m → ℝ)) (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (z : Fin m → ℂ) (hz : z ∈ SCV.TubeDomain C)
    {ξ : Fin m → ℝ} (hξ : ξ ∈ DualConeFlat C) :
    multiDimPsiZExt C hC_open hC_conv hC_cone hC_salient z ξ =
      Complex.exp (Complex.I * ∑ i, z i * (ξ i : ℂ))
```

Lean proof transcript:

```lean
  rw [multiDimPsiZExt_eq C hC_open hC_conv hC_cone hC_salient z hz]
  let χ : FixedConeCutoff (DualConeFlat C) :=
    (fixedConeCutoff_exists (DualConeFlat C) (dualConeFlat_closed C)).some
  change psiZRaw χ 1 z ξ =
    Complex.exp (Complex.I * ∑ i, z i * (ξ i : ℂ))
  have hχ : χ.val ξ = 1 := fixedConeCutoff_eq_one_on_dualCone χ hξ
  simp [psiZRaw, hχ]
```

Expected local adjustment: if `simp [psiZRaw, hχ]` does not rewrite the cutoff
argument because it appears as `fun i => 1⁻¹ * ξ i`, add

```lean
  have hscale : (fun i => (1 : ℝ)⁻¹ * ξ i) = ξ := by
    ext i
    simp
  simp [psiZRaw, hscale, hχ]
```

This theorem is mathematically sound because `multiDimPsiZExt` first reduces to
the fixed-radius `multiDimPsiZ` on the tube; `multiDimPsiZ` is
`psiZRaw χ 1 z`; and `χ = 1` on `DualConeFlat C` by
`FixedConeCutoff.one_on_neighborhood` plus `Metric.infDist_zero_of_mem`.

After this support lemma, the EqOn theorem should be implemented with the
following local notation:

```lean
let q : ℕ := n + m
let M : ℕ := q * (d + 1)
let Cflat : Set (Fin M → ℝ) :=
  (flattenCLEquivReal q (d + 1)) '' ForwardConeAbs d q
let Ψ : SchwartzMap (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ :=
  (flattenSchwartzNPoint (d := d) φ.borchersConj).tensorProduct
    (flattenSchwartzNPoint (d := d) ψ)
let Ψfull : SchwartzMap (Fin M → ℝ) ℂ :=
  OSReconstruction.reindexSchwartzFin
    (by ring : n * (d + 1) + m * (d + 1) = M) Ψ
let vTail : Fin M → ℝ :=
  (OSReconstruction.castFinCLE
    (by ring : n * (d + 1) + m * (d + 1) = M))
    (OSReconstruction.zeroHeadBlockShift
      (m := n * (d + 1)) (n := m * (d + 1))
      (flatTimeShiftDirection d m))
let lam ξ : ℝ := ∑ i, vTail i * ξ i
let r ξ : ℝ := - lam ξ / (2 * Real.pi)
let base ξ : ℂ := physicsFourierFlatCLM Ψfull ξ
```

For `ξ ∈ DualConeFlat Cflat`, the public BVLimits sign lemma gives
`lam ξ ≤ 0`, hence `0 ≤ r ξ`. The exact one-variable Fourier normalization is:

```lean
∫ τ : ℝ,
  Complex.exp (-(Complex.I * (lam ξ : ℂ) * τ)) *
    (SchwartzMap.fourierTransformCLM ℂ χ) τ
= χ (r ξ)
```

This is exactly `integral_phase_mul_fourierTransform_eq_eval χ (lam ξ)`.

The fixed-frequency phase functional used with
`exists_horizontalPaleyKernel_universal_pairing` is:

```lean
TWξ χ :=
  base ξ *
    ∫ τ : ℝ,
      Complex.exp (-(Complex.I * (lam ξ : ℂ) * τ)) * χ τ
```

or equivalently the integral of
`Complex.exp (-(I * lam ξ * τ)) * base ξ * χ τ`; choose the former in Lean
because it is the scalar multiple of the existing one-variable
`SchwartzMap.integralCLM` applied after `SchwartzMap.smulLeftCLM` by the
temperate-growth phase. Its evaluation on Fourier transforms is:

```lean
TWξ (SchwartzMap.fourierTransformCLM ℂ χ)
  = base ξ * χ (r ξ)
```

by pulling out `base ξ` and applying
`integral_phase_mul_fourierTransform_eq_eval`.

Implementation-ready support lemma for the full-flat time-shift orbit, to be
placed in `OSToWightmanBoundaryValueLimits.lean` immediately after
`timeShiftFlatOrbit`:

```lean
theorem timeShiftFlatOrbit_apply_phase
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (τ : ℝ) (ξ : Fin ((n + m) * (d + 1)) → ℝ) :
    timeShiftFlatOrbit (d := d) φ ψ τ ξ =
      Complex.exp
        (-(Complex.I *
          (((∑ i,
            (((OSReconstruction.castFinCLE
              (Nat.add_mul n m (d + 1)).symm)
              (OSReconstruction.zeroHeadBlockShift
                (m := n * (d + 1)) (n := m * (d + 1))
                (flatTimeShiftDirection d m))) i) * ξ i : ℝ) : ℂ) *
            (τ : ℂ)))) *
        physicsFourierFlatCLM
          (OSReconstruction.reindexSchwartzFin
            (Nat.add_mul n m (d + 1)).symm
            ((flattenSchwartzNPoint (d := d) φ.borchersConj).tensorProduct
              (flattenSchwartzNPoint (d := d) ψ))) ξ
```

Lean proof transcript:

```lean
  classical
  let Ψ : SchwartzMap (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ :=
    (flattenSchwartzNPoint (d := d) φ.borchersConj).tensorProduct
      (flattenSchwartzNPoint (d := d) ψ)
  dsimp [timeShiftFlatOrbit]
  rw [physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift_apply
    (d := d) (n := n) (m := m)
    (a := τ • flatTimeShiftDirection d m) (Ψ := Ψ) (ξ := ξ)]
  congr 1
  have hsum_real :
      (∑ i,
          ((OSReconstruction.castFinCLE
            (Nat.add_mul n m (d + 1)).symm)
            (OSReconstruction.zeroHeadBlockShift
              (m := n * (d + 1)) (n := m * (d + 1))
              (τ • flatTimeShiftDirection d m))) i * ξ i) =
        (∑ i,
          ((OSReconstruction.castFinCLE
            (Nat.add_mul n m (d + 1)).symm)
            (OSReconstruction.zeroHeadBlockShift
              (m := n * (d + 1)) (n := m * (d + 1))
              (flatTimeShiftDirection d m))) i * ξ i) * τ := by
    simp [zeroHeadBlockShift_smul, Finset.mul_sum, Pi.smul_apply,
      mul_assoc, mul_left_comm, mul_comm]
  have hsum :
      (∑ i,
          ((((OSReconstruction.castFinCLE
            (Nat.add_mul n m (d + 1)).symm)
            (OSReconstruction.zeroHeadBlockShift
              (m := n * (d + 1)) (n := m * (d + 1))
              (τ • flatTimeShiftDirection d m))) i : ℝ) : ℂ) *
            (ξ i : ℂ)) =
        ((∑ i,
            (((OSReconstruction.castFinCLE
              (Nat.add_mul n m (d + 1)).symm)
              (OSReconstruction.zeroHeadBlockShift
                (m := n * (d + 1)) (n := m * (d + 1))
                (flatTimeShiftDirection d m))) i) * ξ i : ℝ) : ℂ) * τ := by
    exact_mod_cast hsum_real
  congr 1
  rw [hsum]
```

This theorem is a genuine exposure of existing Fourier algebra, not a wrapper:
it removes the repeated unfold/rewrite burden from the future EqOn proof and
fixes the sign of the phase once, using the already verified translation lemma.

Implementation-ready one-variable phase functional packet, to be placed in
`OSToWightmanPositivity.lean` near the horizontal Paley kernel theorem:

```lean
private theorem horizontalPhase_temperate (lam : ℝ) :
    (fun τ : ℝ =>
      Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ)))).HasTemperateGrowth := by
  let c : ℂ := -(Complex.I * (lam : ℂ))
  suffices htemp : (fun τ : ℝ => Complex.exp (c * (τ : ℂ))).HasTemperateGrowth by
    convert htemp using 1
    ext τ
    simp [c, mul_assoc]
  refine ⟨?_, ?_⟩
  · have hlin : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun τ : ℝ => c * (τ : ℂ)) := by
      simpa using (contDiff_const.mul Complex.ofRealCLM.contDiff)
    exact Complex.contDiff_exp.comp hlin
  · intro n
    refine ⟨0, ‖c ^ n‖, fun τ => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hiter := congr_fun (SCV.iteratedDeriv_cexp_const_mul_real n c) τ
    rw [hiter]
    have hre : (c * (τ : ℂ)).re = 0 := by
      simp [c, Complex.mul_re]
    calc
      ‖c ^ n * Complex.exp (c * (τ : ℂ))‖ = ‖c ^ n‖ := by
        rw [norm_mul, Complex.norm_exp, hre, Real.exp_zero, mul_one]
      _ ≤ ‖c ^ n‖ * (1 + ‖τ‖) ^ 0 := by simp

private noncomputable def horizontalPhasePairingCLM
    (base : ℂ) (lam : ℝ) :
    SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
  base •
    ((SchwartzMap.integralCLM ℂ
      (MeasureTheory.volume : MeasureTheory.Measure ℝ)).comp
      (SchwartzMap.smulLeftCLM ℂ
        (fun τ : ℝ =>
          Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ))))))

private theorem horizontalPhasePairingCLM_apply
    (base : ℂ) (lam : ℝ) (χ : SchwartzMap ℝ ℂ) :
    horizontalPhasePairingCLM base lam χ =
      base *
        ∫ τ : ℝ,
          Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ))) * χ τ := by
  simp [horizontalPhasePairingCLM, SchwartzMap.integralCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply (horizontalPhase_temperate lam), smul_eq_mul]

private theorem horizontalPhasePairingCLM_fourierTransform
    (base : ℂ) (lam : ℝ) (χ : SchwartzMap ℝ ℂ) :
    horizontalPhasePairingCLM base lam
        ((SchwartzMap.fourierTransformCLM ℂ) χ) =
      base * χ (-lam / (2 * Real.pi)) := by
  rw [horizontalPhasePairingCLM_apply]
  rw [integral_phase_mul_fourierTransform_eq_eval]
```

This packet is the precise way to instantiate
`exists_horizontalPaleyKernel_universal_pairing` at a fixed frequency `ξ`.
The next implementation-ready theorem is the direct instantiation:

```lean
private theorem exists_horizontalPaleyKernel_phasePairing
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (base : ℂ) (lam : ℝ) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
      SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
        (by
          have hscaled : 0 < (2 * Real.pi) *
              (((x : ℂ) + ε * Complex.I).im) :=
            mul_pos Real.two_pi_pos (by simpa using hε)
          simpa [Complex.mul_im] using hscaled)
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    ∃ χHorizontal : SchwartzMap ℝ ℂ,
      (∀ τ : ℝ,
        χHorizontal τ =
          ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x) ∧
      horizontalPhasePairingCLM base lam χHorizontal =
        ∫ x : ℝ,
          (base * (ψZxε x) (-lam / (2 * Real.pi))) *
          (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
  classical
  let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
    SCV.schwartzPsiZ
      ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
      (by
        have hscaled : 0 < (2 * Real.pi) *
            (((x : ℂ) + ε * Complex.I).im) :=
          mul_pos Real.two_pi_pos (by simpa using hε)
        simpa [Complex.mul_im] using hscaled)
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  obtain ⟨χHorizontal, hχ_eval, hχ_pair⟩ :=
    exists_horizontalPaleyKernel_universal_pairing (hε := hε) (ht := ht)
  refine ⟨χHorizontal, ?_, ?_⟩
  · simpa [ψZxε, ψZt] using hχ_eval
  · calc
      horizontalPhasePairingCLM base lam χHorizontal
          = ∫ x : ℝ,
              horizontalPhasePairingCLM base lam
                ((SchwartzMap.fourierTransformCLM ℂ) (ψZxε x)) *
              (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
              simpa [ψZxε, ψZt] using
                hχ_pair (horizontalPhasePairingCLM base lam)
      _ = ∫ x : ℝ,
            (base * (ψZxε x) (-lam / (2 * Real.pi))) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            rw [horizontalPhasePairingCLM_fourierTransform]
```

This theorem is not the final shell comparison. Its role is to turn the
horizontal `τ`-kernel into the one remaining `x`-integral at a frozen
frequency. The subsequent theorem uses it with

```lean
base := physicsFourierFlatCLM Ψfull ξ
lam := ∑ i, vTail i * ξ i
```

and use `timeShiftFlatOrbit_apply_phase` to rewrite
`timeShiftFlatOrbit τ ξ` as the integrand represented by
`horizontalPhasePairingCLM base lam`.

The next horizontal-only collapse is implementation-ready:

```lean
private theorem horizontalPaley_phase_xIntegral_eq
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (base : ℂ) (lam : ℝ) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
      SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
        (by
          have hscaled : 0 < (2 * Real.pi) *
              (((x : ℂ) + ε * Complex.I).im) :=
            mul_pos Real.two_pi_pos (by simpa using hε)
          simpa [Complex.mul_im] using hscaled)
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    ∫ x : ℝ,
      (base * (ψZxε x) (-lam / (2 * Real.pi))) *
      (SchwartzMap.fourierTransformCLM ℂ ψZt) x =
    base *
      ((SCV.smoothCutoff (-lam / (2 * Real.pi)) : ℂ) *
        Complex.exp (-(2 * Real.pi * ε : ℂ) * (-lam / (2 * Real.pi))) *
        ψZt (-lam / (2 * Real.pi))) := by
  classical
  let r : ℝ := -lam / (2 * Real.pi)
  let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
    SCV.schwartzPsiZ
      ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
      (by
        have hscaled : 0 < (2 * Real.pi) *
            (((x : ℂ) + ε * Complex.I).im) :=
          mul_pos Real.two_pi_pos (by simpa using hε)
        simpa [Complex.mul_im] using hscaled)
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  have hψ_inv :
      FourierTransform.fourierInv
          ((SchwartzMap.fourierTransformCLM ℂ) ψZt) = ψZt := by
    simpa [ψZt] using (FourierTransform.fourierInv_fourier_eq ψZt)
  have hpair :
      (∫ x : ℝ,
          (ψZxε x) r *
          (SchwartzMap.fourierTransformCLM ℂ ψZt) x) =
        (SCV.smoothCutoff r : ℂ) *
          Complex.exp (-(2 * Real.pi * ε : ℂ) * r) *
          ψZt r := by
    calc
      (∫ x : ℝ,
          (ψZxε x) r *
          (SchwartzMap.fourierTransformCLM ℂ ψZt) x)
          = ∫ x : ℝ,
              SCV.psiZ ((2 * Real.pi : ℂ) * (x + ε * Complex.I)) r *
              (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              simp [ψZxε]
      _ = (SCV.smoothCutoff r : ℂ) *
            Complex.exp (-(2 * Real.pi * ε : ℂ) * r) *
            FourierTransform.fourierInv
              ((SchwartzMap.fourierTransformCLM ℂ) ψZt) r :=
            SCV.psiZ_twoPi_pairing_formula
              (φ := (SchwartzMap.fourierTransformCLM ℂ ψZt))
              (η := ε) (ξ := r)
      _ = (SCV.smoothCutoff r : ℂ) *
            Complex.exp (-(2 * Real.pi * ε : ℂ) * r) *
            ψZt r := by rw [hψ_inv]
  have hmain :
      (∫ x : ℝ,
        (base * (ψZxε x) r) *
        (SchwartzMap.fourierTransformCLM ℂ ψZt) x) =
      base *
        ((SCV.smoothCutoff r : ℂ) *
          Complex.exp (-(2 * Real.pi * ε : ℂ) * r) *
          ψZt r) := by
    calc
      (∫ x : ℝ,
        (base * (ψZxε x) r) *
        (SchwartzMap.fourierTransformCLM ℂ ψZt) x)
          = ∫ x : ℝ,
              base * ((ψZxε x) r *
                (SchwartzMap.fourierTransformCLM ℂ ψZt) x) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              ring
      _ = base *
            ∫ x : ℝ,
              (ψZxε x) r *
              (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
            simpa using
              (MeasureTheory.integral_const_mul
                (μ := MeasureTheory.volume) base
                (fun x : ℝ =>
                  (ψZxε x) r *
                  (SchwartzMap.fourierTransformCLM ℂ ψZt) x))
      _ = base *
            ((SCV.smoothCutoff r : ℂ) *
              Complex.exp (-(2 * Real.pi * ε : ℂ) * r) *
              ψZt r) := by rw [hpair]
  simpa [r, ψZxε, ψZt] using hmain
```

The remaining horizontal simplification, after this theorem, is purely
pointwise:

1. For `ξ ∈ DualConeFlat Cflat`, the promoted theorem
   `zeroHeadBlockShift_flatTimeShiftDirection_pairing_nonpos_of_mem_dualCone`
   gives `lam ξ ≤ 0`, hence `r ξ = -lam ξ / (2π) ≥ 0`.
2. `SCV.smoothCutoff_one_of_nonneg` removes the outer cutoff at `r ξ`.
3. `SCV.psiZ_eq_exp_of_nonneg` removes the cutoff inside `ψZt (r ξ)`.
4. The exponent algebra is

```lean
Complex.I * ((2 * Real.pi : ℂ) * (t * Complex.I)) * (r : ℂ)
  = -(2 * Real.pi * t : ℂ) * (r : ℂ)
```

so the horizontal scalar becomes

```lean
base *
  Complex.exp (-(2 * Real.pi * ε : ℂ) * r) *
  Complex.exp (-(2 * Real.pi * t : ℂ) * r)
```

with `r = -lam / (2 * Real.pi)`.

Implementation-ready cutoff-removal theorem:

```lean
private theorem horizontalPaley_phase_xIntegral_eq_of_nonneg
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (base : ℂ) (lam : ℝ)
    (hr : 0 ≤ -lam / (2 * Real.pi)) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
      SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
        (by
          have hscaled : 0 < (2 * Real.pi) *
              (((x : ℂ) + ε * Complex.I).im) :=
            mul_pos Real.two_pi_pos (by simpa using hε)
          simpa [Complex.mul_im] using hscaled)
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    ∫ x : ℝ,
      (base * (ψZxε x) (-lam / (2 * Real.pi))) *
      (SchwartzMap.fourierTransformCLM ℂ ψZt) x =
    base *
      (Complex.exp (-(2 * Real.pi * ε : ℂ) * (-lam / (2 * Real.pi))) *
       Complex.exp (-(2 * Real.pi * t : ℂ) * (-lam / (2 * Real.pi)))) := by
  classical
  let r : ℝ := -lam / (2 * Real.pi)
  let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
    SCV.schwartzPsiZ
      ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
      (by
        have hscaled : 0 < (2 * Real.pi) *
            (((x : ℂ) + ε * Complex.I).im) :=
          mul_pos Real.two_pi_pos (by simpa using hε)
        simpa [Complex.mul_im] using hscaled)
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  have hr' : 0 ≤ r := by simpa [r] using hr
  have hcut : (SCV.smoothCutoff r : ℂ) = 1 := by
    exact_mod_cast SCV.smoothCutoff_one_of_nonneg hr'
  have hψt :
      ψZt r = Complex.exp (-(2 * Real.pi * t : ℂ) * (r : ℂ)) := by
    calc
      ψZt r
          = SCV.psiZ ((2 * Real.pi : ℂ) * (t * Complex.I)) r := by
              simp [ψZt]
      _ = Complex.exp
            (Complex.I * ((2 * Real.pi : ℂ) * (t * Complex.I)) * (r : ℂ)) := by
            rw [SCV.psiZ_eq_exp_of_nonneg hr']
      _ = Complex.exp (-(2 * Real.pi * t : ℂ) * (r : ℂ)) := by
            congr 1
            calc
              Complex.I * ((2 * Real.pi : ℂ) * (t * Complex.I)) * (r : ℂ)
                  = (Complex.I * Complex.I) *
                      ((2 * Real.pi * t : ℂ) * (r : ℂ)) := by ring
              _ = -(2 * Real.pi * t : ℂ) * (r : ℂ) := by
                    simp [Complex.I_mul_I]
  have hcollapse :=
    horizontalPaley_phase_xIntegral_eq (hε := hε) (ht := ht)
      (base := base) (lam := lam)
  have hmain :
      (∫ x : ℝ,
        (base * (ψZxε x) r) *
        (SchwartzMap.fourierTransformCLM ℂ ψZt) x) =
      base *
        (Complex.exp (-(2 * Real.pi * ε : ℂ) * (r : ℂ)) *
         Complex.exp (-(2 * Real.pi * t : ℂ) * (r : ℂ))) := by
    calc
      (∫ x : ℝ,
        (base * (ψZxε x) r) *
        (SchwartzMap.fourierTransformCLM ℂ ψZt) x)
          = base *
              ((SCV.smoothCutoff r : ℂ) *
                Complex.exp (-(2 * Real.pi * ε : ℂ) * (r : ℂ)) *
                ψZt r) := by
              simpa [r, ψZxε, ψZt] using hcollapse
      _ = base *
            (Complex.exp (-(2 * Real.pi * ε : ℂ) * (r : ℂ)) *
             Complex.exp (-(2 * Real.pi * t : ℂ) * (r : ℂ))) := by
            rw [hcut, hψt]
            ring
  simpa [r, ψZxε, ψZt] using hmain
```

Implementation-ready dual-cone sign bridge:

```lean
private theorem horizontalPaley_frequency_nonneg_of_mem_dualCone
    {n m : ℕ}
    {ξ : Fin ((n + m) * (d + 1)) → ℝ}
    (hξ : ξ ∈ DualConeFlat
      ((flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m))) :
    0 ≤ -(∑ i,
      (((OSReconstruction.castFinCLE
          (Nat.add_mul n m (d + 1)).symm)
        (OSReconstruction.zeroHeadBlockShift
          (m := n * (d + 1)) (n := m * (d + 1))
          (flatTimeShiftDirection d m))) i) * ξ i) / (2 * Real.pi) := by
  have hlam :=
    zeroHeadBlockShift_flatTimeShiftDirection_pairing_nonpos_of_mem_dualCone
      (d := d) (n := n) (m := m) (ξ := ξ) hξ
  have hden_nonneg : 0 ≤ 2 * Real.pi := Real.two_pi_pos.le
  refine div_nonneg ?_ hden_nonneg
  exact neg_nonneg.mpr (by simpa using hlam)
```

Proof transcript:

1. Introduce `ξ hξ` and rewrite both kernels by their Fubini pointwise
   formulas.
2. On the `KHorizontal` side, rewrite `timeShiftFlatOrbit` by
   `physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift_apply` with
   `a := τ • flatTimeShiftDirection d m` and `Ψ := Ψ`. The scalar phase
   simplifies to

```lean
Complex.exp (-(Complex.I * (lam ξ : ℂ) * τ)) * base ξ
```

   using `map_smul`, `Finset.mul_sum`, and commutative-ring normalization.
3. Replace the `τ`-integral against `χHorizontal` by the universal horizontal
   Fubini identity instantiated at `TWξ`. The result is

```lean
∫ x : ℝ,
  base ξ *
    (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) (r ξ) *
    (SchwartzMap.fourierTransformCLM ℂ ψZt) x
```

   after `integral_phase_mul_fourierTransform_eq_eval`.
4. Use Fourier inversion to convert the preceding `x`-integral. The planned
   Lean route is to rewrite with
   `psiZ_twoPi_pairing_formula` in the contrapositive orientation already used
   in `PaleyWiener.lean`: the `x`-integral of the horizontal
   `ψ_{2π(x+εi)}` pairing against `𝓕ψ_{2πit}` evaluates to

```lean
smoothCutoff (r ξ) *
  Complex.exp (-(2 * Real.pi * ε : ℂ) * (r ξ)) *
  ψZt (r ξ)
```

   and `0 ≤ r ξ` makes both one-variable smooth cutoffs equal to `1`.
5. Therefore the horizontal kernel becomes

```lean
base ξ *
  Complex.exp (-(2 * Real.pi * ε : ℂ) * (r ξ)) *
  Complex.exp (-(2 * Real.pi * t : ℂ) * (r ξ))
```

   with the `t` factor coming from `ψZt (r ξ)` after cutoff removal. Since
   `r ξ = -lam ξ/(2π)`, the product is

```lean
base ξ * Complex.exp ((ε + t : ℂ) * (lam ξ : ℂ))
```

   up to the precise sign conventions already fixed by
   `integral_phase_mul_fourierTransform_eq_eval` and
   `physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift_apply`.
   This algebra must be confirmed in Lean before the theorem is considered
   closed; the signs are not to be adjusted by wrappers.
6. On the `KShell` side, use
   `multiDimPsiZExt_apply_of_mem_dualCone` with `C := Cflat` and `hξ`. This
   rewrites the shell kernel integrand to the pure exponential

```lean
Complex.exp
  (Complex.I *
    ∑ i,
      (flattenCLEquiv q (d + 1) (zShell yflat) i) *
        (ξ i : ℂ)) *
  flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ) yflat
```

   Expanding `zShell` gives

```lean
Complex.exp
  (Complex.I * ∑ i, (yflat i : ℂ) * (ξ i : ℂ)) *
Complex.exp
  (Complex.I * (t : ℂ) * tailTimePair ξ) *
Complex.exp
  (-(ε : ℂ) * ηCanonicalPair ξ)
```

   where

```lean
tailTimePair ξ =
  ∑ k : Fin m, ξ (finProdFinEquiv (Fin.natAdd n k, (0 : Fin (d + 1))))

ηCanonicalPair ξ =
  ∑ k : Fin (n + m), ((k : ℕ) + 1 : ℝ) *
    ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))
```

   and the promoted BVLimits sign convention gives
   `lam ξ = -tailTimePair ξ`. Thus the shell scalar is oscillatory in `t`:

```lean
base ξ *
  Complex.exp (-(Complex.I * (t : ℂ) * (lam ξ : ℂ))) *
  Complex.exp (-(ε : ℂ) * ηCanonicalPair ξ)
```

   This is not the horizontal damping scalar from step 5. Consequently the
   raw `KShell = KHorizontal` EqOn must not be implemented.
7. The remaining live bridge must reintroduce the Section-4.3 transport
   hypotheses and prove equality at the scalar level required by the consumer,
   not by asserting an arbitrary ambient shell/horizontal EqOn.

The zero-residual theorem below is therefore retained only as a conditional
diagnostic reducer. Its hypothesis must be supplied by a transported theorem,
not by the withdrawn raw EqOn:

```lean
private theorem
    bvt_F_canonical_xiShift_shell_sub_horizontal_tendsto_zero
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {t : ℝ} (ht : 0 < t) :
    let ψZ : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y) -
        (∫ x : ℝ,
          bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc φ ψ hψ_compact (↑x + ↑ε * Complex.I) *
          (SchwartzMap.fourierTransformCLM ℂ ψZ) x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0)
```

Proof transcript:

1. On `nhdsWithin 0 (Set.Ioi 0)`, introduce `hε : 0 < ε`.
2. Rewrite the horizontal term by
   `bvt_F_canonical_xiShift_shell_sub_horizontal_eventually_eq_shell_sub_iterated_fourierLaplaceIntegral`.
3. Apply the finite-height equality
   `bvt_F_canonical_xiShift_shell_eq_iterated_fourierLaplaceIntegral`.
4. The residual is eventually the constant zero function, hence tends to `0`.

After this theorem, the already-existing reducer
`tendsto_bvt_F_canonical_xiShift_to_ambientCanonicalExtension_imagAxis_of_shell_sub_horizontal_tendsto_zero`
supplies the `hlimit` hypothesis of
`lemma42_matrix_element_time_interchange` with
`H := bvt_W_conjTensorProduct_timeShiftCanonicalExtension ...`.

The following raw packet is retained only as the superseded draft that motivated
the correction above. It must not be used as an implementation target unless a
new proof first replaces the false raw tube-support theorem with a valid
permuted/translated tube representative and tracks the resulting Fourier
factors.

Retired raw packet draft:

Let

```lean
let q : ℕ := n + m
let M : ℕ := q * (d + 1)
let C : Set (Fin q → Fin (d + 1) → ℝ) := ForwardConeAbs d q
let Cflat : Set (Fin M → ℝ) := (flattenCLEquivReal q (d + 1)) '' C
let yOfFlat : (Fin M → ℝ) → NPointDomain d q :=
  fun yflat => (flattenCLEquivReal q (d + 1)).symm yflat
let zSplit : (Fin M → ℝ) → Fin q → Fin (d + 1) → ℂ :=
  fun yflat =>
    xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      (fun i => wickRotatePoint (yOfFlat yflat i))
      ((t : ℂ) * Complex.I)
let zSplitFlat : (Fin M → ℝ) → Fin M → ℂ :=
  fun yflat => flattenCLEquiv q (d + 1) (zSplit yflat)
let fTransport : SchwartzMap (Fin M → ℝ) ℂ :=
  flattenSchwartzNPoint (d := d) (f.1.osConjTensorProduct g.1)
```

The exact support theorem needed to justify the FL rewrite under the
single-split integral is:

```lean
private theorem zSplit_mem_forwardTube_of_osConjTensorProduct_support
    {n m : ℕ} (hm : 0 < m)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    {t : ℝ} (ht : 0 < t)
    {yflat : Fin ((n + m) * (d + 1)) → ℝ}
    (hy :
      yflat ∈ tsupport
        ((flattenSchwartzNPoint (d := d) (f.1.osConjTensorProduct g.1) :
            SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ) :
          (Fin ((n + m) * (d + 1)) → ℝ) → ℂ)) :
    let y : NPointDomain d (n + m) :=
      (flattenCLEquivReal (n + m) (d + 1)).symm yflat
    xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I) ∈
        TubeDomainSetPi (ForwardConeAbs d (n + m))
```

Proof transcript for
`zSplit_mem_forwardTube_of_osConjTensorProduct_support`:

1. Transfer `hy` through `flattenSchwartzNPoint` to a support statement for
   `(f.1.osConjTensorProduct g.1) y`.
2. Use the support of `osConjTensorProduct` to get the left and right
   component support statements. The left statement is for `f.1` after the
   OS conjugation/reversal; the right statement is for `g.1`.
3. Apply the ordered-positive hypotheses `f.2` and `g.2` to the corresponding
   component supports.
4. Unfold `TubeDomainSetPi`, `ForwardConeAbs`, `xiShift`, and
   `wickRotatePoint`. Successive imaginary differences are exactly the
   positive ordered time gaps from the left/right supports, with the split gap
   increased by `t`; positivity of the split gap uses `ht`.
5. The `n = 0` branch has no left support statement; close it by the same
   split-gap computation using the first right point and `ht`.

To make the Fubini family global and continuous, do not branch directly on
`zSplit yflat ∈ TubeDomainSetPi C`; a raw `if` at the tube boundary is not a
sound continuity strategy. Instead introduce a cutoff supported inside the
tube-safe parameter set:

```lean
private theorem exists_transportTubeCutoff
    {n m : ℕ} (hm : 0 < m)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    {t : ℝ} (ht : 0 < t) :
    let q : ℕ := n + m
    let M : ℕ := q * (d + 1)
    let Ω : Set (Fin M → ℝ) :=
      {yflat |
        let y : NPointDomain d q := (flattenCLEquivReal q (d + 1)).symm yflat
        xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I) ∈
            TubeDomainSetPi (ForwardConeAbs d q)}
    ∃ ρ : (Fin M → ℝ) → ℂ,
      ContDiff ℝ ∞ ρ ∧
      HasCompactSupport ρ ∧
      (∀ yflat ∈ tsupport
        ((flattenSchwartzNPoint (d := d) (f.1.osConjTensorProduct g.1) :
            SchwartzMap (Fin M → ℝ) ℂ) :
          (Fin M → ℝ) → ℂ), ρ yflat = 1) ∧
      tsupport ρ ⊆ Ω ∧
      (∀ k : ℕ, ∃ Cρ : ℝ, ∀ yflat, ‖iteratedFDeriv ℝ k ρ yflat‖ ≤ Cρ)
```

Proof transcript for `exists_transportTubeCutoff`:

1. Prove `Ω` is open from `isOpen_tubeDomain`/`forwardConeAbs_isOpen`,
   continuity of `flattenCLEquivReal.symm`, continuity of `wickRotatePoint`,
   and the affine continuity of `xiShift`.
2. Prove the compact set
   `K := tsupport (flattenSchwartzNPoint (f.1.osConjTensorProduct g.1))`
   is contained in `Ω` using
   `zSplit_mem_forwardTube_of_osConjTensorProduct_support`; compactness comes
   from `hf_compact`, `hg_compact`, compact support of `osConjTensorProduct`,
   and transport through `flattenCLEquivReal`.
3. Use the positive distance between compact `K` and the closed complement
   `Ωᶜ`, then apply `exists_smooth_cutoff_of_closed` after translating/scaling
   its fixed-radius cutoff, to get a smooth compactly supported `ρ` with
   `ρ = 1` on `K` and `tsupport ρ ⊆ Ω`.
4. The derivative bounds are inherited from `exists_smooth_cutoff_of_closed`
   and the finite-dimensional affine scaling.

With such a cutoff, the transported Schwartz family is globally defined by:

```lean
let gTransport : (Fin M → ℝ) → SchwartzMap (Fin M → ℝ) ℂ :=
  fun yflat =>
    (ρ yflat) •
      multiDimPsiZExt Cflat
        hCflat_open hCflat_conv hCflat_cone hCflat_salient
        (zSplitFlat yflat)
```

The production side conditions for this family are:

```lean
private theorem continuous_transportPsiZFamily_with_cutoff :
    Continuous gTransport

private theorem seminorm_transportPsiZFamily_with_cutoff_bound :
    ∀ k l : ℕ, ∃ Cg : ℝ, ∃ N : ℕ, Cg > 0 ∧
      ∀ yflat : Fin M → ℝ,
        SchwartzMap.seminorm ℝ k l (gTransport yflat) ≤
          Cg * (1 + ‖yflat‖) ^ N
```

Proof transcript for these two side conditions:

1. If `ρ yflat ≠ 0`, then `yflat ∈ Ω`; locally, `multiDimPsiZExt` rewrites to
   `multiDimPsiZ` and continuity follows from
   `multiDimPsiZ_seminorm_continuous` composed with the affine map
   `zSplitFlat`.
2. If `yflat ∉ tsupport ρ`, then `ρ = 0` on a neighborhood of `yflat`, so
   `gTransport` is locally zero.
3. Seminorm growth follows from compact support of `ρ`: on `tsupport ρ`, the
   image of `zSplitFlat` is contained in a compact subset of the tube, so the
   local uniform seminorm bounds for `multiDimPsiZ` give a uniform constant;
   outside `tsupport ρ`, the family is zero. Conclude with `N := 0`, or absorb
   the compact-region constant into `Cg * (1 + ‖yflat‖)^0`.

The retired draft claimed the transported kernel package would be Lean-ready
as follows. This is now false for the live route because the raw support packet
above does not put `zSplitFlat yflat` in the forward tube:

```lean
private theorem
    exists_transportKernel_pairing_singleSplitXiShiftScalar
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    {t : ℝ} (ht : 0 < t)
    (hCflat_open :
      IsOpen
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_conv :
      Convex ℝ
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_cone :
      IsCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_salient :
      IsSalientCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_supp :
      HasFourierSupportInDualCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)) Tflat)
    (hFL :
      ∀ z : Fin (n + m) → Fin (d + 1) → ℂ,
        z ∈ TubeDomainSetPi (ForwardConeAbs d (n + m)) →
          bvt_F OS lgc (n + m) z =
            fourierLaplaceExtMultiDim
              ((flattenCLEquivReal (n + m) (d + 1)) ''
                ForwardConeAbs d (n + m))
              hCflat_open hCflat_conv hCflat_cone hCflat_salient
              Tflat (flattenCLEquiv (n + m) (d + 1) z)) :
    ∃ KTransport : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
      bvtSingleSplitXiShiftScalar (d := d) OS lgc hm f.1 g.1 t =
        Tflat KTransport ∧
      ∃ ρ : (Fin ((n + m) * (d + 1)) → ℝ) → ℂ,
        ContDiff ℝ ∞ ρ ∧
        HasCompactSupport ρ ∧
        (∀ yflat ∈ tsupport
          ((flattenSchwartzNPoint (d := d) (f.1.osConjTensorProduct g.1) :
              SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ) :
            (Fin ((n + m) * (d + 1)) → ℝ) → ℂ), ρ yflat = 1) ∧
        (∀ ξ, KTransport ξ =
          ∫ yflat : Fin ((n + m) * (d + 1)) → ℝ,
            (((ρ yflat) •
              multiDimPsiZExt
                ((flattenCLEquivReal (n + m) (d + 1)) ''
                  ForwardConeAbs d (n + m))
                hCflat_open hCflat_conv hCflat_cone hCflat_salient
                (flattenCLEquiv (n + m) (d + 1)
                  (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i =>
                      wickRotatePoint
                        (((flattenCLEquivReal (n + m) (d + 1)).symm yflat) i))
                    ((t : ℂ) * Complex.I)))) ξ) *
              (flattenSchwartzNPoint (d := d)
                (f.1.osConjTensorProduct g.1)) yflat)
```

In production, the theorem body obtains `ρ` from `exists_transportTubeCutoff`,
defines the displayed family, proves the two Fubini side conditions from
`continuous_transportPsiZFamily_with_cutoff` and
`seminorm_transportPsiZFamily_with_cutoff_bound`, applies
`schwartz_clm_fubini_exchange`, rewrites the scalar integral by
`bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`, and uses `hFL` on the
support where `ρ = 1` and `fTransport` is nonzero. Outside that support, the
integrand is zero by the Schwartz test factor, so no tube-membership claim is
needed.

For symmetry with the transported package, the ambient Fubini construction can
be implemented as its own small theorem before the hard packet:

```lean
private theorem
    exists_ambientKernel_pairing_psiZTimeShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    {t : ℝ} (ht : 0 < t)
    (Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_bv :
      ∀ φflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
        bvt_W OS lgc (n + m) (unflattenSchwartzNPoint (d := d) φflat) =
          Tflat (physicsFourierFlatCLM φflat)) :
    ∃ KAmbient : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
      let ψZ : SchwartzMap ℝ ℂ :=
        SCV.schwartzPsiZ
          (((2 * Real.pi : ℂ) * (t * Complex.I)))
          (by
            simpa [Complex.mul_im, ht.ne']
              using mul_pos Real.two_pi_pos ht)
      (∫ τ : ℝ,
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          (SchwartzMap.fourierTransformCLM ℂ ψZ) τ) =
          Tflat KAmbient
```

Proof transcript for `exists_ambientKernel_pairing_psiZTimeShift`:

1. Use the displayed `M`, `k`, `hk`, `χhat`, `β`, `fpad0`, `fpad`,
   `ΨAmbient0`, `ambientOrbit`, `headCoord`, and `gAmbient` definitions from
   the hard theorem transcript.
2. Prove `hgAmbient_cont` and `hgAmbient_bound` by the exact copied proof from
   `integral_bvt_W_flattened_translate_mul_fourierTransform_eq_zero_of_negSupport`.
3. Apply `schwartz_clm_fubini_exchange Tflat gAmbient fpad`.
4. Rewrite the scalar pairing field with `hTflat_bv`, the local
   right-tail-shift configuration lemma, `integral_comp_castFinCLE_eq`,
   `integral_finSucc_cons_eq`, `MeasureTheory.integral_prod_mul`, and
   `integral_normedUnitBumpSchwartzPi`, exactly as the existing BVLimits proof
   rewrites `hPair_repr`.
5. Return `KAmbient` and the resulting pair equality. The theorem deliberately
   does not prove the dual-cone EqOn; EqOn is the Section-4.3 comparison in the
   hard packet.

```lean
private theorem
    hardSingleSplit_psiZ_timeShift_expands_to_dualCone_eq_kernel_pairing
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    {t : ℝ} (ht : 0 < t) :
    ∃ Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ,
    ∃ hTflat_supp :
      HasFourierSupportInDualCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)) Tflat,
    ∃ KAmbient KTransport :
      SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
      let ψZ : SchwartzMap ℝ ℂ :=
        SCV.schwartzPsiZ
          (((2 * Real.pi : ℂ) * (t * Complex.I)))
          (by
            simpa [Complex.mul_im, ht.ne']
              using mul_pos Real.two_pi_pos ht)
      (∫ τ : ℝ,
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          (SchwartzMap.fourierTransformCLM ℂ ψZ) τ) =
          Tflat KAmbient ∧
      bvtSingleSplitXiShiftScalar (d := d) OS lgc hm f.1 g.1 t =
          Tflat KTransport ∧
      Set.EqOn
        (KAmbient : (Fin ((n + m) * (d + 1)) → ℝ) → ℂ)
        KTransport
        (DualConeFlat
          ((flattenCLEquivReal (n + m) (d + 1)) ''
            ForwardConeAbs d (n + m)))
```

Implementation transcript for
`hardSingleSplit_psiZ_timeShift_expands_to_dualCone_eq_kernel_pairing`:

1. Define `ψZ` exactly as displayed.
2. Rewrite the shifted right tensor by
   the local configuration lemma below; this is only a configuration-space
   rewrite and does not replace shifted `ψ` by shifted `g`.

```lean
private def rightTailTimeShiftConfig {n m : ℕ} (hm : 0 < m) (t : ℝ)
    (x : NPointDomain d (n + m)) : NPointDomain d (n + m) :=
  fun i =>
    if n ≤ i.val then x i + timeShiftVec d t else x i

private theorem conjTensorProduct_timeShift_eq_rightTailTimeShift
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (τ : ℝ) (x : NPointDomain d (n + m)) :
    (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) x =
      (φ.conjTensorProduct ψ)
        (rightTailTimeShiftConfig (d := d) (n := n) (m := m) hm (-τ) x) := by
  -- Same proof as the private `conjTensorProduct_timeShift_eq_tailTimeShift`
  -- in `OSToWightman.lean`, but restated locally because that theorem and
  -- `tailTimeShiftConfig` are private there.
  simp only [SchwartzMap.conjTensorProduct_apply, timeShiftSchwartzNPoint_apply]
  congr 1
  · ext i μ
    have hi : ¬ n ≤ (Fin.castAdd m i).val := by
      simpa using (not_le_of_gt i.isLt)
    simp [rightTailTimeShiftConfig, hi]
  · ext j μ
    have hj : n ≤ (Fin.natAdd n j).val := by simp
    simp [rightTailTimeShiftConfig, hj, timeShiftVec, sub_eq_add_neg]
```

   Do not call the private imported `conjTensorProduct_timeShift_eq_tailTimeShift`
   from `OSToWightman.lean` in production; either keep the local lemma above in
   the target file or deliberately promote the configuration lemma to a public
   support theorem with a narrow exact-file check.
3. Flatten the full configuration with `flattenCLEquivReal (n + m) (d + 1)`.
   Do **not** try to force the ambient and transported sides into the same
   translated base `Ψ`. The representative data appear in the full Fourier-side
   kernel. The correct outputs are `KAmbient` and `KTransport`, together with
   pointwise formulas for those kernels on the dual cone.
4. Obtain the common distribution package:

```lean
obtain ⟨Tflat, hCflat_open, hCflat_conv, hCflat_cone, hCflat_salient,
  hTflat_supp, hTflat_bv, hTflat_FL⟩ :=
  exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr
    (d := d) OS lgc (n + m)
```

   The ambient pairing will use `hTflat_bv`; the transported shell will use
   `hTflat_FL`.
5. Construct the ambient kernel by the existing translated-orbit Fubini pattern:

```lean
let M : ℕ := (n + m) * (d + 1)
have hM_pos : 0 < M := by
  dsimp [M]
  have hnm_pos : 0 < n + m := by omega
  exact Nat.mul_pos hnm_pos (Nat.succ_pos _)
let k : ℕ := M - 1
have hk : k + 1 = M := by
  dsimp [k]
  exact Nat.succ_pred_eq_of_pos hM_pos
let χhat : SchwartzMap ℝ ℂ := SchwartzMap.fourierTransformCLM ℂ ψZ
let β : SchwartzMap (Fin k → ℝ) ℂ := normedUnitBumpSchwartzPi k
let fpad0 : SchwartzMap (Fin (k + 1) → ℝ) ℂ := χhat.prependField β
let fpad : SchwartzMap (Fin M → ℝ) ℂ :=
  OSReconstruction.reindexSchwartzFin hk fpad0
let ΨAmbient0 : SchwartzMap (Fin (n * (d + 1) + m * (d + 1)) → ℝ) ℂ :=
  (flattenSchwartzNPoint (d := d) φ.borchersConj).tensorProduct
    (flattenSchwartzNPoint (d := d) ψ)
let ambientOrbit : ℝ → SchwartzMap (Fin M → ℝ) ℂ :=
  fun τ =>
    physicsFourierFlatCLM
      (OSReconstruction.reindexSchwartzFin
        (by ring : n * (d + 1) + m * (d + 1) = M)
        (SCV.translateSchwartz
          (OSReconstruction.zeroHeadBlockShift
            (m := n * (d + 1)) (n := m * (d + 1))
            (τ • flatTimeShiftDirection d m))
          ΨAmbient0))
let headCoord : (Fin M → ℝ) → ℝ :=
  fun x => ((OSReconstruction.castFinCLE hk).symm x) 0
let gAmbient : (Fin M → ℝ) → SchwartzMap (Fin M → ℝ) ℂ :=
  fun x => ambientOrbit (headCoord x)
```

   The continuity and seminorm-growth proofs are copied from
   `integral_bvt_W_flattened_translate_mul_fourierTransform_eq_zero_of_negSupport`:
   use
   `continuous_physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift` and
   `exists_bound_seminorm_physicsFourierFlatCLM_reindex_translate_zeroHeadBlockShift`
   with `Ψ := ΨAmbient0`. Apply Fubini:

```lean
obtain ⟨KAmbient, hKAmbient_eval, hKAmbient_pair⟩ :=
  schwartz_clm_fubini_exchange Tflat gAmbient fpad
    hgAmbient_cont hgAmbient_bound
```

   Its pair field rewrites the left scalar to `Tflat KAmbient` after
   `hTflat_bv` rewrites each translated Wightman value and
   `integral_comp_castFinCLE_eq`/`integral_normedUnitBumpSchwartzPi` collapse
   the padded variables.
6. Construct the transported kernel by the new transport package:

```lean
obtain ⟨KTransport, hKTransport_pair, ρ, hρ_smooth, hρ_compact,
  hρ_one_on_support, hKTransport_eval⟩ :=
  exists_transportKernel_pairing_singleSplitXiShiftScalar
    (d := d) OS lgc hm f g hf_compact hg_compact ht
    hCflat_open hCflat_conv hCflat_cone hCflat_salient
    Tflat hTflat_supp hTflat_FL
```

   This Fubini call uses the flattened positive-time test
   `flattenSchwartzNPoint (d := d) (f.1.osConjTensorProduct g.1)`, not `fpad`.
   The equality `hKTransport_pair` is obtained from the FL representation of
   `bvt_F`; it does not use the Wightman boundary representation and therefore
   is not circular.
7. Apply the public `psiZ_twoPi_pairing_formula` only to the real
   time-shift variable `τ`. The expected exponential is
   `Complex.exp (-(2 * Real.pi * t : ℂ) * ξ)` with the sign/normalization from
   `psiZ_pairing_formula`; do not use `SCV.psiZ_eq_exp_of_nonneg` here.
8. The pair equalities are obtained from the two Fubini pair fields:
   `hKAmbient_pair` rewrites the Wightman `ψ_Z`-paired time-shift integral to
   `Tflat KAmbient`.
   `hKTransport_pair` rewrites `bvtSingleSplitXiShiftScalar ...` to
   `Tflat KTransport` through
   `bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq`, the FL representation,
   support-safe cutoff identity `ρ = 1` on the test support, and Fubini.
9. Prove the dual-cone EqOn conjunct by introducing `ξ hξ` and rewriting both
   sides with `hKAmbient_eval ξ` and `hKTransport_eval ξ`. These are not the
   same raw parameter integral. First normalize both pointwise formulas:
   expand `physicsFourierFlatCLM` on the ambient side, apply
   `psiZ_twoPi_pairing_formula` to the `τ` integral, and rewrite the
   transported side by `multiDimPsiZExt_eq` on the cutoff support plus
   `multiDimPsiZR_eval_eq_of_support`/`fourierLaplaceExtMultiDim_eq_dynamic`
   on the dual cone. After these rewrites both pointwise values are expressed
   as the same full spatial/time-slice integral, except that the ambient slices
   are `φ`, `ψ` and the transported slices are `f.1`, `g.1`.
10. At that normalized pointwise equality, extract the nonnegative absolute-time
   data from `hξ ∈ DualConeFlat ((flattenCLEquivReal ...) '' ForwardConeAbs ...)`.
   Use the already documented tail-direction sign lemmas to show the cumulative
   tail time coordinates are nonnegative:

```lean
have htail_nonneg :
    ∀ j : Fin (n + m), 0 ≤
      -(∑ a, flatTailTimeShiftDirection d (n + m) j a * ξ a) := by
  intro j
  have hle :=
    flatTailTimeShiftDirection_pairing_nonpos_of_mem_dualCone
      (d := d) (q := n + m) j hξ
  linarith
```

   Convert these cumulative tail values to
   `absTimesOfTailGapsSplitLeft`, `absTimesOfTailGapsSplitRight`, and, if
   needed, `absTimesOfTailGapsSplitLeftRev`. These are the nonnegative
   background times required by the existing Section-4.3 slice lemmas.
11. If the expanded left factor is exposed as `φ.borchersConj`, call the
   Section-4.3 slice bridge on the reversed vector
   `absTimesOfTailGapsSplitLeftRev` with nonnegativity from the previous dual
   cone tail-direction calculation. The right factor uses the unreversed
   `absTimesOfTailGapsSplitRight` vector.
12. Use
   `partialFourierSpatial_fun_eq_of_repr_eq_transport_on_nonneg` when the
   kernel contains full partial-spatial Fourier values, and use
   `unshifted_full_timeOrthant_descended_pairing_eq_of_section43Transport`
   only when the expansion has already isolated a one-variable
   `fourierInvPairingCLM`.
13. The `n = 0` branch bypasses all left slices via
   `section43_zero_left_repr_eq_transport_pointwise`; the same `Ψ` certificate
   is no longer required. The right-factor kernel and dual-cone EqOn proof are
   still produced.
14. The proof of the hard theorem then destructs this packet, applies
    `tflat_pairing_eq_of_eqOn_dualCone` to the EqOn
    conjunct, and closes by transitivity of the two expansion equalities.

Analytic obligations for the full-kernel packet:

1. The outer real-time pairing is introduced through
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply` with
   `χ := (SchwartzMap.fourierTransformCLM ℂ) ψZ`. This supplies the exact
   scalar integral and avoids proving ad hoc integrability of the
   `τ`-integrand.
2. The one-sided support fact available for the Wightman time-shift functional
   is
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport`;
   use it only for quotient/descent statements, not as a replacement for the
   concrete expansion equalities.
3. The Fubini/Schwartz-family exchange used to construct `KAmbient` and
   `KTransport` must be an application of `schwartz_clm_fubini_exchange` or of
   a theorem already proved from it. For `KAmbient`, the side conditions are
   the copied translated-orbit continuity and seminorm-growth lemmas from
   BVLimits. For `KTransport`, the side conditions are exactly
   `continuous_transportPsiZFamily_with_cutoff` and
   `seminorm_transportPsiZFamily_with_cutoff_bound`.
4. Existing BVLimits growth lemmas may be reused only when the new
   `gAmbient`/`gTransport` family is definitionally the same translated orbit
   already covered there. If the expansion introduces a different finite orbit,
   first prove the analogue of the continuity and seminorm-growth lemmas for
   that exact family; do not silently reuse the right-block
   `zeroHeadBlockShift` estimates.
5. The public `psiZ_twoPi_pairing_formula` is the only Paley-Wiener identity
   needed in the packet. It is already available in `SCV/PaleyWiener.lean`;
   no additional export step is part of the current route.
6. The packet's final EqOn proof is pointwise in all remaining spatial/Fubini
   parameters. Those parameters must be introduced before the EqOn proof, not
   hidden behind extensional equality of two large integrals.

Retired readiness guard for this packet:

1. This raw packet is no longer Lean-ready because its tube-support premise is
   false. The apparent cutoff/Fubini completion would invoke the
   Fourier-Laplace representation outside its domain.
2. The `Set.EqOn KAmbient KTransport dualCone` idea remains mathematically
   useful, but the transport side must be rebuilt on a valid finite-height
   canonical shell, not on the raw `singleSplit` surface.
3. The active implementation order is the transported scalar-bridge order in
   §5.9.4a.1.ε after the 2026-04-13 scalar mismatch correction. In particular,
   the names
   `zSplit_mem_forwardTube_of_osConjTensorProduct_support`,
   `exists_transportTubeCutoff`,
   `exists_transportKernel_pairing_singleSplitXiShiftScalar`, and
   `hardSingleSplit_psiZ_timeShift_expands_to_dualCone_eq_kernel_pairing`
   must not be added to production for the current route.

The active positive-support theorem for hPsi is the direct spectral version
below. It is not a corollary of a hard single-split theorem; the single-split
surface is retired for the current route.

```lean
private theorem
    integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_selfAdjointSpectralLaplaceOffdiag_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g) :
    let A : OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS :=
      osTimeShiftHilbert (d := d) OS lgc 1 one_pos
    let hA : IsSelfAdjoint A :=
      osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos
    let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single n f.1 f.2⟧)) : OSHilbertSpace OS))
    let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single m g.1 g.2⟧)) : OSHilbertSpace OS))
    ∀ t : ℝ, ∀ ht : 0 < t,
      let ψZ : SchwartzMap ℝ ℂ :=
        SCV.schwartzPsiZ
          (((2 * Real.pi : ℂ) * (t * Complex.I)))
          (by
            simpa [Complex.mul_im, ht.ne']
              using mul_pos Real.two_pi_pos ht)
      (∫ τ : ℝ,
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          (SchwartzMap.fourierTransformCLM ℂ ψZ) τ) =
        ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag A hA xF xG (t : ℂ)
```

Proof transcript for the expanded positive-support theorem:

1. Fix `t ht` and introduce `ψZ`, `A`, `hA`, `xF`, and `xG`.
2. Rewrite the left side by
   `integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_fourierPairingDescendsToSection43PositiveEnergy1D`.
3. Expand the descended pairing only by
   `fourierPairingDescendsToSection43PositiveEnergy1D_apply` and
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply`.
4. Apply the Section-4.3 transported slice comparison for the quotient class
   of `ψZ`. This is the hard step: it converts the Wightman time-shift
   distribution paired against `𝓕ψZ` to the OS off-diagonal time-shift
   distribution on the Hilbert vectors `xF`, `xG`. It must use `hφf` and
   `hψg` through quotient/slice lemmas only.
5. Rewrite the OS off-diagonal time-shift scalar by
   `OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag`.
6. Close by `simpa [ψZ, A, hA, xF, xG]`. If Lean exposes a mismatch here, it is
   either a local abbreviation mismatch or an explicit missing slice bridge;
   record the exact goal before adding support lemmas.

Circularity guard for this theorem:

1. Do not use
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imag_eq_osHolomorphicValue_of_ambient_descended_psiZ_boundaryValue_eq`
   or
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imag_eq_osHolomorphicValue_of_section43Transport`.
   Those theorems consume the descended `ψ_Z`/hPsi equality that this theorem
   is meant to supply.
2. Do not use
   `bvt_W_conjTensorProduct_timeShift_boundaryValue_fourierTransform_eq_of_ambient_canonicalExtension_imag_eq_osHolomorphicValue`.
   It assumes the positive-imaginary-axis canonical-to-OS equality and then
   derives boundary-value Fourier-transform equality; using it here would be a
   proof loop.
3. Do not use `lemma42_matrix_element_time_interchange` or
   `lemma42_matrix_element_time_interchange_of_section43Transport`. These are
   consumers after the shell limit and hPsi are available.
4. Do not use
   `integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_singleSplitXiShiftScalar_of_section43Transport`
   or any theorem with `bvtSingleSplitXiShiftScalar` in its statement. That
   route is optional downstream diagnostics only; it is no longer a live proof
   dependency.

The descended off-diagonal theorem consumed by `hPsi` is then:

```lean
private theorem
    descendedPsiZ_boundaryValue_eq_selfAdjointSpectralLaplaceOffdiag_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g) :
    let A : OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS :=
      osTimeShiftHilbert (d := d) OS lgc 1 one_pos
    let hA : IsSelfAdjoint A :=
      osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos
    let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single n f.1 f.2⟧)) : OSHilbertSpace OS))
    let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
      (⟦PositiveTimeBorchersSequence.single m g.1 g.2⟧)) : OSHilbertSpace OS))
    ∀ t : ℝ, ∀ ht : 0 < t,
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
          (d := d) OS lgc φ ψ hψ_compact)
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm φ ψ hψ_compact)
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (t * Complex.I)))
            (by
              simpa [Complex.mul_im, ht.ne']
                using mul_pos Real.two_pi_pos ht))) =
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag A hA xF xG (t : ℂ)
```

Proof transcript for the off-diagonal core theorem:

1. Introduce `ψZ`, `A`, `hA`, `xF`, and `xG`.
2. Expand the descended Wightman side only with
   `fourierPairingDescendsToSection43PositiveEnergy1D_apply` and
   `bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply`.
3. Apply
   `integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_selfAdjointSpectralLaplaceOffdiag_of_section43Transport`
   at the same `t ht`.
4. Close by `simpa [ψZ, A, hA, xF, xG]`.
5. Do not use `selfAdjointSpectralBoundaryValueOffdiag_eq_selfAdjointSpectralLaplaceOffdiag_psiZ`
   in this core theorem; that theorem belongs to the final one-line conversion
   from Laplace offdiag to spectral boundary offdiag.
6. Do not introduce any theorem whose statement needs
   `HasCompactSupport (φ : NPointDomain d n → ℂ)`. Such a theorem is on the
   wrong surface for the live consumer.

Implementation transcript for this `hPsi` theorem:

1. Introduce, for fixed `t ht`, the local names
   `ψZ`, `A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos`,
   `hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos`,
   `xF`, and `xG`.
2. Let `hLaplace` be
   `descendedPsiZ_boundaryValue_eq_selfAdjointSpectralLaplaceOffdiag_of_section43Transport`
   specialized at `t ht`.
3. Rewrite the right side with `selfAdjointSpectralBoundaryValueOffdiagCLM_apply`.
4. Rewrite the resulting scalar with
   `selfAdjointSpectralBoundaryValueOffdiag_eq_selfAdjointSpectralLaplaceOffdiag_psiZ`
   using
   `spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos`.
5. Close by transitivity through the common scalar
   `ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag A hA xF xG (t : ℂ)`,
   then `simpa [A, hA, xF, xG, ψZ]`.

Exact linearity helper slots for OS-side bookkeeping:

These helpers are still useful if Lean needs to simplify the OS Hilbert vectors
appearing in local semigroup rewrites, but they are **not** a license to
polarize the Wightman side. They should never introduce a compactness
hypothesis for `φ`.

The two Section-4.3 maps have been checked against production declarations in
`Section43Codomain.lean`:

```lean
section43PositiveEnergyQuotientMap (d := d) n :
  SchwartzNPoint d n →L[ℂ] Section43PositiveEnergyComponent (d := d) n

os1TransportComponent d n :
  euclideanPositiveTimeSubmodule (d := d) n →L[ℂ]
    Section43PositiveEnergyComponent (d := d) n
```

Therefore all component transport linearity needed for OS-side local
bookkeeping is ordinary `map_add`/`map_smul`. Add this exact helper theorem
immediately before
`descendedPsiZ_boundaryValue_eq_osSpectral_of_section43Transport`:

```lean
private theorem section43Transport_component_linear_comb_single_single
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    (a b : ℂ) :
    let Φ : BorchersSequence d :=
      a • BorchersSequence.single n φ + b • BorchersSequence.single m ψ
    let F : PositiveTimeBorchersSequence d :=
      a • PositiveTimeBorchersSequence.single n f.1 f.2 +
      b • PositiveTimeBorchersSequence.single m g.1 g.2
    ∀ k : ℕ,
      section43PositiveEnergyQuotientMap (d := d) k (Φ.funcs k) =
        os1TransportComponent d k
          ⟨((F : BorchersSequence d).funcs k), F.ordered_tsupport k⟩
```

Proof transcript:

1. `intro k`.
2. `dsimp` the local `Φ` and `F`.
3. Close by `simp` with
   `BorchersSequence.add_funcs`, `BorchersSequence.smul_funcs`,
   `PositiveTimeBorchersSequence.add_toBorchersSequence`,
   `PositiveTimeBorchersSequence.smul_toBorchersSequence`,
   `PositiveTimeBorchersSequence.single_toBorchersSequence`,
   `os1TransportComponent_apply`, `map_add`, `map_smul`, `hφf`, and `hψg`.
4. The cases `k = n`, `k = m`, `n = m`, and the off-support zero cases are all
   componentwise `simp` cases of the same statement; do not split them into
   four separate theorem surfaces.

The exact helper theorem for the OS Hilbert vectors is the corresponding class
linearity in the OS quotient completion:

```lean
private theorem osHilbertClass_linear_comb_single_single
    (OS : OsterwalderSchraderAxioms d)
    {n m : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (a b : ℂ) :
    let F₀ : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single n f.1 f.2
    let G₀ : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single m g.1 g.2
    (((show OSPreHilbertSpace OS from (⟦a • F₀ + b • G₀⟧)) :
        OSHilbertSpace OS)) =
      a • (((show OSPreHilbertSpace OS from (⟦F₀⟧)) :
        OSHilbertSpace OS)) +
      b • (((show OSPreHilbertSpace OS from (⟦G₀⟧)) :
        OSHilbertSpace OS))
```

Proof transcript:

1. `dsimp` the local `F₀` and `G₀`.
2. Change the left OS pre-Hilbert class to
   `a • (⟦F₀⟧ : OSPreHilbertSpace OS) + b • (⟦G₀⟧ : OSPreHilbertSpace OS)`.
   This is justified by the quotient `Add`/`SMul` instances in
   `SchwingerOS.lean`.
3. Push the equality into the completion with
   `UniformSpace.Completion.coe_add` and
   `UniformSpace.Completion.coe_smul`.
4. Finish by `simpa`.

The four OS-side expanded-boundary bookkeeping instantiations are exactly:

```lean
section43Transport_component_linear_comb_single_single
  (d := d) φ ψ f g hφf hψg 1 1
section43Transport_component_linear_comb_single_single
  (d := d) φ ψ f g hφf hψg 1 (-1)
section43Transport_component_linear_comb_single_single
  (d := d) φ ψ f g hφf hψg 1 Complex.I
section43Transport_component_linear_comb_single_single
  (d := d) φ ψ f g hφf hψg 1 (-Complex.I)

osHilbertClass_linear_comb_single_single
  (d := d) OS f g 1 1
osHilbertClass_linear_comb_single_single
  (d := d) OS f g 1 (-1)
osHilbertClass_linear_comb_single_single
  (d := d) OS f g 1 Complex.I
osHilbertClass_linear_comb_single_single
  (d := d) OS f g 1 (-Complex.I)
```

Use `simpa [sub_eq_add_neg, one_smul]` to match the theorem outputs to the
four terms `xF + xG`, `xF - xG`, `xF + Complex.I • xG`, and
`xF - Complex.I • xG` produced by
`selfAdjointSpectralBoundaryValueOffdiagCLM_apply`.

With that `hPsi` theorem, the canonical witness is identified with the OS
holomorphic matrix element by direct application of the existing reducer:

```lean
private theorem
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imag_eq_osHolomorphicValue_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g) :
    ∀ t : ℝ, 0 < t →
      bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I) =
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f.1 f.2)
        (PositiveTimeBorchersSequence.single m g.1 g.2) (t : ℂ)
```

Proof transcript:

1. Apply
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imag_eq_osHolomorphicValue_of_ambient_descended_psiZ_boundaryValue_eq`
   with `f := f.1`, `hf_ord := f.2`, `g := g.1`, `hg_ord := g.2`.
2. Supply its `hPsi` hypothesis with
   `descendedPsiZ_boundaryValue_eq_osSpectral_of_section43Transport`.

The direct Lemma-4.2 adapter for transported-image representatives is then:

```lean
theorem lemma42_matrix_element_time_interchange_of_section43Transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) m)
    (hf_compact : HasCompactSupport (f.1 : NPointDomain d n → ℂ))
    (hg_compact : HasCompactSupport (g.1 : NPointDomain d m → ℂ))
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g) :
    bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.1.osConjTensorProduct g.1))
```

Proof transcript:

1. Apply `lemma42_matrix_element_time_interchange` with
   `H := fun z =>
      bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc φ ψ hψ_compact z`.
2. Supply `hH_imag_os` from
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imag_eq_osHolomorphicValue_of_section43Transport`.
3. Supply `hlimit` from
   `tendsto_bvt_F_canonical_xiShift_to_canonicalExtension_imagAxis_of_section43Transport`.

Readiness rule for this subsection:

1. No theorem without `hφf` and `hψg` may conclude a shell-to-canonical,
   real-time-to-Laplace, or Wightman-to-OS scalar identity.
2. Arbitrary-`φ, ψ` residual theorems may only compute obstruction limits; they
   must not be used as zero-limit targets.
3. As of the corrected 2026-04-13 readiness audit, the raw
   single-split/cutoff packet is retired. The support lemmas
   `tflat_pairing_eq_of_eqOn_dualCone`, `psiZ_twoPi_pairing_formula`, and
   `exists_flattened_bvt_F_dualCone_distribution_with_fourierLaplace_repr`
   have already been implemented and checked. The canonical positive-height
   shell packet and the horizontal Paley packet may be used only as diagnostic
   normal forms unless Section-4.3 transport hypotheses `hφf` and `hψg` are
   present in the theorem statement.
4. The direct pointwise theorem
   `bvt_W_timeShift_sub_descendedPsiZ_zero_of_section43Transport` remains
   forbidden. The current shell-to-OS route must go through a transported
   scalar bridge; the raw finite-height canonical-shell/horizontal dual-cone
   EqOn is withdrawn because it would identify a real-time oscillatory shell
   with an imaginary-axis Laplace damping factor for arbitrary `φ, ψ`.
5. Auxiliary Lean lemmas before the finite-height canonical-shell theorem are
   allowed only for one of the explicitly displayed obligations in
   §5.9.4a.1.ε: canonical tube membership, shell-side `Tflat` Fubini,
   horizontal/iterated `Tflat` Fubini, the `ψ_Z` kernel calculation inside
   that Fubini exchange, or Section-4.3 transported scalar bridge work. No raw
   `singleSplit` tube-support lemma, cutoff package, arbitrary-`φ,ψ`
   shell-minus-horizontal zero theorem, or administrative decomposition may be
   introduced.
6. The hPsi compactness correction remains sound: use the direct off-diagonal
   helper
   `descendedPsiZ_boundaryValue_eq_selfAdjointSpectralLaplaceOffdiag_of_section43Transport`
   and never Wightman-side diagonal polarization. Any theorem that asks for
   `HasCompactSupport (φ : NPointDomain d n → ℂ)` has left the live surface.
7. If Lean implementation exposes a genuine mathematical or type-level gap not
   covered by the displayed theorem slots, stop production edits and return to
   this proof-doc section first. Do not patch around the gap with wrappers or a
   weaker theorem shape.
8. After the limit-level canonical residual theorem is proved, feed it into the
   existing reducer
   `tendsto_bvt_F_canonical_xiShift_to_ambientCanonicalExtension_imagAxis_of_shell_sub_horizontal_tendsto_zero`
   to supply the `hlimit` hypothesis of
   `lemma42_matrix_element_time_interchange`. The remaining live consumer
   work is then the separate `hH_imag_os` identification of
   `bvt_W_conjTensorProduct_timeShiftCanonicalExtension` on the positive
   imaginary axis with the OS holomorphic matrix element.
9. Optional downstream diagnostics involving raw `singleSplit` or
   `bvtSingleSplitXiShiftScalar` are not part of the live route. They may be
   revisited only after the main positivity path is closed or after a new
   valid tube representative is documented and checked.
10. Exact verification commands for the next Lean edits are:
    `lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean`
    after implementing `canonicalXiShift_mem_forwardTube` or any
    Positivity-side canonical residual theorem; and
    `lake env lean OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValueLimits.lean`
    if the shell/horizontal `Tflat` Fubini packages are placed in BVLimits.
    If a support theorem is promoted from private to public in an imported
    file, run that exact support-file check first, then the downstream
    Positivity check. Do not replace these with a broad build.

### 5.9.5. Detailed proof of the final public closure

The final theorem

`bvt_W_positive_of_transportImage_density`

is proved in four formal stages:

1. Transport-image core.
   Apply `bvt_wightmanInner_eq_transport_norm_sq_onImage` and
   Hilbert-space nonnegativity on the transported image.

2. Hilbert-space density.
   Use the fact that the relevant positive-time vectors are dense in
   `OSHilbertSpace OS` by construction of the completion. This is the density
   actually used in the OS I positivity mechanism.

3. VEV/transport identification.
   Show that `bvt_W` agrees with the corresponding vacuum expectation value on
   the transported positive-time core.

4. Continuity closure.
   Use continuity of `bvt_W` together with Hilbert-space closure to pass from
   the transported core to arbitrary public `BorchersSequence d`.

The only continuity allowed here is the bounded finite-support continuity
already documented in the repo. Rebuilding theorem 3 from a new global topology
on raw `BorchersSequence d` remains off-route.

Exact current implementation status:

1. the old raw same-input theorem slogan is withdrawn and must not be
   implemented literally;
2. the current local production branch already contains the Stage-3/4
   transformed-image carrier and the on-image Hilbert transport;
3. the live frontier is no longer a transport placeholder or a Schwartz-density
   theorem, but the transformed-image quadratic identity and final positivity
   closure;
4. the theorem-3 blueprint now endorses only the transformed-image /
   Hilbert-density reading of Section 4.3.

## 6. Exact relation to the current production consumers

The current legacy consumers can remain compiled, but they are not part of the
endorsed closure route.

Safe usage:

1. mine the current codebase only for reusable continuity / completion /
   positive-time Hilbert-space facts;
2. keep the deprecated `hschw` consumer chain compiled but untouched;
3. if a legacy theorem becomes useful later, re-justify it from the corrected
   transformed-image Package-I route rather than treating it as an input.

Unsafe usage:

1. introducing a new theorem whose primary conclusion is another `h*` consumer
   interface;
2. reentering the K2 common-kernel route;
3. implementing the old raw Package-I theorem surface on the same
   `BorchersSequence d` input without first fixing the transformed-image
   statement.

## 7. Minimal Lean pseudocode for the endorsed route

The later Lean implementation should use the following theorem-package names
unless an exact compile failure forces a local renaming. In that case the docs
must be updated at the same time; the names below are now part of the intended
implementation contract, not casual pseudocode.

```lean
/- Step A: one-variable identity theorem. -/
theorem identity_theorem_right_halfplane ... := by
  ...

/- Step B: compact positive-time single/split equality on {Re z > 0}. -/
theorem bvt_xiShift_eq_osInnerProduct_holomorphicValue_single ... := by
  apply identity_theorem_right_halfplane
  ...

/- Step C: withdrawn same-shell boundary pairing route (historical, false). -/
-- Do not implement `schwinger_timeShift_eq_bvt_W_conjTensorProduct_timeShift`.
-- The same-input shell identity is false and remains quarantined.

/- Step D: withdrawn raw positive-time sesquilinear route (historical, false). -/
-- Do not implement `bvt_wightmanInner_eq_osInner_of_positiveTime`.

/- Step E: withdrawn raw positive-time positivity route (historical, false). -/
-- Do not implement `bvt_positiveTime_self_nonneg_from_packageC`.

/- Step F: withdrawn raw density route (historical, do not implement). -/
theorem orderedPositiveTime_dense_schwartzNPoint ... := by
  ...

theorem exists_orderedPositiveTime_seq_tendsto ... := by
  ...

/- Step G: withdrawn approximation bundling route (historical, do not implement). -/
theorem exists_positiveTime_componentwise_approximation ... := by
  ...

/- Step H: withdrawn continuity-after-density route (historical, do not implement). -/
theorem WightmanInnerProduct_tendsto_of_componentwise_tendsto ... := by
  ...

theorem re_WightmanInnerProduct_tendsto_of_componentwise_tendsto ... := by
  ...

/- Step I: final theorem-3 closure via Section 4.3 transformed image. -/
def bvtTransportImage ... := by
  ...

def BvtTransportImageSequence ... := by
  ...

noncomputable def bvt_transport_to_osHilbert_onImage ... := by
  ...

theorem bvt_wightmanInner_eq_transport_norm_sq_onImage ... := by
  ...

theorem bvt_W_positive_of_transportImage_density ... := by
  ...
```

The current production file
`OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanPositivity.lean`
already uses the exact names
`identity_theorem_right_halfplane`,
`bvt_xiShift_eq_osInnerProduct_holomorphicValue_single`.
The transformed-image theorem names above should therefore be treated as the
fixed guidance for the corrected Section 4.3 closure package. The older raw
same-input names
`schwinger_timeShift_eq_bvt_W_conjTensorProduct_timeShift`,
`bvt_wightmanInner_eq_osInner_of_positiveTime`,
and `bvt_positiveTime_self_nonneg_from_packageC`
are withdrawn historical names and should not be reintroduced as theorem
targets.

## 8. Representation-gap note

The theorem-3 route above is the current-code realization of the OS proof.

The docs therefore record the following explicitly:

1. raw `BorchersSequence d` is a bounded finite-record representation;
2. this representation is enough for theorem 3 because
   `WightmanInnerProduct` is a finite sum;
3. therefore theorem 3 should be closed by the Section 4.3 transport-map
   realization, not by first imposing a `Submodule` / topology package on the
   raw type.

This is a local repo encoding fact, not a mathematical change to the OS route.

## 9. Support-work checklist

Before any later production proof resumes, the support work should verify:

1. no theorem-3 doc section still treats `hschw` as the target theorem shape;
2. no theorem-3 doc section still recommends `bvtInitialCore` on raw
   `BorchersSequence d`;
3. `mathlib_gap_analysis.md` classifies the raw `BorchersSequence` issue as a
   local representation gap, not an upstream gap;
4. any new test-file support work stays inside Package A through Package I
   above, and does not revive the withdrawn F/G/H density route as if it were
   endorsed.
5. the docs identify the exact current local frontier as the corrected
   transformed-image Package-I theorem surface, not as a generic
   “boundary-value limit”.
6. the docs explicitly record that Packages A-B are already implemented in
   `OSToWightmanPositivity.lean`;
7. no theorem-3 doc section still states the naive raw theorem
   `WightmanInnerProduct(bvt_W)(F,F).re = ‖u(F)‖^2` on the same raw public
   `BorchersSequence d` input as if it were already the correct Section 4.3
   theorem surface.

## 10. Bottom line

Theorem 3 is no longer a shell-comparison project.

Theorem 3 is now exactly this:

1. prove the positive-time semigroup bridge;
2. prove positivity on `PositiveTimeBorchersSequence d`;
3. define the Section 4.3 transformed Minkowski image and its OS Hilbert-space
   transport map;
4. identify the Wightman quadratic form with a Hilbert norm square on that
   transformed-image core;
5. extend positivity from the transformed-image core to arbitrary
   `BorchersSequence d` by density/continuity.

That is the only theorem-3 route this note now endorses.
