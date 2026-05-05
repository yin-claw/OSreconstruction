# W-to-integral bridge plan — discharge of `W_analytic_cluster_integral` via R4

Status as of 2026-05-04. Supersedes `docs/cluster_routeA_plan.md` as the
live target for closing `W_analytic_cluster_integral` (the integral-form
cluster theorem in `SchwingerAxioms.lean:3786`).

## Why this is the right target

The R→E direction (Wightman → OS axioms) requires verifying E4 on the
constructed Schwinger functions. In the project:

* `OsterwalderSchraderAxioms.S` = `constructSchwingerFunctions Wfn`
  = `fun n f => wickRotatedBoundaryPairing Wfn n f.1`
  (`Reconstruction/WickRotation/BHWTranslation.lean:1536`)
* E4 (`Reconstruction/SchwingerOS.lean:792`) is stated in integral form
  via the un-reflected tensor product `f.1 ⊗ g_a.1`.
* `W_analytic_cluster_integral` (`SchwingerAxioms.lean:3786`) matches E4
  exactly — same un-reflected form.

So `W_analytic_cluster_integral` IS the E4-verification lemma for the
constructed Schwinger functions. Modifying its signature would break
the OS-axiom verification.

## The proof strategy: route through `Wfn.cluster` (R4)

The cleanest path uses the R4 axiom field directly:

1. **R4** (`Wfn.cluster`, `Core.lean:787`) gives, for arbitrary Schwartz
   `f, g` and ε > 0, an R such that for spatial `a` with `|⃗a| > R`:
   ```
   ‖Wfn.W (n+m) (f.tensorProduct g_a) - Wfn.W n f * Wfn.W m g‖ < ε.
   ```

2. **W-to-integral bridge** (the new live target): for OPTR-supported f,
   ```
   wickRotatedBoundaryPairing Wfn n f = Wfn.W n f.
   ```

3. The cluster theorem follows by:
   * Specialize R4 to `f, g` from the OPTR hypothesis.
   * Apply the bridge to convert `Wfn.W n f` to `wickRotatedBoundaryPairing Wfn n f`,
     similarly for `g` and the joint `f.tensorProduct g_a`.
   * Conclude `‖integral - product of integrals‖ < ε`.

This avoids both the polynomial-growth obstruction (which lived in
the pointwise-BHW + dominated-convergence approach of route (i)) and
the OS-reflected/un-reflected mismatch (which made Route A off-path).

## The bridge: what it claims and why it's plausible

**Statement** (single-block):
```lean
theorem wickRotatedBoundaryPairing_eq_W
    (Wfn : WightmanFunctions d) (n : ℕ) (f : SchwartzNPoint d n)
    (hsupp_f : tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
  wickRotatedBoundaryPairing Wfn n f = Wfn.W n f
```

**Joint version** (needed for `W_analytic_cluster_integral`):
```lean
theorem wickRotatedBoundaryPairing_eq_W_joint
    (Wfn : WightmanFunctions d) (n m : ℕ)
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hsupp_f : tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hsupp_g : tsupport ((g : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
      OrderedPositiveTimeRegion d m)
    (a : SpacetimeDim d) (ha0 : a 0 = 0)
    (g_a : SchwartzNPoint d m)
    (hga : ∀ x, g_a x = g (fun i => x i - a)) :
  wickRotatedBoundaryPairing Wfn (n+m) (f.tensorProduct g_a) =
    Wfn.W (n+m) (f.tensorProduct g_a)
```

**Why this is plausible**:
* The `spectrum_condition` field gives a holomorphic
  `W_analytic : ForwardTube d n → ℂ` whose distributional boundary
  values recover `Wfn.W n`.
* `wickRotatedBoundaryPairing` is `∫ F_ext(wick x) f(x) dx`. For
  OPTR-supported `f`, the Wick-rotated config `wick(x)` lies in
  `ForwardTube` (positive ordered times → strictly increasing forward-cone
  imaginary parts under (τ,x⃗) ↦ (iτ,x⃗)).
* On `ForwardTube`, `F_ext_on_translatedPET_total` agrees with
  `W_analytic` (proved `F_ext_on_translatedPET_total_eq_on_PET`,
  `BHWTranslation.lean:1315`).
* The integral at imaginary times equals the boundary-value `Wfn.W n f`
  by analyticity + a Cauchy-like deformation argument.

## Existing infrastructure we'll use

* `bhw_distributional_boundary_values` (`BHWTranslation.lean:1477`,
  proved): `Tendsto (∫ W_analytic(x + iεη) f(x) dx) (ε→0+) (nhds (Wfn.W n f))`
  for η in the forward cone.
* `F_ext_on_translatedPET_total_eq_on_PET` (`BHWTranslation.lean:1315`):
  on PET, `F_ext_on_translatedPET_total = W_analytic`.
* `F_ext_on_translatedPET_total_translation_invariant`
  (`BHWTranslation.lean:1327`): translation-invariance.
* `F_ext_on_translatedPET_total_perm_invariant`
  (`BHWTranslation.lean:1339`): permutation-invariance.
* `wick_rotated_kernel_mul_zeroDiagonal_integrable` (referenced in
  `SchwingerAxioms.lean:3827`): integrability of `F_ext * test` on
  zero-diagonal Schwartz tests.
* `wickRotatedBoundaryPairing_reality` (`SchwingerAxioms.lean:3436`,
  proved): `(starRingEnd ℂ) (∫ F_ext f) = ∫ F_ext f.osConj`.
* `Wfn.spectrum_condition.choose_spec.2.2` (the boundary-value
  recovery axiom inside R1).

## Proof sketch (single-block)

The single-block bridge is the heart. Strategy:

1. **Wick-rotated config in ForwardTube**: for OPTR-supported `f`,
   `wick(x) ∈ ForwardTube d n` for `x` in the support. Because:
   * OPTR support: `0 < x_1^0 < x_2^0 < ... < x_n^0`.
   * `wick(x_k)^0 = i x_k^0` has imaginary part `x_k^0 > 0`.
   * Successive differences `wick(x_{k+1}) - wick(x_k)` have time
     imaginary part `x_{k+1}^0 - x_k^0 > 0`, in V_+.
   * (May need explicit lemma `OPTR_wick_in_ForwardTube` if not present.)

2. **Replace F_ext with W_analytic on the support**:
   `wickRotatedBoundaryPairing Wfn n f = ∫ F_ext(wick x) f(x) dx`.
   On the OPTR support, `F_ext(wick x) = W_analytic(wick x)` by
   `F_ext_on_translatedPET_total_eq_on_PET`.

3. **Holomorphic deformation**: the integral
   `g(s) := ∫ W_analytic(x + i s · η(x)) f(x) dx`
   where `η(x) = (x^0, 0⃗)` (the Wick rotation imaginary direction)
   is constant in `s ∈ (0, 1]`, by a Cauchy-style argument: the
   integrand is holomorphic in s for `s` near 1, and the boundary
   contributions vanish by Schwartz decay of `f`.

   Mathematically: differentiating under the integral and using
   holomorphicity gives `g'(s) = 0` away from boundary. So
   `g(1) = lim_{s→0+} g(s)`.

4. **Boundary value**: `lim_{s→0+} g(s) = Wfn.W n f` by
   `bhw_distributional_boundary_values`. (This requires η = (x^0, 0⃗)
   to be in the forward cone for all x in the OPTR support, which
   holds because x^0 > 0 there.)

5. Combine: `g(1) = ∫ W_analytic(wick x) f(x) dx = wickRotatedBoundaryPairing Wfn n f`,
   and `g(1) = Wfn.W n f`. QED.

The technical heart is step 3 — the holomorphic deformation. This is
a Cauchy / Stokes-type argument on the integral with a one-parameter
family of imaginary shifts.

**Potential subtlety**: the boundary-value lemma uses a CONSTANT η
(independent of x), while we want η depending on x as `η(x) = (x^0, 0⃗)`.
Either:
* Apply the constant-η lemma fiberwise (η(x) only depends on x^0),
  using a slicing decomposition; or
* Establish a generalized boundary-value lemma for x-dependent η in
  the forward cone (more general but more work).

## Proof sketch (joint case)

The joint case `wickRotatedBoundaryPairing Wfn (n+m) (f.tensorProduct g_a) = Wfn.W (n+m) (f.tensorProduct g_a)`
is the same argument applied to the joint config.

**Subtlety**: for OPTR-supported `f, g` separately, the joint
Wick-rotated config `wick(f-block, g_a-block)` lies in PET (Permuted
Extended Tube), not necessarily in `ForwardTube` (because inter-block
time ordering between f and g_a is not guaranteed by separate OPTR).

* On PET, F_ext = appropriate-permutation of W_analytic, by
  `F_ext_on_translatedPET_total_perm_invariant`.
* The boundary-value relation on the permuted forward tube gives the
  permuted W_n value, which by Wightman symmetry (R0 / `Wfn.linear` +
  `Wfn.symmetric` if it's a field) equals the original W_n value.
* Integration over the joint domain decomposes into pieces by the
  permutation that puts each (x_n, x_m+a) into ForwardTube. Each
  piece equals the corresponding W evaluation.
* Sum over permutations + Wightman symmetry collapses back to the
  single value `Wfn.W (n+m) (f.tensorProduct g_a)`.

**Estimated complexity**: nontrivial. The single-block case is ~200
Lean lines of holomorphic-deformation argument. The joint case
adds permutation-decomposition logic — perhaps ~100 more lines.

## Discharge plan, step by step

1. **Lemma: OPTR config Wick-rotates into ForwardTube**.
   ~20 lines. Should be a direct consequence of OPTR's positive-ordered
   times. Search the project for an existing lemma first.

2. **Single-block bridge (Step 1 above)**: prove via holomorphic
   deformation. Needs:
   * Cauchy-deformation lemma for integrals along a vertical strip
     in the time component.
   * Or generalized boundary-value lemma with x-dependent η.
   ~150–300 Lean lines depending on path.

3. **Joint bridge (Step 2 above)**: extend to permuted-tube case.
   ~100 Lean lines.

4. **Compose**: `W_analytic_cluster_integral` falls out from
   `Wfn.cluster` + bridge in ~20 Lean lines.

5. **Optional cleanup**: retire the legacy Route-B sorrys in
   `ClusterFromKL.lean`, retire `cluster_npoint_OS_form_inner_limit`
   if Route A is no longer on the cluster critical path. Or keep
   them as parallel infrastructure (Route A is still useful for
   GNS-side theorems unrelated to E4).

## What this means for Route A

Route A (`cluster_inner_product_from_GNS`,
`cluster_npoint_OS_form_inner_limit`) is **off the E4 critical path**.
But it's NOT wasted:
* It's a complete, sorry-free derivation of the GNS-Hilbert-space
  cluster, conditional on a `WightmanReconstruction` instance.
* It provides infrastructure for future GNS-side theorems (mass gap,
  asymptotic completeness, particle interpretation).
* The `WightmanReconstruction` class is a vetted, reusable interface
  for the OS-quantization output.

We keep it; we just stop pretending it discharges E4 directly.

## Open design questions for the user

1. **Constant vs x-dependent η in the boundary-value lemma**.
   * (a) Apply constant-η fiberwise via slicing: simpler but adds
     measure-theory bookkeeping.
   * (b) Generalize the boundary-value relation to x-dependent η:
     more direct but new infrastructure.

2. **How to prove the joint case**.
   * (a) Decompose by permutation, applying single-block bridge per
     permutation.
   * (b) Joint deformation argument directly (more uniform but more
     complex).

3. **Where to file the bridge lemma**. Options:
   * `BHWTranslation.lean` (next to existing F_ext infrastructure).
   * New file `Reconstruction/WickRotation/WickRotatedPairingEqW.lean`.
   * Bottom of `SchwingerAxioms.lean`.

## References

* OS 1973 §2 (definitions of Schwinger families on `𝒮_<`)
* OS 1973 §4 (E4 statement)
* Glimm-Jaffe Chapter 19 (OS reconstruction; cluster theorem 19.4.1)
* Streater-Wightman Chapter 3 (Wightman → Schwinger via BHW)
* Bargmann-Hall-Wightman 1957 (original analytic continuation theorem)
