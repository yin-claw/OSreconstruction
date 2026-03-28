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

---

## Summary

| ID | Name | Kind | File | On critical path? |
|----|------|------|------|-------------------|
| A1 | `schwartz_nuclear_extension` | axiom | WightmanAxioms.lean:297 | Yes (transitive) |
| A2 | `exists_continuousMultilinear_ofSeparatelyContinuous` | axiom | WightmanAxioms.lean:459 | Yes (transitive) |
| S1 | `gnsQFT.spectrum_condition` | sorry | GNSHilbertSpace.lean:834 | Yes |
| S2 | `gnsQFT.cyclicity` | sorry | GNSHilbertSpace.lean:871 | Yes |
| S3 | `gnsQFT.vacuum_unique` (part 2) | sorry | GNSHilbertSpace.lean:919 | Yes |
| S4 | `wightman_uniqueness` | sorry | Main.lean:82 | No (standalone) |

**Core.lean, PoincareAction.lean, PoincareRep.lean, GNSConstruction.lean**: all clean (no sorries or axioms).

---

## Axioms (declared with `axiom`, no proof)

### A1. `schwartz_nuclear_extension`

**File:** `WightmanAxioms.lean:297`

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
`wightmanFunction_linear` (WightmanAxioms.lean:550), which shows that the
Wightman n-point function `qft.wightmanFunction n` is a continuous linear
functional on S(R^{nd}). This is needed to state `wightman_reconstruction`
properly: the theorem says `qft.wightmanFunction n fs = W_n(productTensor fs)`,
and `wightmanFunction` is defined using this axiom.

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

**File:** `WightmanAxioms.lean:459`

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

**How it enters the GNS pipeline:** Used in `wightmanFunction_linear`
(WightmanAxioms.lean:530) to upgrade the separately continuous n-point function
to a jointly continuous one, so that A1 can be applied.

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

## Sorries in `gnsQFT` (all on the critical path for `wightman_reconstruction`)

These three sorries are fields of `gnsQFT : WightmanQFT d`
(GNSHilbertSpace.lean:826), which is used by `wightman_reconstruction'`
(line 955), which is the proof of the main theorem.

### S1. `spectrum_condition`

**File:** `GNSHilbertSpace.lean:834`

```lean
spectrum_condition := sorry
-- Requires Stone's theorem and spectral theory for unbounded operators
```

**What it needs:** The energy-momentum spectrum of the reconstructed QFT lies in
the closed forward light cone. Concretely, the `SpectralCondition` structure
requires `energy_nonneg` (non-negative Hamiltonian expectation values) and
`mass_shell` (momentum spectral measure supported in the forward cone).

**Proof strategy (from comments):**
1. The Poincare representation `U(a) = exp(iP_mu a^mu)` gives self-adjoint
   generators P_mu via Stone's theorem.
2. The forward tube analyticity of the Wightman functions implies that the
   Fourier transform of W_n is supported in the forward cone.
3. This translates to sigma(P) subset V_+.

**Importance: High.**
Without the spectrum condition, the reconstructed `WightmanQFT` is incomplete --
it satisfies field axioms, locality, covariance, but lacks the fundamental
energy positivity that distinguishes physical QFTs. The spectrum condition is
one of the Wightman axioms (W1).

However, it does not affect the *reproducing property*
`gns_reproduces_wightman`: the inner product identity
`<Omega, phi(f1)...phi(fn)Omega> = W_n(f1 x ... x fn)` is fully proved
regardless.

**Difficulty to prove: Very Hard.**
This is blocked by two major missing pieces in Mathlib:
- **Stone's theorem** (one-parameter unitary groups <-> self-adjoint generators).
  This is a fundamental result in functional analysis that Mathlib does not yet
  have. Formalizing it requires the spectral theorem for unbounded self-adjoint
  operators.
- **Spectral theory for unbounded operators.** Mathlib has spectral theory for
  bounded operators on Banach spaces but not for unbounded self-adjoint
  operators on Hilbert spaces.

These are major Mathlib infrastructure projects, each likely requiring months of
work. This sorry is the hardest to discharge in the entire GNS pipeline.

---

### S2. `cyclicity`

**File:** `GNSHilbertSpace.lean:871`

```lean
cyclicity := sorry
-- Requires the Schwartz nuclear theorem: product test functions are dense
-- in the n-point Schwartz space
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

**Importance: High.**
Cyclicity is a Wightman axiom (implicit in W2) and is essential for the
uniqueness theorem. Without it, the Hilbert space might be "too big" -- it could
contain sectors invisible to the field operators.

In practice, cyclicity is almost tautological for the GNS construction (the
pre-Hilbert space is *defined* as the span of Borchers sequences, and every
Borchers sequence is a finite sum of terms that can be approximated by iterated
field actions). The gap is purely about the approximation of general Schwartz
functions by product tensors, which is the nuclear theorem.

**Difficulty to prove: Hard.**
Directly blocked by A1 (Schwartz nuclear theorem). Once A1 is available, the
cyclicity proof should be relatively short -- the density of product tensors in
the Wightman-norm topology follows from the density of product tensors in the
Schwartz topology (which is what the nuclear theorem gives) plus continuity of
the Wightman inner product (which is `Wfn.tempered`).

Estimated additional work beyond A1: 1-2 weeks.

---

### S3. `vacuum_unique` (part 2 only)

**File:** `GNSHilbertSpace.lean:919`

```lean
vacuum_unique :=
    -- Part 1 (proved): Omega is time-translation invariant
    ⟨fun t => gnsVacuum_poincare_invariant Wfn _,
    -- Part 2 (sorry): any time-translation-invariant vector is proportional to Omega
    sorry⟩
```

**What it needs:** If `U(t,0)psi = psi` for all time translations t, then
`psi = c * Omega` for some c in C.

**Proof strategy (from comments):**
1. Stone's theorem: time translation `U(t) = exp(iHt)` for self-adjoint H.
2. Spectrum condition: sigma(H) subset [0, infinity).
3. Time-translation invariance: `U(t)psi = psi` for all t => `Hpsi = 0`.
4. `ker(H) = C * Omega` by the cluster decomposition / ergodicity argument.

Part 1 (Omega is invariant) is proved. Part 2 (uniqueness) is sorry.

**Importance: Medium.**
Vacuum uniqueness (W4) is the weakest of the Wightman axioms in terms of its
impact on the rest of the theory. It is not needed for:
- The reproducing property (gns_reproduces_wightman)
- Locality, covariance, or field operator properties
- The wightman_reconstruction statement

It *is* needed for the full logical package of `WightmanQFT`, and it is
physically important (it says there's a unique vacuum state / no
spontaneous symmetry breaking of translations).

**Difficulty to prove: Very Hard.**
Blocked by the same Stone's theorem / spectral theory infrastructure as S1,
plus the additional ergodicity argument (cluster decomposition implies
uniqueness of the ground state). Even with Stone's theorem available, step 4
requires a nontrivial argument connecting the cluster property of the
Wightman functions to the spectral gap of H.

---

## Standalone Sorry (not on the reconstruction critical path)

### S4. `wightman_uniqueness`

**File:** `Main.lean:82`

```lean
theorem wightman_uniqueness (qft1 qft2 : WightmanQFT d)
    (h : forall n fs, qft1.wightmanFunction n fs = qft2.wightmanFunction n fs) :
    exists U : qft1.HilbertSpace →ₗᵢ[ℂ] qft2.HilbertSpace,
      U qft1.vacuum = qft2.vacuum ∧
      (forall f psi, psi in qft1.field.domain ->
        U (qft1.field.operator f psi) = qft2.field.operator f (U psi)) := by
  sorry
```

**What it says:** Two Wightman QFTs with identical n-point functions are
unitarily equivalent (there exists a linear isometry intertwining vacua and
field operators).

**Importance: Low-Medium for the reconstruction theorem.**
This theorem is not used by any other proof in the codebase. It is a
standalone companion to `wightman_reconstruction`. Together they say: the
Wightman functions *determine* the QFT up to unitary equivalence. But
`wightman_reconstruction` (existence) is fully proved without it.

**Difficulty to prove: Moderate.**
This is the uniqueness half of the GNS theorem. The standard proof:
1. Define U on the dense span by `U(phi1(f1)...phi_n(fn)Omega_1) = phi2(f1)...phi2(fn)Omega_2`.
2. Well-definedness: if two expressions give the same vector in H1, they give
   the same vector in H2, because the inner products (= Wightman functions) match.
3. Isometry: `||U(v)||^2 = <v,v>` because both are expressed via Wightman functions.
4. Extend by continuity to all of H1.

The hard part is step 1 (well-definedness on the algebraic span as a quotient),
which requires careful bookkeeping with Mathlib's completion API. The
mathematical content is straightforward. Estimated effort: 2-4 weeks.

Note: this proof implicitly requires cyclicity (S2) of both QFTs, since it
constructs U on the algebraic span of field operators applied to the vacuum.

---

## Dependency and Criticality Summary

```
wightman_reconstruction  (PROVED, modulo sorries in gnsQFT)
  └── wightman_reconstruction'  (PROVED)
       └── gnsQFT : WightmanQFT d
            ├── spectrum_condition  = sorry  [S1]  ← Stone + spectral theory
            ├── cyclicity           = sorry  [S2]  ← nuclear theorem (A1)
            ├── vacuum_unique.2     = sorry  [S3]  ← Stone + spectral theory + cluster
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
- **`translation_preserves_inner`**: inner product is translation-invariant -- fully proved
- **Poincare representation**: unitary, group law, vacuum invariance -- fully proved
- **Locality**: field operators commute at spacelike separation -- fully proved
- **Covariance**: `phi(f)(U(g)psi) = U(g)(phi(g^{-1}f)psi)` -- fully proved
- **Field hermiticity**: `<phi(f)x, y> = <x, phi(f*)y>` -- fully proved
- **All algebraic instances** (AddCommGroup, Module, InnerProductSpace.Core, completion) -- fully proved

### What remains

| Blocker | Sorries it blocks | Mathematical area |
|---------|-------------------|-------------------|
| Stone's theorem + spectral theory (unbounded) | S1, S3 | Functional analysis |
| Schwartz nuclear theorem | S2 (and transitively A1, A2) | Functional analysis / nuclear spaces |
| Cluster -> vacuum uniqueness | S3 | Ergodic theory / QFT |
| GNS uniqueness argument | S4 | Operator algebras |

### Difficulty ranking (hardest first)

1. **S1 (spectrum condition)** -- Very Hard. Blocked by major missing Mathlib infrastructure (Stone's theorem, spectral theory for unbounded operators). This is a multi-month project.

2. **S3 (vacuum uniqueness, part 2)** -- Very Hard. Same blockers as S1, plus the ergodicity/cluster argument. Strictly harder than S1.

3. **S2 (cyclicity)** -- Hard. Blocked by the nuclear theorem (A1). Once A1 is available, the proof is relatively straightforward. The nuclear theorem itself is hard but has partial formal infrastructure already.

4. **A1 (Schwartz nuclear extension)** -- Hard. The nuclearity of Schwartz space exists in Lean 4 (`gaussian-field` library). Bridging to the kernel theorem is the remaining work.

5. **A2 (separately continuous -> jointly continuous)** -- Moderate. Standard Frechet space result, but Mathlib's Frechet space coverage is limited.

6. **S4 (wightman_uniqueness)** -- Moderate. Standard GNS uniqueness argument. Mathematically straightforward, main challenge is Lean/Mathlib bookkeeping. Not on the critical path.

### Bottom line

The GNS pipeline is in strong shape. The core mathematical content -- the
reproducing identity, the inner product space construction, Poincare covariance,
locality, and field hermiticity -- is **fully proved**. The three remaining
sorries (S1-S3) in the reconstructed `WightmanQFT` are all blocked by
**missing Mathlib infrastructure** (Stone's theorem, spectral theory, nuclear
theorem), not by gaps in the QFT formalization itself. These are well-understood
theorems from functional analysis that simply haven't been formalized in Lean yet.

---

## Proof Trace: `wightman_reconstruction`

This section traces every key theorem in the proof of `wightman_reconstruction`,
organized by the file that proves it. Line numbers refer to the files under
`OSReconstruction/Wightman/`.

### Entry point

**`wightman_reconstruction`** (`Reconstruction/Main.lean:60`)
```
:= wightman_reconstruction' Wfn
```
A one-line delegation.

**`wightman_reconstruction'`** (`Reconstruction/GNSHilbertSpace.lean:951`)
```
refine ⟨gnsQFT Wfn, fun n fs => ?_⟩
```
Constructs `gnsQFT Wfn : WightmanQFT d`, then proves the reproducing identity
in three steps:

| Step | What it does | Key theorem used |
|------|-------------|-----------------|
| 1 | `operatorPow` on the vacuum = iterated `fieldOperator` embedded in completion | `operatorPow_gnsQFT_eq` (line 924) |
| 2 | Inner product on completion = inner product on pre-Hilbert space | `UniformSpace.Completion.inner_coe` (Mathlib) |
| 3 | Pre-Hilbert inner product = Wightman function | `gns_reproduces_wightman` (GNSConstruction.lean:220) |

---

### Layer 1: Borchers algebra and inner product (`Reconstruction/Core.lean`)

This file builds the algebraic foundation. Everything here is sorry-free.

#### Structures

| Line | Definition | Role |
|------|-----------|------|
| 156 | `BorchersSequence d` | Finitely-supported sequence `funcs : (n : ℕ) -> SchwartzNPoint d n` with a `bound`; elements of the Borchers *-algebra |
| 279 | `WightmanInnerProduct d W F G` | `Sum_{n <= F.bound} Sum_{m <= G.bound} W(n+m)(f*_n ⊗ g_m)`; the GNS pre-inner product |
| 293 | `WightmanInnerProductN d W F G N1 N2` | Same sum with explicit bounds (used for extending to common bounds) |
| 548 | `WightmanFunctions d` | Input axiom bundle: `W`, `linear`, `tempered`, `normalized`, `translation_invariant`, `lorentz_covariant`, `spectrum_condition`, `locally_commutative`, `positive_definite`, `hermitian`, `cluster` |
| 822 | `borchersSetoid Wfn` | `F ~ G` iff `Re(⟨F,F⟩ + ⟨G,G⟩ - ⟨F,G⟩ - ⟨G,F⟩) = 0`; identifies null-difference vectors |
| 883 | `PreHilbertSpace Wfn` | `Quotient (borchersSetoid Wfn)`; the GNS quotient space |
| 887 | `PreHilbertSpace.innerProduct` | Inner product on the quotient, lifted via `Quotient.lift₂` |
| 937 | `vacuumSequence` | `funcs 0 = 1` (constant), `funcs (n+1) = 0`; the algebraic vacuum |
| 988 | `fieldOperatorAction f F` | `(phi(f)F)_0 = 0`, `(phi(f)F)_{k+1} = prependField f (F.funcs k)`; field operator on Borchers sequences |
| 1158 | `fieldOperator Wfn f` | Field operator on `PreHilbertSpace Wfn`, defined via `Quotient.lift` |

#### Inner product: sesquilinearity and compatibility lemmas

These are the workhorses used throughout the pipeline to manipulate `WightmanInnerProduct`.

| Line | Lemma | Statement |
|------|-------|-----------|
| 343 | `WightmanInnerProduct_eq_extended` | Can compute at any common bounds >= the actual bounds |
| 355 | `WightmanInnerProduct_add_right` | `⟨F, G+H⟩ = ⟨F,G⟩ + ⟨F,H⟩` |
| 381 | `WightmanInnerProduct_add_left` | `⟨F+G, H⟩ = ⟨F,H⟩ + ⟨G,H⟩` |
| 405 | `WightmanInnerProduct_smul_right` | `⟨F, c*G⟩ = c * ⟨F,G⟩` |
| 415 | `WightmanInnerProduct_zero_left` | `⟨0, G⟩ = 0` |
| 425 | `WightmanInnerProduct_zero_right` | `⟨F, 0⟩ = 0` |
| 435 | `WightmanInnerProduct_congr_right` | Same `funcs` => same inner product (right) |
| 450 | `WightmanInnerProduct_congr_left` | Same `funcs` => same inner product (left) |
| 465 | `WightmanInnerProduct_neg_left` | `⟨-F, G⟩ = -⟨F,G⟩` |
| 476 | `WightmanInnerProduct_neg_right` | `⟨F, -G⟩ = -⟨F,G⟩` |
| 487 | `WightmanInnerProduct_sub_right` | `⟨F, G-H⟩ = ⟨F,G⟩ - ⟨F,H⟩` |
| 513 | `WightmanInnerProduct_smul_left` | `⟨c*F, G⟩ = conj(c) * ⟨F,G⟩` |
| 525 | `WightmanInnerProduct_expand_diff` | `Re⟨F-G, F-G⟩ = Re(⟨F,F⟩ + ⟨G,G⟩ - ⟨F,G⟩ - ⟨G,F⟩)` |

#### Critical structural lemmas

| Line | Lemma | Role in pipeline |
|------|-------|-----------------|
| 700 | `WightmanInnerProduct_hermitian` | `⟨F,G⟩ = conj(⟨G,F⟩)`. Used by `inner_conj_symm` (GNSHilbertSpace) and `preHilbert_inner_real` (GNSConstruction) |
| 764 | `null_inner_product_zero` | `Re⟨X,X⟩ = 0 => ⟨X,Y⟩ = 0` for all `Y`. The Cauchy-Schwarz consequence that makes the null space a left ideal. Used by `fieldOperator_preserves_null`, `add_respects_equiv`, `locality_setoid` |
| 1102 | `field_adjoint` | `⟨phi(f)F, G⟩ = ⟨F, phi(conj f)G⟩`. Used by `field_hermitian` in `gnsQFT` and by `fieldOperator_preserves_null` |
| 1126 | `fieldOperator_preserves_null` | `Re⟨F,F⟩ = 0 => Re⟨phi(f)F, phi(f)F⟩ = 0`. Proved via `field_adjoint` + `null_inner_product_zero` |
| 1136 | `fieldOperator_well_defined` | `F ~ G => phi(f)F ~ phi(f)G`. Justifies `Quotient.lift` in the definition of `fieldOperator` |

---

### Layer 2: Poincare action (`Reconstruction/PoincareAction.lean`, `Reconstruction/PoincareRep.lean`)

Sorry-free. Builds the Poincare group action from single-particle level up to the pre-Hilbert space.

#### PoincareAction.lean (single-particle level)

| Line | Definition/Lemma | Description |
|------|-----------------|-------------|
| 92 | `poincareActSchwartz g f` | `(g*f)(x) = f(g^{-1}*x)` on `SchwartzSpacetime d` |
| 113 | `poincareActSchwartz_one` | `1 * f = f` |
| 119 | `poincareActSchwartz_mul` | `(g1*g2) * f = g1 * (g2 * f)` |

#### PoincareRep.lean (n-point, Borchers, and pre-Hilbert levels)

| Line | Definition/Lemma | Description |
|------|-----------------|-------------|
| 141 | `poincareActNPoint g f` | Action on `SchwartzNPoint d n`: apply `g^{-1}` to each coordinate |
| 166 | `poincareActNPoint_conjTensorProduct` | Poincare action commutes with `conjTensorProduct` |
| 177 | `poincareActBorchers g F` | Componentwise `poincareActNPoint` on `BorchersSequence` |
| 198 | `WightmanInnerProduct_poincare_invariant` | **Key**: `⟨g*F, g*G⟩ = ⟨F,G⟩`. Uses `Wfn.translation_invariant` and `Wfn.lorentz_covariant` |
| 236 | `poincareActBorchers_setoid` | Action preserves `borchersSetoid` (via inner product invariance) |
| 248 | `poincareActPreHilbert Wfn g` | Action on `PreHilbertSpace Wfn` via `Quotient.lift` |
| 255 | `poincareActPreHilbert_inner` | `⟨g*x, g*y⟩ = ⟨x,y⟩` on `PreHilbertSpace`. Reduces to `WightmanInnerProduct_poincare_invariant` |

---

### Layer 3: Reproducing identity (`Reconstruction/GNSConstruction.lean`)

Sorry-free. Proves the mathematical heart of the GNS construction.

| Line | Theorem | Role |
|------|---------|------|
| 85 | `preHilbert_inner_pos` | `Re⟨[F],[F]⟩ >= 0` on the quotient |
| 93 | `preHilbert_inner_real` | `Im⟨[F],[F]⟩ = 0` (diagonal is real) |
| 110 | `vacuumState Wfn` | Vacuum in pre-Hilbert space: `⟦vacuumSequence⟧` |
| 114 | `vacuum_normalized` | `⟨Omega, Omega⟩ = 1`. Expands the double sum, uses `Wfn.normalized` |

The reproducing identity `gns_reproduces_wightman` (line 220) is proved via
four private helpers:

| Line | Helper | What it shows |
|------|--------|--------------|
| 153 | `foldr_fieldOperator_eq_mk` | Iterated `fieldOperator` on quotient = quotient of iterated `fieldOperatorAction` |
| 164 | `iteratedAction_funcs_n` | The n-th component of `phi(f1)...phi(fn) * vacuum` is `productTensor fs` |
| 174 | `iteratedAction_funcs_ne` | All other components are zero |
| 192 | `iteratedAction_bound` | The bound is `n+1` |
| 201 | `W_conjTP_vacuum_zero` | `W(0+m)(vac_0.conjTP h) = W(m)(h)` (vacuum eliminates the 0-slot) |

The proof of `gns_reproduces_wightman` then:
1. Lifts to Borchers sequence level (`foldr_fieldOperator_eq_mk`)
2. Expands the `WightmanInnerProduct` sum (vacuumSequence has bound 1, so only k in {0,1})
3. Kills the k=1 term (vacuumSequence.funcs 1 = 0)
4. In the inner sum, extracts the single nonzero term at m=n (`iteratedAction_funcs_n`, `iteratedAction_funcs_ne`)
5. Applies `W_conjTP_vacuum_zero` to eliminate the vacuum slot

---

### Layer 4: Algebraic instances and Hilbert space (`Reconstruction/GNSHilbertSpace.lean`)

This is the longest file. It builds Mathlib-compatible typeclass instances,
completes to a Hilbert space, extends the Poincare action and field operators,
proves locality and covariance, and assembles the final `WightmanQFT`.

#### Phase 1: Algebraic structure on `PreHilbertSpace` (lines 50-217)

All algebraic laws are proved by the same strategy: lift to Borchers
representatives via `Quotient.inductionOn`, then show the two sides have
equal `funcs` via `mk_eq_of_funcs_eq`.

| Line | Instance | Depends on |
|------|----------|-----------|
| 70 | `add_respects_equiv` | `null_inner_product_zero`, sesquilinearity lemmas |
| 111 | `neg_respects_equiv` | `WightmanInnerProduct_neg_*` |
| 124 | `smul_respects_equiv` | `WightmanInnerProduct_smul_*` |
| 176 | **`instAddCommGroup`** | `add_respects_equiv`, `neg_respects_equiv`, `mk_eq_of_funcs_eq` |
| 198 | **`instModule`** | `smul_respects_equiv`, `mk_eq_of_funcs_eq` |

#### Phase 2: Inner product space core (lines 218-307)

| Line | Theorem/Instance | Proves |
|------|-----------------|--------|
| 229 | `inner_conj_symm` | `conj⟨y,x⟩ = ⟨x,y⟩` (from `WightmanInnerProduct_hermitian`) |
| 237 | `inner_re_nonneg` | `0 <= Re⟨x,x⟩` (from `preHilbert_inner_pos`) |
| 243 | `inner_add_left` | `⟨x+y,z⟩ = ⟨x,z⟩ + ⟨y,z⟩` (from `WightmanInnerProduct_add_left`) |
| 252 | `inner_smul_left` | `⟨r*x,y⟩ = conj(r)*⟨x,y⟩` (from `WightmanInnerProduct_smul_left`) |
| 261 | `inner_definite` | `⟨x,x⟩ = 0 => x = 0` (from the quotient: `⟨F,F⟩ = 0` means `F ~ 0`) |
| 277 | **`instCore`** | `InnerProductSpace.Core C (PreHilbertSpace Wfn)` packaging the above |
| 299 | **`instNormedAddCommGroup`** | `NormedAddCommGroup` via `Core.toNormedAddCommGroup`; norm = sqrt(Re⟨x,x⟩) |
| 304 | **`instInnerProductSpace`** | `InnerProductSpace C` via `InnerProductSpace.ofCore` |

#### Phase 3: Completion (lines 309-331)

| Line | Definition/Theorem | Description |
|------|-------------------|-------------|
| 313 | **`GNSHilbertSpace Wfn`** | `UniformSpace.Completion (PreHilbertSpace Wfn)` -- the physical Hilbert space |
| 316 | `gnsVacuum Wfn` | Vacuum in the completion (image of `vacuumState` under embedding) |
| 321 | `vacuumState_norm` | `‖Omega‖ = 1` (from `vacuum_normalized` + `Core.normSq`) |

#### Phase 4: Poincare representation on the completion (lines 335-527)

Extends the pre-Hilbert Poincare action to the completion via Mathlib's
`ContinuousLinearMap.extend`.

| Line | Theorem | What it proves |
|------|---------|---------------|
| 389 | `poincareActPreHilbert_norm` | `‖g*x‖ = ‖x‖` (from `poincareActPreHilbert_inner`) |
| 401 | `poincareActPreHilbert_CLM` | Packages the action as a `ContinuousLinearMap` with norm bound 1 |
| 415 | `poincareActGNS g` | Extension to `GNSHilbertSpace ->L[C] GNSHilbertSpace` |
| 421 | `poincareActGNS_coe` | On embedded vectors: agrees with pre-Hilbert action |
| 441 | `poincareActGNS_one` | `U(1) = id` (via `ContinuousLinearMap.extend_unique`) |
| 451 | `poincareActGNS_mul` | `U(g1*g2) = U(g1) . U(g2)` |
| 469 | `poincareActGNS_inner` | `⟨U(g)x, U(g)y⟩ = ⟨x,y⟩` (density argument + `poincareActPreHilbert_inner`) |
| 490 | `poincareActGNS_adjoint_comp` | `U(g)* . U(g) = id` (unitarity) |
| 501 | **`gnsPoincareRep`** | `PoincareRepresentation d (GNSHilbertSpace Wfn)` -- the full unitary representation |
| 511 | `gnsVacuum_poincare_invariant` | `U(g)Omega = Omega` (vacuum has no spacetime args to transform) |

#### Phase 5: Field operators on the completion (lines 529-656)

| Line | Definition/Theorem | Description |
|------|-------------------|-------------|
| 539 | `fieldOperator_add_test` | `phi(f+g)x = phi(f)x + phi(g)x` |
| 545 | `fieldOperator_smul_test` | `phi(c*f)x = c*phi(f)x` |
| 551 | `fieldOperator_vector_add` | `phi(f)(x+y) = phi(f)x + phi(f)y` |
| 558 | `fieldOperator_vector_smul` | `phi(f)(c*x) = c*phi(f)x` |
| 568 | **`gnsFieldOp f`** | Field operator on `GNSHilbertSpace` via `Function.extend` along the completion embedding |
| 577 | `gnsFieldOp_coe` | On embedded vectors: `gnsFieldOp f (embed y) = embed(fieldOperator f y)` |
| 592 | `gnsDomainSubmodule` | Image of `PreHilbertSpace` in the completion, as a `Submodule` |
| 604 | `gnsDomain_dense` | The domain is dense (from `Completion.denseRange_coe`) |
| 612 | **`gnsDomain`** | The domain as a `DenseSubspace` |
| 621 | `gnsFieldOp_domain` | Field operators preserve the domain |
| 629 | `matrix_element_continuous_aux` | `f |-> ⟨x, phi(f)y⟩` is continuous (from `Wfn.tempered` + `prependField_continuous_left`) |

#### Locality proof chain (lines 657-780)

Proves that spacelike-separated field operators commute. The proof descends
from the `locally_commutative` axiom of `WightmanFunctions` through four
layers:

```
Wfn.locally_commutative  (axiom: W_n with permuted spacelike args are equal)
  -> locality_term_eq      (line 705: per-summand equality of W applied to conjTP)
     -> locality_inner_eq   (line 739: WightmanInnerProduct equality for phi(f)phi(g)F vs phi(g)phi(f)F)
        -> locality_setoid  (line 758: phi(f)phi(g)F ~ phi(g)phi(f)F in borchersSetoid)
           -> gnsQFT.locality  (line 905: gnsFieldOp f (gnsFieldOp g x) = gnsFieldOp g (gnsFieldOp f x))
```

The computational heart is `conjTP_prependField_swap` (line 662), which shows
that swapping coordinates n and n+1 in the `conjTensorProduct` argument
corresponds to swapping the order of `prependField f` and `prependField g`.

#### Covariance proof chain (lines 782-820)

Proves `phi(f)(U(g)y) = U(g)(phi(g^{-1}*f)y)`:

```
prependField_poincareAct_comm   (line 785: SchwartzMap-level identity)
  -> covariance_borchers_funcs  (line 801: funcs-wise identity on BorchersSequence)
     -> covariance_preHilbert   (line 815: identity on PreHilbertSpace)
        -> gnsQFT.covariance    (line 874: identity on GNSHilbertSpace, via inner products)
```

#### Final assembly: `gnsQFT` (line 826)

Packages everything into `WightmanQFT d`:

| Field | Source | Status |
|-------|--------|--------|
| `HilbertSpace` | `GNSHilbertSpace Wfn` | -- |
| `poincare_rep` | `gnsPoincareRep Wfn` | proved |
| `spectrum_condition` | -- | **sorry** (S1) |
| `vacuum` | `gnsVacuum Wfn` | -- |
| `vacuum_normalized` | `gnsVacuum_norm Wfn` | proved |
| `vacuum_invariant` | `gnsVacuum_poincare_invariant Wfn` | proved |
| `field.domain` | `gnsDomain Wfn` | proved |
| `field.operator` | `gnsFieldOp Wfn` | proved |
| `field.operator_add` | `fieldOperator_add_test` + `gnsFieldOp_coe` | proved |
| `field.operator_smul` | `fieldOperator_smul_test` + `gnsFieldOp_coe` | proved |
| `field.operator_vector_add` | `fieldOperator_vector_add` + `gnsFieldOp_coe` | proved |
| `field.operator_vector_smul` | `fieldOperator_vector_smul` + `gnsFieldOp_coe` | proved |
| `field.operator_domain` | `gnsFieldOp_domain Wfn` | proved |
| `field.matrix_element_continuous` | `matrix_element_continuous_aux Wfn` | proved |
| `vacuum_in_domain` | `gnsVacuum_in_domain Wfn` | proved |
| `cyclicity` | -- | **sorry** (S2) |
| `covariance` | `poincareActGNS_coe` + `covariance_preHilbert` + `poincareActGNS_inner` | proved |
| `field_hermitian` | `field_adjoint Wfn` + `gnsFieldOp_coe` + `Completion.inner_coe` | proved |
| `locality` | `locality_setoid Wfn` + `gnsFieldOp_coe` | proved |
| `vacuum_unique.1` | `gnsVacuum_poincare_invariant Wfn` | proved |
| `vacuum_unique.2` | -- | **sorry** (S3) |

---

### Full theorem dependency graph

```
wightman_reconstruction (Main.lean:60)
 := wightman_reconstruction' Wfn (GNSHilbertSpace.lean:951)
     |
     +-- gnsQFT Wfn (GNSHilbertSpace.lean:826)
     |    |
     |    +-- GNSHilbertSpace Wfn (line 313)
     |    |    := UniformSpace.Completion (PreHilbertSpace Wfn)
     |    |         |
     |    |         +-- instInnerProductSpace (line 304)
     |    |         |    +-- instNormedAddCommGroup (line 299)
     |    |         |    +-- instCore (line 277)
     |    |         |         +-- inner_conj_symm    <-- WightmanInnerProduct_hermitian (Core:700)
     |    |         |         +-- inner_re_nonneg     <-- Wfn.positive_definite
     |    |         |         +-- inner_add_left      <-- WightmanInnerProduct_add_left (Core:381)
     |    |         |         +-- inner_smul_left     <-- WightmanInnerProduct_smul_left (Core:513)
     |    |         |         +-- inner_definite      <-- borchersSetoid quotient construction
     |    |         |
     |    |         +-- instAddCommGroup (line 176)
     |    |         |    +-- add_respects_equiv   <-- null_inner_product_zero (Core:764)
     |    |         |    +-- mk_eq_of_funcs_eq    <-- borchersSetoid_of_funcs_eq (line 57)
     |    |         |
     |    |         +-- instModule (line 198)
     |    |              +-- smul_respects_equiv  <-- WightmanInnerProduct_smul_* (Core)
     |    |
     |    +-- gnsPoincareRep Wfn (line 501)
     |    |    +-- poincareActGNS (line 415)
     |    |    |    +-- poincareActPreHilbert_CLM (line 401)
     |    |    |         +-- poincareActPreHilbert_norm (line 389)
     |    |    |              +-- poincareActPreHilbert_inner (PoincareRep:255)
     |    |    |                   +-- WightmanInnerProduct_poincare_invariant (PoincareRep:198)
     |    |    |                        +-- Wfn.translation_invariant
     |    |    |                        +-- Wfn.lorentz_covariant
     |    |    +-- poincareActGNS_adjoint_comp (line 490)  -- unitarity
     |    |    +-- poincareActGNS_one / _mul (lines 441, 451)  -- group law
     |    |
     |    +-- gnsVacuum Wfn (line 316)
     |    |    +-- vacuumState Wfn (GNSConstruction:110)
     |    |         +-- vacuumSequence (Core:937)
     |    |
     |    +-- gnsVacuum_norm (line 583) <-- vacuumState_norm (line 321) <-- vacuum_normalized (GNSConstruction:114)
     |    |                                                                  +-- Wfn.normalized
     |    |
     |    +-- gnsVacuum_poincare_invariant (line 511)  -- U(g)Omega = Omega
     |    |
     |    +-- gnsFieldOp Wfn (line 568)
     |    |    +-- fieldOperator Wfn (Core:1158)
     |    |         +-- fieldOperator_well_defined (Core:1136)
     |    |              +-- fieldOperator_preserves_null (Core:1126)
     |    |                   +-- field_adjoint (Core:1102)
     |    |                   +-- null_inner_product_zero (Core:764)
     |    |
     |    +-- gnsDomain Wfn (line 612) -- dense subspace = image of PreHilbertSpace
     |    |
     |    +-- locality (line 905)
     |    |    +-- locality_setoid (line 758) <-- locality_inner_eq (line 739)
     |    |         <-- locality_term_eq (line 705) <-- Wfn.locally_commutative
     |    |         <-- conjTP_prependField_swap (line 662)
     |    |
     |    +-- covariance (line 874)
     |    |    +-- covariance_preHilbert (line 815) <-- covariance_borchers_funcs (line 801)
     |    |         <-- prependField_poincareAct_comm (line 785)
     |    |
     |    +-- field_hermitian (line 898) <-- field_adjoint (Core:1102)
     |    |
     |    +-- spectrum_condition = sorry [S1]
     |    +-- cyclicity = sorry [S2]
     |    +-- vacuum_unique.2 = sorry [S3]
     |
     +-- operatorPow_gnsQFT_eq Wfn n fs (line 924)
     |    +-- gnsFieldOp_coe (line 577)
     |
     +-- UniformSpace.Completion.inner_coe (Mathlib)
     |
     +-- gns_reproduces_wightman Wfn n fs (GNSConstruction:220)
          +-- foldr_fieldOperator_eq_mk (GNSConstruction:153)
          +-- iteratedAction_funcs_n (GNSConstruction:164)
          +-- iteratedAction_funcs_ne (GNSConstruction:174)
          +-- iteratedAction_bound (GNSConstruction:192)
          +-- W_conjTP_vacuum_zero (GNSConstruction:201)
          +-- Wfn.normalized
```
