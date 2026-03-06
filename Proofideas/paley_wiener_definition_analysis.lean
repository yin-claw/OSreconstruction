/-
# Proof Ideas: PaleyWiener.lean Definition Issues and Sorry Analysis

## Date: 2026-03-05 (updated)

## Status: CRITICAL DEFINITION BUGS IDENTIFIED AND PARTIALLY FIXED

---

## 1. HasOneSidedFourierSupport — FIXED

### The Bug
The original definition:
```lean
def HasOneSidedFourierSupport (T : SchwartzMap ℝ ℂ → ℂ) : Prop :=
  ∀ (φ : SchwartzMap ℝ ℂ), (∀ x ∈ support φ, x < 0) → T φ = 0
```
This defines: "T annihilates test functions supported on (-∞,0)."
This is the condition that the DISTRIBUTIONAL SUPPORT of T lies in [0,∞), NOT the Fourier support.

Counter-example (Gemini, 2026-03-05): δ₁ (Dirac delta at x=1) satisfies the current definition
(support = {1} ⊂ [0,∞)) but its Fourier transform is e^{-iξ}, which does NOT have support in [0,∞).

### The Fix (applied 2026-03-05)
The correct definition:
```lean
def HasOneSidedFourierSupport (T : SchwartzMap ℝ ℂ → ℂ) : Prop :=
  ∀ (φ : SchwartzMap ℝ ℂ), (∀ x ∈ support φ, x < 0) →
    T (SchwartzMap.fourierTransformCLM ℂ φ) = 0
```
This says: T(F[φ]) = 0 for supp(φ) ⊂ (-∞,0). By Fourier duality, T(F[φ]) = T̂(φ).
So this correctly says: T̂ annihilates test functions supported on (-∞,0), i.e., supp(T̂) ⊆ [0,∞).

Required import: `Mathlib.Analysis.Distribution.SchwartzSpace.Fourier`

---

## 2. HasFourierSupportIn — NOT YET FIXED (TYPE ISSUE)

### The Bug
The definition:
```lean
def HasFourierSupportIn {m : ℕ} (T : SchwartzMap (Fin m → ℝ) ℂ → ℂ)
    (S : Set (Fin m → ℝ)) : Prop :=
  ∀ (φ : SchwartzMap (Fin m → ℝ) ℂ), (∀ x ∈ support φ, x ∉ S) → T φ = 0
```
Same issue: this captures distributional support, not Fourier support.

### The Type Problem
`SchwartzMap.fourierTransformCLM` requires `InnerProductSpace ℝ V` where the norm matches
the inner product. But `Fin m → ℝ` in Mathlib uses the **sup norm** (Pi.normedAddCommGroup),
which does NOT match the ℓ²-inner product (Pi.innerProductSpace). Hence type error.

### Correct Fix (not yet applied)
Replace `Fin m → ℝ` with `EuclideanSpace ℝ (Fin m)` throughout:
- `HasFourierSupportIn` definition
- `dualCone` definition
- `paley_wiener_cone`, `paley_wiener_converse` signatures
- All other multi-dimensional PW lemmas

This requires refactoring the entire multi-d PW framework. Left as TODO.

---

## 3. paley_wiener_one_step and paley_wiener_one_step_simple — INCORRECT HYPOTHESES

### The Problem
The `h_spectral` condition in both theorems uses DISTRIBUTIONAL support:
```lean
h_spectral : ∀ φ, (∀ x ∈ support φ, x < 0) → ∫ t, F(t) * φ(t) = 0
```
This says: the boundary value function has distributional support in [0,∞), i.e., f = 0 a.e. on (-∞,0).

### Physical Application Mismatch
The OS spectral condition gives: the Schwinger function's Fourier transform is supported in [0,∞)
(from positivity of the Hamiltonian). This is FOURIER SUPPORT, not distributional support.

These are different conditions:
- Distributional support in [0,∞): f(x) = 0 for x < 0
- Fourier support in [0,∞): f̂(ξ) = 0 for ξ < 0 ↔ f is a BV from above (holomorphic in UHP)

The Paley-Wiener theorem for the OS reconstruction should use the FOURIER support condition.

### The Conclusion Problem in paley_wiener_one_step_simple
The conclusion `∀ x : ℝ, F_ext ↑x = f x` (pointwise equality on ℝ) is INCORRECT for
polynomial-growth functions. For f ∈ L¹ ∩ L²([0,∞)), the Laplace transform F(z) = ∫₀^∞ f(t)e^{izt}dt
has F(x) = (Fourier transform of f)(x) which need not equal f(x). The boundary value of F on ℝ
is the Fourier transform f̂, NOT f itself.

### Correct Conclusion
The conclusion should be that F_ext has distributional boundary value equal to f:
```lean
∀ φ : SchwartzMap ℝ ℂ,
  Tendsto (fun η => ∫ x, F_ext (x + η*I) * φ x) (nhdsWithin 0 (Ioi 0)) (nhds (∫ x, f x * φ x))
```

---

## 4. Sorry Status in PaleyWiener.lean

All 5 sorrys remain blocked by FL theory not in Mathlib:

| Sorry | Status | Blocker |
|-------|--------|---------|
| `paley_wiener_half_line` | SORRY | Needs FL distribution theory |
| `paley_wiener_cone` | SORRY | Needs multi-d FL theory |
| `paley_wiener_converse` | SORRY | Needs FL inversion |
| `paley_wiener_one_step` | SORRY | Needs PW half-line + Osgood |
| `paley_wiener_one_step_simple` | SORRY + WRONG STATEMENT | See above |

`paley_wiener_unique` is PROVED (uses distributional_uniqueness_tube).

---

## 5. Proof Strategy for paley_wiener_half_line (with corrected definition)

With the correct Fourier support definition, the proof strategy is:

**Approach: Smooth Cutoff (Fourier-Laplace)**

Define: F(z) = T(F^{-1}[χ(ξ) e^{izξ}]) where χ is a smooth cutoff (= 1 for ξ ≥ 0, = 0 for ξ ≤ -1).

For Im(z) > 0: χ(ξ)e^{izξ} = χ(ξ) e^{iRe(z)ξ} e^{-Im(z)ξ}
- For ξ ≥ 0: decays as e^{-Im(z)ξ} ✓
- For ξ ≤ -1: χ(ξ) = 0 ✓
- For -1 ≤ ξ ≤ 0: bounded ✓
So ξ ↦ χ(ξ)e^{izξ} is in L¹(ℝ), and its inverse FT F^{-1}[χe^{iz·}] ∈ 𝓢(ℝ,ℂ) (by smooth cutoff).

Holomorphicity: differentiate under T.
BV condition: as η → 0+, F^{-1}[χe^{iz·}] → F^{-1}[χe^{ix·}]. For the HasOneSidedFourierSupport
condition (supp(T̂) ⊆ [0,∞)): T(F^{-1}[φ]) = T̂(φ)/normalization, so T(F^{-1}[χe^{ix·}])
= T̂(χ e^{ix·})(ξ) which recovers T̂ at real frequencies ξ ≥ 0 → the BV is T(f) for Schwartz f.

Key obstacle in Lean formalization:
- Showing F^{-1}[χ(ξ)e^{izξ}] ∈ 𝓢(ℝ,ℂ) as a function of z (holomorphic map into Schwartz)
- Differentiating T under the Schwartz topology
- Identifying the BV via the HasOneSidedFourierSupport condition

---

## 6. isConnected_permutedExtendedTube_inter_translate Analysis

Gemini consultation (2026-03-05) suggests D = PET ∩ (PET-c) might be DISCONNECTED for general c.
The "starburst" structure of PET could fracture under translation.

**Recommendation (Gemini Path B)**: Instead of proving D is connected, prove bhw_translation_invariant
using only the connected component of D containing FT ∩ (FT-c):
1. D' = connected component of D containing FT ∩ (FT-c)
2. G = F_ext on FT ∩ (FT-c) ⊆ D'
3. Identity theorem on D': G = F_ext on all of D'
4. For z ∉ D', the translation invariance might not hold (if D is disconnected)

This weakens `bhw_translation_invariant` but might be mathematically correct.

**Alternative**: Reformulate everything in difference variables (Gemini Path A) — requires
major refactoring but matches the physics literature (Streater-Wightman pg. 65).

Numerical evidence: 9 test cases for d=1, n=2 all returned 1 connected component (D connected).
Confidence: medium-high for small n,d but uncertain for large n.

---

## 7. LaplaceSchwartz.lean Sorrys

All 5 sorrys require FL theory (Vladimirov §25-26), not in Mathlib:
1. `fourierLaplace_continuousWithinAt` — requires pointwise (not distributional) BV extension
   (stronger than HasFourierLaplaceRepr provides without regularity assumptions on dist)
2. `fourierLaplace_uniform_bound_near_boundary` — requires growth bounds from FL repr
3. `fourierLaplace_polynomial_growth` — Vladimirov Theorem 25.5
4. `polynomial_growth_of_continuous_bv` — requires FL repr → regularity
5. `fourierLaplace_boundary_continuous` — requires regularity of boundary function

All blocked until FL theory is formalized in Mathlib or built from scratch.

---

## 8. SchwingerAxioms.lean Sorrys

All 5 sorrys require FL/PW theory or deep distribution theory:
1. `polynomial_growth_forwardTube_full` — Vladimirov, requires FL repr
2. `polynomial_growth_on_PET` — depends on (1)
3. `schwinger_os_term_eq_wightman_term` — distributional BV identity; requires PW
4. `bhw_pointwise_cluster_euclidean` — analytic continuation of cluster property
5. `W_analytic_cluster_integral` — depends on (4), DCT application

---

## 9. OSToWightman.lean Axiom Transfer Sorrys

All 12 sorrys require FL/PW theory:
- `inductive_analytic_continuation` — the central sorry; needs PW one-step extension
- `schwinger_holomorphic_on_base_region` — Schwinger kernel ↔ distribution
- `extend_to_forward_tube_via_bochner` — Bochner tube theorem (itself sorry)
- `full_analytic_continuation` (2 holes) — combination
- `forward_tube_bv_tempered` — Vladimirov distributional BV theorem
- Axiom transfers (5 sorrys) — all depend on FL+BV infrastructure
- `bvt_cluster` — cluster property transfer

Note on `bv_hermiticity_transfer` (line 625): This sorry may be missing an OS Hermiticity/
reality axiom in its hypothesis list. The OS axioms should include:
S_n(g) = conj(S_n(f)) when g(x) = conj(f(rev x))
Check OsterwalderSchraderAxioms in SchwingerAxioms.lean.

---

## 10. Root Blocker Summary

**All project sorrys ultimately blocked by ONE root blocker:**

> Fourier-Laplace theory for tube domains (Vladimirov §25-26) is NOT in Mathlib.

Required theory:
1. The Fourier-Laplace transform T(ξ ↦ e^{iz·ξ}) for tempered distributions T
2. Holomorphicity on the tube domain T(C) when supp(T̂) ⊆ dualCone(C)
3. Polynomial growth bounds (Theorem 25.5 in Vladimirov)
4. Distributional boundary value recovery

Until this is in Mathlib or built from scratch, the project will remain heavily sorry-laden.

-/

section PaleyWienerAnalysis
end PaleyWienerAnalysis
