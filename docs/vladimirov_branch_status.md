# Vladimirov-Tillmann Proof Branch Status

Branch: `vladimirov-tillmann-phase1-2` on `myfork` (mrdouglasny/OSreconstruction)

## Overview

10 new files, ~3200 lines. Goal: eliminate the `vladimirov_tillmann` axiom and prove the VT converse (growth → BV) needed for OS reconstruction.

**3 complete files** (0 axioms, 0 sorrys):
- `SCV/DualCone.lean` (220 lines) — dual cone properties, Hahn-Banach separation
- `SCV/ConeCutoffSchwartz.lean` (864 lines) — concrete ψ_{z,R} construction, all decay estimates
- `SCV/VladimirovProof.lean` (~80 lines) — consistency of axiom package

## Axioms (6)

All reviewed by Gemini Deep Think and confirmed TRUE.

### In `SCV/PaleyWienerSchwartz.lean` (3):

**1. `psiZRSchwartz_seminorm_vladimirovBound`**

For the dynamically-scaled Schwartz family ψ_{z,R(z)} where R(z) = 1/(1+‖Im z‖):

$$\|\psi_{z,R(z)}\|_{k,n} \leq B \cdot (1 + \|z\|)^N \cdot \left(1 + \frac{1}{\mathrm{dist}(\mathrm{Im}\,z, \partial C)}\right)^M$$

The (k,n)-Schwartz seminorm grows polynomially in ‖z‖ with an inverse-boundary-distance singularity. The polynomial growth comes from chain-rule factors R^{-n} = (1+‖y‖)^n when differentiating the scaled cutoff χ(ξ/R). The dist⁻¹ factor captures the blow-up of sup_{ξ ∈ C*} ‖ξ‖^k exp(-y·ξ) as y approaches ∂C (the peak of r^k exp(-Δr) is at r = k/Δ, giving Δ^{-k}).

**2. `multiDimPsiZ_seminorm_difference_bound`**

For z near z₀ in the tube (fixed R=1):

$$\|\psi_z - \psi_{z_0}\|_{k,n} \leq D \cdot \|z - z_0\| \qquad \text{for } \|z - z_0\| < \delta_0$$

Lipschitz continuity of z ↦ ψ_z in Schwartz seminorms. The constant D depends on z₀ (absorbing the finite dist(Im z₀, ∂C)⁻¹ factor). TRUE because the exponential exp(iz·ξ) is Lipschitz in z on compact subsets of the tube, and the cutoff provides uniform support control.

**3. `multiDimPsiZ_differenceQuotient_seminorm_bound`**

The difference quotient converges in Schwartz seminorms:

$$\left\|\frac{\psi_{z+he_j} - \psi_z}{h} - \psi'_j\right\|_{k,n} \leq D \cdot |h| \qquad \text{for } |h| < \delta_0$$

where ψ'_j(ξ) = χ(ξ) · iξ_j · exp(iz·ξ) is the z_j-derivative. TRUE by the Taylor remainder |exp(ihξ_j) - 1 - ihξ_j| ≤ |h|²ξ_j²/2 combined with cutoff × exponential decay.

### In `GeneralResults/` (3):

**4. `schwartz_seminorm_cutoff_exp_bound`** (SchwartzCutoffExp.lean)

For χ smooth with bounded derivatives and L : ℝ^m → ℂ linear with Re(Lξ) ≤ -c‖ξ‖ on supp(χ):

$$\|ξ\|^k \cdot \|D^n[\chi \cdot e^L](ξ)\| \leq B \cdot (1 + \|L\|)^n$$

The Leibniz rule gives D^n[χ·exp(L)] = Σ C(n,j) D^j[χ] · D^{n-j}[exp(L)]. Each term has ‖D^j χ‖ ≤ C_j (bounded), ‖D^{n-j} exp(L)‖ ≤ ‖L‖^{n-j} exp(-c‖ξ‖) (exponential decay), and ‖ξ‖^k exp(-c‖ξ‖) ≤ (k/ce)^k (polynomial × exponential). Summing gives B(1+‖L‖)^n.

**5. `hasDerivAt_schwartz_integral`** (DiffUnderIntegralSchwartz.lean)

Differentiation under the integral sign for Schwartz test functions:

$$\frac{d}{dt}\int F(t,x)\,\varphi(x)\,dx = \int \frac{\partial F}{\partial t}(t_0,x)\,\varphi(x)\,dx$$

when F(t,·) has uniform polynomial growth and ∂F/∂t has polynomial growth on a neighborhood of t₀. The dominator C(1+‖x‖)^N |φ(x)| is integrable (polynomial × Schwartz). Proved via Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le`.

**6. `exists_smooth_cutoff_of_closed`** (SmoothCutoff.lean)

For any closed set S ⊆ ℝ^m, there exists χ : ℝ^m → [0,1] smooth with:
- χ = 1 on an ε-neighborhood of S
- χ = 0 outside the 1-neighborhood of S
- All iterated derivatives globally bounded

Construction: convolution χ = 1_A * φ where A = {dist(·,S) ≤ 1/2} and φ ∈ C_c^∞(B_{1/2}) with ∫φ = 1. The `HilleYosida.BCR_d0.Mollifier` structure in the hille-yosida project has a 1D version.

## Sorrys (7)

### `SCV/FourierSupportCone.lean` (1):

**`fourierSupportInDualCone_of_tube_boundaryValue`** — Tube-holomorphic F with BV W implies W has Fourier support in C*. Needs the full PW-Schwartz bridge (write F = W(ψ_z), then support follows by construction).

### `SCV/PaleyWienerSchwartz.lean` (1):

**`fourierLaplaceExtMultiDim_boundaryValue`** — BV convergence of F(z) = T(ψ_z). Known type error: RHS should be T(FT⁻¹(f)) not T(f). Needs `EuclideanSpace ℝ (Fin m)` cast for Fourier transform.

### `SCV/TubeBoundaryValueExistence.lean` (4):

**`hasDerivAt_tubeSlice_ray`** — d/dτ ∫ F(x+iτη)φ(x)dx = -i ∫ F(x+iτη)(η·∇φ)(x)dx. Needs CR equations + integration by parts + `hasDerivAt_schwartz_integral`.

**`continuous_tubeSlice_ray_deriv`** — τ ↦ tubeSlice F (τ•η) (η·∇φ) is continuous. Needs dominated convergence for parameter-dependent integrals.

**`tube_boundaryValue_of_vladimirov_growth`** — THE main VT converse (growth → BV). Needs Cauchy repeated integration + `distributional_limit_of_equicontinuous`.

**`tube_boundaryValueData_of_polyGrowth'`** — M=0 specialization for OS reconstruction. Needs the CR identity for the Cauchy condition + distributional limit.

### `GeneralResults/DistributionalLimit.lean` (1):

**Cauchy filter → convergent** — Converting the pointwise Cauchy condition to filter convergence in ℂ. Standard completeness argument, needs filter plumbing.

## Dependency DAG

```
exists_smooth_cutoff_of_closed
    → fixedConeCutoff_exists (PROVED)
        → multiDimPsiZR (PROVED, concrete def)

schwartz_seminorm_cutoff_exp_bound
    → psiZRSchwartz_seminorm_vladimirovBound (axiom)
        → multiDimPsiZDynamic_seminorm_bound (PROVED)
            → fourierLaplaceExtMultiDim_vladimirov_growth (PROVED)

hasDerivAt_schwartz_integral
    → hasDerivAt_tubeSlice_ray (sorry)
        → cr_integration_identity (PROVED from helper)
            → tube_boundaryValueData_of_polyGrowth' (sorry, OS critical)

distributional_limit_of_equicontinuous (1 sorry)
    → tube_boundaryValueData_of_polyGrowth' (sorry)
    → tube_boundaryValue_of_vladimirov_growth (sorry)
```

## What's fully proved (no sorrys in chain)

- Dual cone: all properties, separation theorem
- Concrete ψ_{z,R}: construction, decay, support, R-independence, iteratedFDeriv decay
- Fourier-Laplace extension: holomorphicity (via Osgood), Vladimirov growth bound
- Distributional derivative infrastructure
- Tube slice temperedness (each ε-slice defines a tempered distribution)
- R-independence under Fourier support hypothesis

## References

- Vladimirov, "Methods of the Theory of Generalized Functions" (2002), §25
- Hörmander, "The Analysis of Linear PDOs I" (1990), §7.4
- Streater & Wightman, "PCT, Spin and Statistics, and All That", Ch. 2
- See also: `docs/vladimirov_tillmann_proof_plan.md`, `docs/vladimirov_axiom_blueprints.md`, `docs/vladimirov_tillmann_gemini_reviews.md`
