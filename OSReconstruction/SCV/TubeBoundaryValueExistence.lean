/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import OSReconstruction.SCV.VladimirovTillmann
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Tube-Domain Boundary Value Existence from Polynomial Growth

The converse direction of the Vladimirov-Tillmann theorem:
a holomorphic function on a tube domain T(C) with the global Vladimirov
growth bound has tempered distributional boundary values.

This is the **critical SCV theorem** needed for OS reconstruction:
it takes the analytically continued Schwinger functions (which have
polynomial growth from the semigroup contraction) and produces the
Wightman distributions as tempered boundary values.

## Strategy (1D ray integration, avoiding Poincaré lemma)

Fix η ∈ C and approach the boundary along the ray y = tη for t > 0.

1. The Vladimirov bound along the ray: |F(x+itη)| ≤ C(1+|x|)^N · t^{-q}
2. Define the k-th iterated integral using Cauchy's repeated integration formula:
   `G_k(x,t) = (i^k / (k-1)!) ∫_{t₀}^{t} (t-τ)^{k-1} F(x+iτη) dτ`
   This is ONE integral (not k nested integrals), avoiding Fubini boilerplate.
3. For k > q, the t^{-q} singularity is integrable: (t-τ)^{k-1} · τ^{-q} ∈ L¹
4. G_k(x,t) extends continuously to t = 0 as a function H(x)
5. H(x) has polynomial growth (inherited from F)
6. Define the boundary value W as a distributional derivative by duality:
   `⟨W, φ⟩ = (-1)^k ∫ H(x) · ((η·∇_x)^k φ(x)) dx + ⟨correction terms, φ⟩`
   Since φ is Schwartz, (η·∇)^k φ is Schwartz, and the integral converges.

This constructs W ∈ S'(ℝ^m) using only 1D real integrals — no Poincaré lemma,
no Fourier multiplier traps, no Fréchet-valued integration.

## References

- Vladimirov, "Methods of Generalized Functions", §25
- See docs/vladimirov_tillmann_proof_plan.md (Phase 4)
- See docs/vladimirov_tillmann_gemini_reviews.md (ray integration trick)
-/

open scoped Classical ComplexConjugate BigOperators NNReal
open MeasureTheory Complex Filter
noncomputable section

variable {m : ℕ}

/-! ### General-purpose distribution theory axioms -/

/-- A continuous function with polynomial growth defines a tempered distribution
    via integration against Schwartz test functions.

    This is a standard functional analysis fact: if |F(x)| ≤ C(1+‖x‖)^N,
    then φ ↦ ∫ F(x)φ(x) dx is continuous on Schwartz space (because
    polynomial times Schwartz is integrable, and the Schwartz seminorm
    bound gives |∫ Fφ| ≤ C · ‖φ‖_{N+dim+1, 0}).

    Ref: Hörmander, "The Analysis of Linear PDOs I", Theorem 7.1.5 -/
axiom polyGrowth_temperedDistribution {m : ℕ}
    (F : (Fin m → ℝ) → ℂ) (hF_cont : Continuous F)
    (C_bd : ℝ) (N : ℕ) (hC_bd : 0 < C_bd)
    (hF_growth : ∀ x : Fin m → ℝ, ‖F x‖ ≤ C_bd * (1 + ‖x‖) ^ N) :
    ∃ (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ),
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        T φ = ∫ x : Fin m → ℝ, F x * φ x

/-! ### The directional derivative operator -/

/-- The directional derivative as a continuous linear operator on Schwartz space.
    `(η · ∇) φ (x) = ∑_j η_j · (∂φ/∂x_j)(x)`

    This is a CLM because differentiation is continuous on Schwartz space
    (it increases the Schwartz seminorm index by 1). -/
axiom directionalDerivSchwartz {m : ℕ} (η : Fin m → ℝ) :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzMap (Fin m → ℝ) ℂ

/-- The distributional directional derivative of a tempered distribution.
    Defined by duality: ⟨(η·∇)T, φ⟩ = -⟨T, (η·∇)φ⟩.

    This is NOT an axiom — it's just `-(T.comp (directionalDerivSchwartz η))`,
    which is automatically a CLM by `ContinuousLinearMap.comp` + `Neg`. -/
def distribDirectionalDeriv {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) (η : Fin m → ℝ) :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ :=
  -(T.comp (directionalDerivSchwartz η))

theorem distribDirectionalDeriv_apply {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) (η : Fin m → ℝ)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    distribDirectionalDeriv T η φ = -(T (directionalDerivSchwartz η φ)) := by
  simp [distribDirectionalDeriv]

/-- The k-th iterated distributional directional derivative. -/
def iteratedDistribDirectionalDeriv {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) (η : Fin m → ℝ) (k : ℕ) :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ :=
  ((-1 : ℂ) ^ k) • (T.comp ((directionalDerivSchwartz η) ^ k))

/-- The k-th iterated directional derivative. -/
def iteratedDirectionalDerivSchwartz (η : Fin m → ℝ) (k : ℕ) :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzMap (Fin m → ℝ) ℂ :=
  (directionalDerivSchwartz η) ^ k

/-! ### The slice functional -/

/-- Integration of F(x+iy) against a test function, for y in the tube. -/
def tubeSlice
    (F : (Fin m → ℂ) → ℂ) (y : Fin m → ℝ)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) : ℂ :=
  ∫ x : Fin m → ℝ, F (fun i => (x i : ℂ) + (y i : ℂ) * I) * φ x

/-! ### Cauchy's repeated integration formula -/

/-- The k-th iterated integral of the slice functional along a ray η ∈ C.
    Using Cauchy's formula for repeated integration:

    `G_k(φ, t) = (1/(k-1)!) ∫_{t₀}^{t} (t-τ)^{k-1} · tubeSlice F (τ•η) φ dτ`

    This is a single 1D integral, avoiding recursive definition + Fubini. -/
def cauchyRepeatedIntegral
    (F : (Fin m → ℂ) → ℂ) (η : Fin m → ℝ) (t₀ : ℝ)
    (k : ℕ) (φ : SchwartzMap (Fin m → ℝ) ℂ) (t : ℝ) : ℂ :=
  (((k - 1).factorial : ℝ)⁻¹ : ℂ) *
    ∫ τ in Set.Icc t₀ t,
      ((t - τ) ^ (k - 1) : ℝ) * tubeSlice F (τ • η) φ

/-! ### Sub-lemmas for the boundary value construction -/

/-- For each ε > 0 and η ∈ C, the slice functional defines a tempered distribution.
    This is because F(x+iεη) has polynomial growth in x (from the Vladimirov bound
    with y = εη fixed), so `polyGrowth_temperedDistribution` applies. -/
theorem tubeSlice_temperedDistribution
    {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_cone : IsCone C)
    {F : (Fin m → ℂ) → ℂ}
    (hF_cont : ContinuousOn F (SCV.TubeDomain C))
    {C_bd : ℝ} {N M : ℕ} (hC_bd : 0 < C_bd)
    (hF_growth : ∀ z ∈ SCV.TubeDomain C,
      ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N *
        (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M)
    (η : Fin m → ℝ) (hη : η ∈ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ (T_ε : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ),
      ∀ φ, T_ε φ = tubeSlice F (ε • η) φ := by
  -- F_ε(x) := F(x + iεη) is continuous with polynomial growth in x:
  -- |F(x+iεη)| ≤ C_bd (1+‖(x,εη)‖)^N · (dist(εη,∂C)⁻¹ + 1)^M
  -- The dist factor is a constant D_ε for fixed ε,η.
  -- So |F_ε(x)| ≤ C_bd · D_ε^M · (1+‖x‖+ε‖η‖)^N ≤ C' · (1+‖x‖)^N
  -- Then polyGrowth_temperedDistribution gives the result.
  --
  -- Step 1: εη ∈ C (cone scaling)
  have hεη : ε • η ∈ C := hC_cone η hη ε hε
  -- Step 2: x+iεη ∈ TubeDomain C for all x
  have hmem : ∀ x : Fin m → ℝ,
      (fun i => (x i : ℂ) + ((ε • η) i : ℝ) * I) ∈ SCV.TubeDomain C := by
    intro x
    show (fun i => ((fun i => (x i : ℂ) + ((ε • η) i : ℝ) * I) i).im) ∈ C
    convert hεη using 1
    ext i; simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_im, Complex.I_re, Pi.smul_apply, smul_eq_mul]
  -- Step 3: F_ε(x) = F(x+iεη) has polynomial growth
  -- |F_ε(x)| ≤ C_bd · (1+‖z‖)^N · D^M where D = (1+dist(εη,∂C)⁻¹)
  -- Since ‖z‖ ≤ ‖x‖ + ε‖η‖ and D is constant, this is ≤ C'(1+‖x‖)^N
  sorry

/-- The CR-integration identity: along a ray y = tη, integrating k times gives
    `(iη·∇_x)^k G_k(x,t) = F(x+itη) - (lower-order correction terms from t₀)`.

    This is a distributional identity obtained by:
    1. ∂/∂t F(x+itη) = i(η·∇_x) F(x+itη) (Cauchy-Riemann)
    2. Integrating both sides k times in t from t₀ to t
    3. Using Cauchy's repeated integration formula -/
theorem cr_integration_identity
    {C : Set (Fin m → ℝ)}
    {F : (Fin m → ℂ) → ℂ}
    (hF_hol : DifferentiableOn ℂ F (SCV.TubeDomain C))
    (η : Fin m → ℝ) (hη : η ∈ C)
    (hC_cone : IsCone C) (hC_open : IsOpen C)
    (t₀ t : ℝ) (ht₀ : 0 < t₀) (ht : 0 < t)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    tubeSlice F (t • η) φ =
      tubeSlice F (t₀ • η) φ +
      I * tubeSlice F (t • η) (directionalDerivSchwartz η φ) -
      I * tubeSlice F (t₀ • η) (directionalDerivSchwartz η φ) +
      sorry := by -- higher order terms from integration by parts
  sorry

/-! ### The boundary value construction -/

/-- **Main theorem**: A holomorphic function on T(C) with Vladimirov growth
    has tempered distributional boundary values.

    This is the converse of `vladimirov_tillmann` and the critical SCV
    theorem needed for OS reconstruction.

    Equivalent to xiyin's `tube_boundaryValueData_of_polyGrowth` in
    `SCV/TubeBoundaryValues.lean`, but with the full Vladimirov bound
    (including boundary-distance factor). -/
theorem tube_boundaryValue_of_vladimirov_growth
    {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_ne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ}
    (hF_hol : DifferentiableOn ℂ F (SCV.TubeDomain C))
    {C_bd : ℝ} {N M : ℕ} (hC_bd : 0 < C_bd)
    (hF_growth : ∀ (z : Fin m → ℂ), z ∈ SCV.TubeDomain C →
      ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N *
        (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M) :
    ∃ (W : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ),
      ∀ (φ : SchwartzMap (Fin m → ℝ) ℂ)
        (η : Fin m → ℝ), η ∈ C →
        Tendsto
          (fun ε : ℝ => tubeSlice F (ε • η) φ)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W φ)) := by
  -- Proof outline (1D ray integration):
  -- 1. Fix η ∈ C, t₀ > 0. Along the ray y = tη:
  --    |tubeSlice F (tη) φ| ≤ ∫ |F(x+itη)| |φ(x)| dx
  --    ≤ ∫ C_bd (1+‖x‖+t‖η‖)^N · t^{-M} · |φ(x)| dx
  --    ≤ C' · t^{-M}  (since φ is Schwartz, the x-integral is finite)
  --
  -- 2. Define G_k via cauchyRepeatedIntegral with k = M + 1.
  --    The integrand (t-τ)^{k-1} · tubeSlice has singularity τ^{-M},
  --    and (t-τ)^{k-1} · τ^{-M} is integrable on [t₀, t] since k > M.
  --
  -- 3. G_k(φ, t) extends continuously to t = 0:
  --    As t → 0+, the integral ∫_{t₀}^{0} ... = -∫_{0}^{t₀} (0-τ)^{k-1} · ... dτ
  --    This is a convergent integral (k > M).
  --    Define H(φ) = G_k(φ, 0) = (-1)^{k-1} / (k-1)! ∫_0^{t₀} τ^{k-1} · tubeSlice F (τη) φ dτ
  --
  -- 4. H is a continuous linear functional on Schwartz space:
  --    - Linear: tubeSlice is linear in φ, integral preserves linearity
  --    - Continuous: |H(φ)| ≤ C · ‖φ‖_{s,s} from the growth bound + Schwartz decay
  --
  -- 5. The Cauchy-Riemann equations give:
  --    (η·∇_x)^k G_k(φ, t) = tubeSlice F (tη) φ - (correction from t₀)
  --    Taking t → 0+: (η·∇_x)^k H(φ) = W(φ) - correction
  --    Define W by duality:
  --    ⟨W, φ⟩ = (-1)^k H((η·∇_x)^k φ) + correction(φ)
  --
  -- 6. W ∈ S' and the BV convergence follows from the construction.
  sorry

/-- Simplified version matching xiyin's interface in TubeBoundaryValues.lean:
    just polynomial growth (no boundary-distance factor), Wightman-style types. -/
theorem tube_boundaryValueData_of_polyGrowth'
    {n d : ℕ}
    (C : Set (Fin n → Fin (d + 1) → ℝ))
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_ne : C.Nonempty)
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_hol : DifferentiableOn ℂ F (TubeDomainSetPi C))
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hF_growth : ∀ z ∈ TubeDomainSetPi C,
      ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N) :
    ∃ (W : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ),
      ∀ (φ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ)
        (η : Fin n → Fin (d + 1) → ℝ),
        η ∈ C →
        Tendsto
          (fun ε : ℝ => ∫ x : Fin n → Fin (d + 1) → ℝ,
            F (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W φ)) := by
  -- This follows from tube_boundaryValue_of_vladimirov_growth
  -- by noting that polynomial growth implies the Vladimirov bound
  -- (with M = 0, since no boundary-distance factor is needed).
  sorry

end
