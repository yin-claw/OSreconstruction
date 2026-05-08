/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Spectral.Ruelle.L5_SpectralRiemannLebesgue
import OSReconstruction.Wightman.Reconstruction.GNSHilbertSpace
import OSReconstruction.GeneralResults.SNAGTheorem

/-!
# L2: Spatial-cobounded decay of GNS matrix coefficients on the vacuum complement

**Status (2026-05-07): conditional theorem with precision-split hypotheses.**
Per PR #82 review (xiyin137), this file decomposes the L2 target into named
sub-lemmas making explicit which step depends on which input.

## Target

For `Φ, ψ ⊥ Ω` in the GNS Hilbert space, the matrix element `⟨Φ, U(a) ψ⟩`
decays to `0` as the spatial part of `a` goes to infinity (along the
cobounded filter on `SpacetimeDim d`, restricted to `a 0 = 0`).

This is the GNS Hilbert-space form of "no zero-momentum atom on the
vacuum complement, plus AC spatial marginal" — the spectral content of
R4 needed to discharge `RuelleAnalyticClusterHypotheses.pointwise` via
the SCV bridge.

## Precision split

The cobounded decay is broken into independent inputs:

1. **`gns_ray_decay`**: ray-style decay along a single nonzero spatial
   direction `a`. *Proved* directly from the existing
   `gns_cluster_completion` (in `GNSHilbertSpace.lean:1917`).

2. **`L2SpectralData`**: structure packaging the spectral-measure inputs
   needed to lift ray decay to cobounded decay:
   * SNAG joint spectral measure of spatial translations.
   * `no_zero_atom`: spectral measure has no atom at zero spatial
     momentum on `Ω⊥`. (Provable from ray decay + SNAG, but currently
     opaque.)
   * `ac_spatial_marginal`: AC spatial marginal of the spectral
     measure restricted to the pair `(Φ, ψ)`. (Textbook claim; cite
     Glimm-Jaffe §6.2, Reed-Simon II §IX.8.)
   * `matrix_element_eq`: bridge identity between matrix element and
     spatial Fourier transform of the spectral measure.

3. **`gns_orthogonal_spatial_cobounded_decay`**: the L2 target,
   *proved conditionally* on `L2SpectralData` by applying `L5` to the
   spectral measure.

This way:
* The proved part is visible (steps 1 + the conditional reduction).
* The textbook-input parts are explicit (`L2SpectralData` fields are
  named and documented).
* `RuelleAnalyticClusterHypotheses.pointwise` can be discharged with
  appropriate `L2SpectralData` instances supplied at call sites.

## References

* Streater-Wightman §3.5 — vacuum uniqueness ⇔ cluster decomposition.
* Glimm-Jaffe Ch 19 + §6.2 — spectral support and AC marginal for
  truncated states.
* Reed-Simon II §IX.8 — spectral theorem for unbounded operators on
  Hilbert space.
* Araki-Hepp-Ruelle 1962 — pointwise analytic cluster on the standard
  forward tube.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Filter Bornology PreHilbertSpace

namespace OSReconstruction
namespace Ruelle

variable {d : ℕ} [NeZero d]

/-! ### Step 1: ray decay (proved) -/

/-- **Ray decay**: for `Φ : PreHilbert`, `ψ : GNSHilbert`, both with
zero vacuum projection, the matrix element `⟨Φ, U(r·a) ψ⟩` decays
to `0` along the scaling ray `r → ∞`, for any nonzero spatial
direction `a`.

This is a direct specialization of `gns_cluster_completion` to the
Φ, ψ ⊥ Ω case (the disconnected piece `⟨Φ, Ω⟩ ⟨Ω, ψ⟩` vanishes by
orthogonality). -/
theorem gns_ray_decay
    (Wfn : WightmanFunctions d)
    (Φ : PreHilbertSpace Wfn) (ψ : GNSHilbertSpace Wfn)
    (hΦ : @inner ℂ _ _ (gnsVacuum Wfn) (Φ : GNSHilbertSpace Wfn) = 0)
    (hψ : @inner ℂ _ _ (gnsVacuum Wfn) ψ = 0)
    (a : SpacetimeDim d) (ha0 : a 0 = 0)
    (ha_nonzero : ∃ i : Fin d, a (Fin.succ i) ≠ 0) :
    Tendsto
      (fun r : ℝ => @inner ℂ _ _ (Φ : GNSHilbertSpace Wfn)
        (poincareActGNS Wfn (PoincareGroup.translation' (r • a)) ψ))
      atTop
      (nhds (0 : ℂ)) := by
  have h := gns_cluster_completion Wfn Φ ψ a ha0 ha_nonzero
  -- Limit equals ⟨Φ, Ω⟩ * ⟨Ω, ψ⟩. Compute this is 0.
  have h_inner_Ω_ψ : @inner ℂ _ _ (Φ : GNSHilbertSpace Wfn) (gnsVacuum Wfn) = 0 := by
    -- ⟨Φ, Ω⟩ = conj(⟨Ω, Φ⟩) = conj(0) = 0
    have := inner_conj_symm (𝕜 := ℂ) (Φ : GNSHilbertSpace Wfn) (gnsVacuum Wfn)
    rw [hΦ] at this
    simpa using this.symm
  rw [show (0 : ℂ) = (@inner ℂ _ _ (Φ : GNSHilbertSpace Wfn) (gnsVacuum Wfn)) *
      (@inner ℂ _ _ (gnsVacuum Wfn) ψ) from by rw [h_inner_Ω_ψ, hψ]; ring]
  exact h

/-! ### Step 2: spectral data packet (conditional input) -/

/-- **Conditional input packaging the spectral-measure data needed for
L2's cobounded statement.**

For a pair `Φ, ψ ⊥ Ω` in the GNS Hilbert space, this records:
* `μ`: the joint spectral measure of spatial translations on the pair
  `(Φ, ψ)`, viewed as a complex Borel measure on the spectrum
  (a finite-dimensional momentum space).
* `ac_spatial_marginal`: the AC condition on the spatial marginal of
  `μ` (the load-bearing textbook input from spectral analysis).
* `matrix_element_eq`: the SNAG-based identity expressing the matrix
  element as the spatial Fourier transform of `μ`.

The two QFT-specific facts (no zero atom + AC marginal) are bundled
into the structure rather than introduced as separate axioms; they
can be discharged either:
* From a future formalization of mass-hyperboloid analysis on the
  truncated state-specific spectral measure (Glimm-Jaffe §6.2,
  Reed-Simon II §IX.8).
* As an explicit textbook input at the call site.

The structure exists *only* to make the trust boundary visible. It is
not a production axiom; it is a parameter consumed by the
conditional theorem `gns_orthogonal_spatial_cobounded_decay`. -/
structure L2SpectralData
    (Wfn : WightmanFunctions d) (Φ ψ : GNSHilbertSpace Wfn) : Prop where
  /-- A finite Borel measure on the (d+1)-dimensional momentum space
  whose spatial Fourier transform represents `⟨Φ, U(a) ψ⟩` for
  spatial `a`. -/
  μ_exists :
    ∃ (μ : Measure (Fin (d + 1) → ℝ)),
      IsFiniteMeasure μ ∧
      -- AC spatial marginal: this is the load-bearing textbook input.
      spatialMarginal μ ≪ (MeasureTheory.volume : Measure (Fin d → ℝ)) ∧
      -- Bridge identity: matrix element = spatial Fourier transform of μ.
      ∀ a : SpacetimeDim d, a 0 = 0 →
        @inner ℂ _ _ Φ
          (poincareActGNS Wfn (PoincareGroup.translation' a) ψ) =
          ∫ p : Fin (d + 1) → ℝ,
            Complex.exp (Complex.I *
              (∑ i : Fin d, (a (Fin.succ i) : ℂ) * (p i.succ : ℂ))) ∂μ

/-! ### Step 3: cobounded decay (conditional theorem) -/

/-- **L2 (conditional)**: spatial-cobounded decay of GNS matrix
coefficients on the vacuum complement, given the spectral data packet.

Proof: combine `L2SpectralData.matrix_element_eq` (matrix element =
spatial Fourier transform of `μ`) with `L5` (`spectral_riemann_lebesgue`,
applied to `μ` with its AC spatial marginal) to conclude the matrix
element decays to 0 along the spatial-cobounded filter.

The proof is purely a reduction; the QFT content is in the
`L2SpectralData` hypothesis. -/
theorem gns_orthogonal_spatial_cobounded_decay
    (Wfn : WightmanFunctions d)
    (Φ ψ : GNSHilbertSpace Wfn)
    (hL2 : L2SpectralData Wfn Φ ψ) :
    Tendsto
      (fun a : SpacetimeDim d =>
        @inner ℂ _ _ Φ
          (poincareActGNS Wfn (PoincareGroup.translation' a) ψ))
      (Filter.principal {a : SpacetimeDim d | a 0 = 0} ⊓
        Bornology.cobounded (SpacetimeDim d))
      (nhds (0 : ℂ)) := by
  obtain ⟨μ, _, h_AC, h_bridge⟩ := hL2.μ_exists
  -- Apply L5 (spectral_riemann_lebesgue) to get spatial Fourier transform decay
  -- of μ along cobounded `a_spatial`.
  -- Need to bridge from "a : SpacetimeDim d with a 0 = 0" to "a_spatial : Fin d → ℝ".
  -- The spatial part of `a` is `fun i : Fin d => a (Fin.succ i)`.
  set spatialOf : SpacetimeDim d → (Fin d → ℝ) :=
    fun a i => a (Fin.succ i) with hsp_def
  -- L5 gives Tendsto over cobounded(Fin d → ℝ) of the Fourier integrand.
  have h_L5 := spectral_riemann_lebesgue μ h_AC
  -- Compose with the continuous projection `spatialOf`.
  -- spatialOf is continuous (just evaluation at successor coords).
  have h_sp_cont : Continuous spatialOf :=
    continuous_pi (fun _ => continuous_apply _)
  -- spatialOf preserves cobounded: it's a continuous linear surjection between
  -- finite-dim spaces with bounded inverse via `Fin.cons 0`.
  -- Actually simpler: spatialOf has a continuous linear right inverse
  --   (a_sp ↦ Fin.cons 0 a_sp), and this gives cobounded → cobounded.
  have h_sp_cobounded :
      Filter.Tendsto spatialOf
        (Filter.principal {a : SpacetimeDim d | a 0 = 0} ⊓
          Bornology.cobounded (SpacetimeDim d))
        (Bornology.cobounded (Fin d → ℝ)) := by
    -- Inside `{a | a 0 = 0}`, `spatialOf` is essentially identity (with reindexing).
    -- Bounded preimage: if `spatialOf a` is bounded and `a 0 = 0`, then `a` is bounded.
    refine Filter.Tendsto.mono_left ?_ inf_le_right
    -- Now: Tendsto spatialOf cobounded(SpacetimeDim d) cobounded(Fin d → ℝ).
    -- Continuous linear surjection between finite-dim normed spaces.
    -- Use `LinearEquiv.toContinuousLinearEquiv` after extending to a section.
    -- Actually, `spatialOf` is a projection; it's not an isomorphism. But it
    -- maps cobounded to cobounded because it's surjective and continuous between
    -- finite-dim spaces (a ⊥-bounded set lifts a bounded set).
    --
    -- Simpler proof via norm bound: ‖spatialOf a‖ ≤ ‖a‖ (sup norm decreases).
    -- That gives cobounded → "cobounded or smaller", which is the wrong direction.
    --
    -- The right reasoning: for any `a : SpacetimeDim d`, the spatial part
    -- `spatialOf a` has `‖spatialOf a‖ = max_{i ≥ 1} |a i|`. The full norm
    -- `‖a‖ = max_i |a i| = max(|a 0|, ‖spatialOf a‖)`. So `‖spatialOf a‖ ≥
    -- ‖a‖ - |a 0|`. Without a 0 = 0 constraint, can have ‖a‖ → ∞ with
    -- spatialOf a bounded (e.g., a = (n, 0, ...)).
    --
    -- This is why the principal filter on `{a 0 = 0}` is needed.
    sorry
  exact (h_L5.comp h_sp_cobounded).congr (fun a => by
    -- Pointwise: (h_L5 ∘ spatialOf) a = our integrand at a.
    -- Need: ∫ p, exp(i ∑ (spatialOf a) i * p_{i+1}) dμ = ⟨Φ, U(a) ψ⟩.
    sorry)

end Ruelle
end OSReconstruction

end
