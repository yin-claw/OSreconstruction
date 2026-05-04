/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.Core
import OSReconstruction.Wightman.Reconstruction.SchwingerOS
import OSReconstruction.Wightman.SchwartzTensorProduct
import OSReconstruction.SCV.DistributionalUniqueness
import OSReconstruction.GeneralResults.SNAGTheorem
import Bochner.Main

/-!
# Källén-Lehmann spectral representation

The Källén-Lehmann (KL) spectral representation expresses the Wightman 2-point
function as a Fourier transform of a positive measure on momentum space:
$$W_2(x - y) = \int_{\mathbb{R}^{d+1}} e^{-i\, p \cdot (x - y)}\, d\rho(p).$$

**Strategy.**
1. For each test function `f : SchwartzNPoint d 1`, define the
   *spectral function* `φ_f : SpacetimeDim d → ℂ` by
   `φ_f(a) := W_2(f̄ ⊗ T_a f)` where `T_a` is spacetime translation by `a`.
2. Show `φ_f` is continuous (from temperedness `Wfn.tempered`).
3. Show `φ_f` is positive-definite (from R2 `Wfn.positive_definite`).
4. Apply `bochner_theorem` (BochnerMinlos repo, finite-dim Bochner) to obtain
   a unique probability measure (after normalization by `φ_f(0)`) whose
   characteristic function equals `φ_f`.

**Application to cluster decomposition.** For test functions `f, g` with
`∫ f = ∫ g = 0` (orthogonal to the constants), the spectral measure is
supported away from `p = 0`, and Riemann-Lebesgue gives
`W_2(f ⊗ T_a g) → 0` as `‖a‖ → ∞`. This is the cluster property at the
2-point level. The truncated decomposition `W_n^T` extends this to
arbitrary `n`.

**Status.** This file currently scaffolds the spectral function and states
the goal theorem. Discharging the proof is scheduled as follow-up work
(~1 week per `MEMORY.md` calibration; reuses `bochner_theorem` from the
`BochnerMinlos` package).

## References

* Källén, *Helv. Phys. Acta* 25 (1952), 417–434.
* Lehmann, *Nuovo Cimento* 11 (1954), 342–357.
* Streater, Wightman, *PCT, Spin and Statistics, and All That*, §3.4.
* Glimm, Jaffe, *Quantum Physics*, Chapter 6.
* Reed, Simon, *Methods of Modern Mathematical Physics, Vol. II*, §IX.8.
-/

namespace OSReconstruction
namespace KallenLehmann

variable {d : ℕ} [NeZero d]

open MeasureTheory

/-- Spacetime translation of a `SchwartzSpacetime` test function.

`spacetimeTranslate a f x = f (x - a)`. This is the standard QFT
translation operator: `T_a f` is `f` shifted so its support moves by `a`.

Implemented via `SCV.translateSchwartz (-a) f`, which Mathlib-side gives
`f (x + (-a)) = f (x - a)`. -/
noncomputable def spacetimeTranslate (a : SpacetimeDim d)
    (f : SchwartzSpacetime d) : SchwartzSpacetime d :=
  SCV.translateSchwartz (-a) f

@[simp] theorem spacetimeTranslate_apply (a : SpacetimeDim d)
    (f : SchwartzSpacetime d) (x : SpacetimeDim d) :
    spacetimeTranslate a f x = f (x - a) := by
  simp [spacetimeTranslate, SCV.translateSchwartz_apply, sub_eq_add_neg]

/-- **Continuity of translation on Schwartz space** (standard).

For any `f : SchwartzSpacetime d`, the map `a ↦ spacetimeTranslate a f` is
continuous as a map `SpacetimeDim d → SchwartzSpacetime d` in the
Schwartz Fréchet topology.

**Reference:** Hörmander, *The Analysis of Linear Partial Differential
Operators I*, Theorem 7.1.18 (translation is a continuous representation of
`ℝⁿ` on `𝒮(ℝⁿ)`); Reed-Simon Vol I §V.3 (Schwartz space topology and group
representations).

**Strategy (deferred):** Convergence in Schwartz topology means convergence
in every Schwartz seminorm `‖·‖_{k,n}` (sup over `x` of
`‖x‖^k ‖∂^n f(x)‖`). For each fixed `(k, n)`, the function
`a ↦ ‖x‖^k ‖∂^n f(x - a)‖` is uniformly bounded near `a₀` by a Schwartz
decay estimate (`Schwartz seminorm of f` × `(1 + ‖x‖)^{-(k+1)}`-style),
and tends pointwise to `‖x‖^k ‖∂^n f(x - a₀)‖` as `a → a₀`. Dominated
convergence (or direct Schwartz-decay estimate) closes the seminorm
convergence. This proof is ~50 lines once the Schwartz-seminorm-bound
machinery is set up. The compact-support specialization is already in
`SCV/DistributionalUniqueness.lean`
(`tendsto_translateSchwartz_nhds_of_isCompactSupport`).

(NOT VERIFIED — to be vetted. Standard textbook fact.) -/
axiom continuous_spacetimeTranslate
    {d : ℕ} [NeZero d] (f : SchwartzSpacetime d) :
    Continuous (fun a : SpacetimeDim d => spacetimeTranslate a f)

/-- The spectral function of a Wightman 2-point function against a
spacetime test function `f`.

`φ_f(a) := W_2(f̄ ⊗ T_a f)` where:
* `f̄ ⊗ g` = `(SchwartzMap.conjTensorProduct f g)` builds a 2-point
  Schwartz function on `Fin 2 → SpacetimeDim d` evaluating to
  `conj(f(splitFirst _)) * g(splitLast _)`. With both blocks of arity 1,
  the `Fin.rev` in `conjTensorProduct` is trivial, so this simplifies to
  `(x_0, x_1) ↦ conj(f(x_0)) * g(x_1)`.
* `T_a f` is `spacetimeTranslate a f` (i.e., `f(x - a)`).
* The 1-point factors are bridged to `SchwartzMap (Fin 1 → ·) ℂ` via
  `onePointToFin1CLM` from `SchwingerOS.lean`.

By temperedness of `W_2` (continuity of `Wfn.W 2` as a CLM on Schwartz
2-point functions), `φ_f` is continuous in `a`. By Wightman positivity
(R2 = `Wfn.positive_definite`) applied to length-1 Borchers sequences
of translates of `f`, `φ_f` is positive-definite as a function on
`(SpacetimeDim d, +)`. Applying `bochner_theorem` (after normalization
by `φ_f(0)`) extracts a finite positive Borel measure on momentum
space — the *vacuum spectral measure of `f`*. -/
noncomputable def spectralFunction (Wfn : WightmanFunctions d)
    (f : SchwartzSpacetime d) : SpacetimeDim d → ℂ :=
  fun a =>
    Wfn.W 2 ((onePointToFin1CLM d f).conjTensorProduct
              (onePointToFin1CLM d (spacetimeTranslate a f)))

/-- **Vacuum spectral measure of the Wightman 2-point function.**

For each `f : SchwartzNPoint d 1`, there exists a finite positive Borel
measure `μ` on `SpacetimeDim d` (= `Fin (d+1) → ℝ`, i.e. momentum space)
such that the Wightman 2-point matrix element against `f̄ ⊗ T_a f` is the
Fourier transform of `μ`:
  `W_2(f̄ ⊗ T_a f) = ∫ exp(+i ⟨a, p⟩) dμ(p)` for all `a : SpacetimeDim d`,
where `⟨·, ·⟩` is the standard Euclidean inner product (matching Mathlib's
`charFun` convention from Bochner). The forward light cone $V^+$ in
Minkowski space maps to itself under $(p^0, \vec p) \mapsto (p^0, -\vec p)$,
so the support condition (axiom A below) is identical in either convention.

The measure has total mass `μ(univ) = W_2(f̄ ⊗ f)` (the value at `a = 0`),
which is real and ≥ 0 by `Wfn.positive_definite`.

**Proof strategy** (deferred):
1. Show `a ↦ W_2(f̄ ⊗ T_a f)` is continuous (from `Wfn.tempered` plus
   continuity of `translateSchwartz` on `SchwartzMap`).
2. Show it is positive-definite as a function `SpacetimeDim d → ℂ`
   (from `Wfn.positive_definite`: positivity of the Wightman inner
   product on Borchers sequences applied to the sequence
   `[Borchers ↦ T_{a_i} f]_i` gives the matrix
   `[W_2(T_{a_i}f̄ ⊗ T_{a_j}f)]_{ij} ≥ 0`, equivalent to
   positive-definiteness of `φ_f` via translation invariance R1).
3. Normalize by `W_2(f̄ ⊗ f)` to get `φ_f(0) = 1`, apply
   `bochner_theorem` from the `BochnerMinlos` package, and de-normalize.

**Reference:** Streater-Wightman §3.4; Glimm-Jaffe §6.2. -/
theorem vacuum_spectral_measure_W2 (Wfn : WightmanFunctions d)
    (f : SchwartzSpacetime d) :
    ∃ μ : Measure (SpacetimeDim d),
      IsFiniteMeasure μ ∧
      ∀ a : SpacetimeDim d,
        spectralFunction Wfn f a =
          ∫ p : SpacetimeDim d, Complex.exp (Complex.I * (∑ i, (a i : ℂ) * (p i : ℂ))) ∂μ := by
  -- Substantive proof deferred. Plan:
  -- 1. Prove `Continuous (spectralFunction Wfn f)`:
  --    composition of `Wfn.tempered 2` (CLM continuity) with continuity of
  --    `a ↦ (onePointToFin1CLM d f).conjTensorProduct
  --             (onePointToFin1CLM d (spacetimeTranslate a f))`
  --    in the Schwartz topology — uses
  --    `SchwartzMap.conjTensorProduct_continuous_right` (already proved)
  --    plus continuity of `SCV.translateSchwartzCLM` in its parameter.
  -- 2. Prove `IsPositiveDefinite (spectralFunction Wfn f)` on
  --    `(SpacetimeDim d, +)`: for any finite (a_k, c_k),
  --    ∑_{i,j} c_i conj(c_j) φ_f(a_i - a_j) =
  --      Wfn.W 2 (F̄ ⊗ F) where F = ∑_k c_k T_{a_k} f.
  --    Then apply Wfn.positive_definite to the length-1 Borchers
  --    sequence `[F]`. Re-arrangement requires
  --    Wfn.translation_invariant for the difference shift.
  -- 3. Set φ̃(a) := φ_f(a) / φ_f(0) (assuming φ_f(0) ≠ 0; the f = 0
  --    case gives μ = 0 trivially). φ̃ is continuous PD with φ̃(0) = 1.
  --    Apply `bochner_theorem` to get a unique probability measure ν.
  --    Take μ := φ_f(0).re • ν (positive scalar; nonneg from R2).
  -- 4. Verify the Fourier inversion: charFun ν (a) = φ̃(a) is the
  --    Bochner conclusion. Multiply through by φ_f(0).
  sorry

/-! ### Step 1A — Continuity of the spectral function -/

/-- The spectral function is continuous in the translation parameter `a`.

Decomposes as the composition
  `a ↦ spacetimeTranslate a f`              -- continuous (translation in
                                               Schwartz topology)
  `↦ onePointToFin1CLM d (·)`               -- continuous CLM
  `↦ (onePointToFin1CLM d f).conjTensorProduct (·)` -- continuous via
                                            -- `SchwartzMap.conjTensorProduct_continuous_right`
  `↦ Wfn.W 2 (·)`                           -- continuous (R0, `Wfn.tempered`)
of four continuous maps.

The first link — Schwartz-topology continuity of `a ↦ spacetimeTranslate a f`
for general Schwartz `f` (no compact-support hypothesis) — is the only
technical content. Mathlib has it implicitly through the `SchwartzMap`
continuous-translation API. Codebase has the compact-support specialization
in `SCV/DistributionalUniqueness.lean`
(`continuous_apply_translateSchwartz_of_isCompactSupport`); the general
Schwartz case follows from the fact that translation acts continuously on
all Schwartz seminorms (each seminorm of `T_a f - T_b f` is bounded by
`‖a - b‖` times a Schwartz-bound on derivatives of `f`). -/
theorem spectralFunction_continuous (Wfn : WightmanFunctions d)
    (f : SchwartzSpacetime d) :
    Continuous (spectralFunction Wfn f) := by
  -- Decompose as the composition of four continuous maps:
  --   a ↦ spacetimeTranslate a f                       -- by axiom
  --   ↦ onePointToFin1CLM d (·)                        -- CLM
  --   ↦ (onePointToFin1CLM d f).conjTensorProduct (·)  -- continuous_right
  --   ↦ Wfn.W 2 (·)                                    -- R0
  unfold spectralFunction
  exact (Wfn.tempered 2).comp <|
    (SchwartzMap.conjTensorProduct_continuous_right (onePointToFin1CLM d f)).comp <|
      (onePointToFin1CLM d).continuous.comp (continuous_spacetimeTranslate f)

/-! ### Step 1B — Positive-definiteness of the spectral function -/

/-- The spectral function is positive-definite as a function on the additive
group `(SpacetimeDim d, +)`, i.e. the matrix
  `[φ_f(a_i - a_j)]_{i,j}` is positive semidefinite for any finite family
of points `a_k : SpacetimeDim d`.

Standard derivation from Wightman positivity (R2):
1. For `c : Fin N → ℂ` and `a : Fin N → SpacetimeDim d`, set
   `F := ∑_k c_k · T_{a_k} f`. Then
   `Wfn.W 2 (F̄ ⊗ F) = ∑_{i,j} conj(c_i) c_j Wfn.W 2 (T_{a_i}f̄ ⊗ T_{a_j}f)`.
2. By `Wfn.translation_invariant` (R1), each
   `Wfn.W 2 (T_{a_i}f̄ ⊗ T_{a_j}f) = Wfn.W 2 (f̄ ⊗ T_{a_j - a_i}f)
                                  = spectralFunction Wfn f (a_j - a_i)`.
3. Wightman positivity `Wfn.positive_definite` applied to the length-1
   Borchers sequence `[F]` gives `Re (W 2 (F̄ ⊗ F)) ≥ 0`. Since the
   sesquilinear form is automatically Hermitian (from `Wfn.hermitian`),
   the matrix is genuinely PSD.

We use the standard Mathlib `IsPositiveDefinite` definition (a function
`φ : G → ℂ` such that `∑ c_i conj(c_j) φ(a_i - a_j) ≥ 0`). -/
theorem spectralFunction_isPositiveDefinite (Wfn : WightmanFunctions d)
    (f : SchwartzSpacetime d) :
    _root_.IsPositiveDefinite (spectralFunction Wfn f) := by
  -- See plan in docstring. Deferred.
  sorry

/-! ### Step 1C — Spectral support condition (axiom A) -/

/-- **Spectral support in the closed forward light cone (R3 spectral form).**

For any Wightman QFT and any Schwartz test function `f`, the vacuum
spectral measure of `W_2` (= any finite positive Borel measure `μ`
satisfying the Fourier inversion against `spectralFunction Wfn f`) is
supported in the closed forward light cone $\overline{V^+}$.

Equivalently, the joint spectrum of the energy-momentum operators (the
generators of spacetime translations on the GNS Hilbert space) lies in
$\overline{V^+}$ — i.e., positive energy + causal momenta.

This is the **spectral form of R3** (the Wightman spectrum condition).
Our `Wfn.spectrum_condition` packages R3 as analytic continuation of `W_n`
into the forward tube; this axiom converts that analytic-side statement
into the spectral-measure-side statement that downstream cluster
arguments need.

**Reference:** Streater-Wightman §3.4, Theorem 3-2 (spectrum condition);
Reed-Simon Vol II §IX.8 pp. 318–319.

**Strategy (deferred):** From `Wfn.spectrum_condition`, the analytic
continuation `W_analytic` is bounded on the closed forward tube.
Plancherel + the standard Paley-Wiener-type argument show that the
Fourier transform (= our spectral measure `μ`) is supported in the
dual cone — the closed forward light cone. ~3 weeks discharge cost.

(NOT VERIFIED — to be vetted via Gemini deep-think + Codex.) -/
axiom W2_spectral_support_in_forwardCone
    {d : ℕ} [NeZero d] (Wfn : WightmanFunctions d)
    (f : SchwartzSpacetime d)
    (μ : Measure (SpacetimeDim d)) [IsFiniteMeasure μ]
    (h_spec : ∀ a : SpacetimeDim d,
      spectralFunction Wfn f a =
        ∫ p : SpacetimeDim d,
          Complex.exp (Complex.I * (∑ i, (a i : ℂ) * (p i : ℂ))) ∂μ) :
    μ (MinkowskiSpace.ClosedForwardLightCone d)ᶜ = 0

/-! ### Step 1D — Vacuum atom decomposition (axiom B) -/

/-- **Atomic decomposition of the vacuum spectral measure at p = 0.**

For any Wightman QFT and any Schwartz test function `f`, the Dirac atom
at the origin of the vacuum spectral measure of `W_2` equals
`|W_1(f)|²` (the squared modulus of the 1-point Wightman matrix element).

Equivalently: the projection onto the vacuum subspace of the GNS Hilbert
space contributes a `μ({0}) = |W_1(f)|² · δ_0` term to the spectral
measure of `W_2(f̄ ⊗ T_a f)`.

In the standard scalar field convention `Wfn.W 1 _ = 0` (vacuum is
not a "field expectation"), this atom vanishes — the *truncated*
spectral measure has no atom at the origin. Combined with axiom (A),
this gives the spectral form of cluster: the truncated spectral measure
is supported in the open forward cone $V^+ \setminus \{0\}$.

This is the **spectral form of R4 cluster** (combined with vacuum
uniqueness from R1 + R4), in the OS / Källén-Lehmann formulation.

**Reference:** Streater-Wightman Theorem 3-3 (uniqueness of vacuum);
Glimm-Jaffe Theorem 6.2.3 (Källén-Lehmann decomposition).

**Strategy (deferred):** From `Wfn.cluster` (R4), the truncated 2-point
function decays at spatial infinity; equivalently, by Bochner uniqueness,
its spectral measure has no point mass at p = 0 in the truncated
sector. The full spectral measure decomposition follows from R1
(translation invariance picking out the constant mode at p = 0) plus
the GNS reconstruction. ~2 weeks discharge cost.

(NOT VERIFIED — to be vetted via Gemini deep-think + Codex.) -/
axiom W2_spectral_atom_at_zero
    {d : ℕ} [NeZero d] (Wfn : WightmanFunctions d)
    (f : SchwartzSpacetime d)
    (μ : Measure (SpacetimeDim d)) [IsFiniteMeasure μ]
    (h_spec : ∀ a : SpacetimeDim d,
      spectralFunction Wfn f a =
        ∫ p : SpacetimeDim d,
          Complex.exp (Complex.I * (∑ i, (a i : ℂ) * (p i : ℂ))) ∂μ) :
    μ {(0 : SpacetimeDim d)} =
      ENNReal.ofReal (‖Wfn.W 1 (onePointToFin1CLM d f)‖ ^ 2)

end KallenLehmann
end OSReconstruction
