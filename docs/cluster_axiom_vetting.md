# Cluster route axiom vetting log

Vetting record for axioms considered while closing `W_analytic_cluster_integral`
on the `r2e/kallen-lehmann-revival` branch.

**Status (2026-05-07)**: the cluster theorem is closed *conditionally* on
the Ruelle 1962 textbook content, packaged as a `RuelleAnalyticClusterHypotheses`
**hypothesis structure** rather than as production axioms. PR #82 adds
**zero new production axioms**; the trust boundary is visible at every
call site that supplies a hypothesis value.

The KL / spectral-route axioms recorded here as entries 4–7 are parked
in `Proofideas/kallen_lehmann.lean`. Entries 2–3
(`spectral_riemann_lebesgue`, `continuous_translate_schwartz`) are
parked in `Proofideas/spectral_analysis.lean`. Entry 1 (`snag_theorem`)
remains in production via `GeneralResults/SNAGTheorem.lean`.

The "Pivot" section below describes the route to Ruelle and what the
two textbook hypothesis fields encode. Their docstring-level vetting
verdict is "Standard" (Araki-Hepp-Ruelle 1962 Theorem 2 plus the
related uniform polynomial bound); they are *not* production axioms in
the current shape.

---

## Vetted axioms (historical — most superseded by Ruelle pivot)

### 1. `snag_theorem`
**Verdict (Gemini chat, 2026-05-03)**: **Standard** — matches Reed-Simon I VIII.12 exactly.
Hypotheses (strong continuity + group + unitary + identity) are textbook.
Initial draft had axioms on all `Set α`; Gemini flagged as ZFC-inconsistent;
fixed to use `MeasurableSet`-gated indexing.
**Status**: on main from PR #81.

### 2. `spectral_riemann_lebesgue`
**Verdict (Gemini chat, 2026-05-04)**: **Likely correct** with cosmetic fix.
Replaced ad-hoc null-set pull-back form with idiomatic
`Measure.map (...) μ ≪ MeasureTheory.volume`.
**Status**: parked in `Proofideas/spectral_analysis.lean` (per PR #82 review).

### 3. `continuous_translate_schwartz`
**Verdict (Gemini chat, 2026-05-04)**: **Initially FALSE** — operator-norm
continuity was the form I'd used; Gemini correctly noted that translation is
**not** continuous in operator norm even on `L²`/Schwartz (oscillatory test
functions show this). Only **strong continuity** holds (`∀ f, Continuous (a ↦ T_a f)`).
Fixed accordingly. Matches Hörmander I 7.1.18.
**Status**: parked in `Proofideas/spectral_analysis.lean` (per PR #82 review).

### 4. `W2_spectral_support_in_forwardCone`
**Verdict (Gemini chat, 2026-05-03)**: **Standard** — matches Streater-Wightman 3-2.
**Status**: parked in `Proofideas/kallen_lehmann.lean` (per PR #82 review).

### 5. `W2_spectral_atom_at_zero`
**Verdict (Gemini chat, 2026-05-03)**: **Likely correct** — matches Streater-Wightman 3-3.
**Status**: parked in `Proofideas/kallen_lehmann.lean` (per PR #82 review).

### 6. `vacuum_spectral_measure_W2`
**Verdict (Gemini chat, 2026-05-03)**: **Standard** — direct Bochner application
to the continuous PD function `a ↦ ⟨ψ, U(a) ψ⟩`. Mathematical content is a
corollary of the proved `bochner_theorem` (BochnerMinlos).
**Status**: parked in `Proofideas/kallen_lehmann.lean` (per PR #82 review).

### 7. `WightmanTruncated_decomposition_formula`
**Verdict (Gemini chat, 2026-05-04)**: **Likely correct** with caveat.
* The partition formula `W_n = ∑_π ∏ W^T_|B|` is correct.
* Should be stated for **factorizable test functions only**
  (`g_1 ⊗ ⋯ ⊗ g_n`); finite linear combinations are dense in
  `SchwartzNPoint`, and continuity of `W_n` and `W^T_k` extends the
  identity to general Schwartz tests automatically (no separate
  justification needed).
**Status**: parked in `Proofideas/cluster_from_kallen_lehmann.lean`
(per PR #82 review). Factorizable form would be written out
if/when the file is revived.

---

## Rejected axioms

### `wickRotatedIntegral_eq_laplaceFourier_spectralIntegral` (initial draft)
**Verdict (Gemini chat, 2026-05-04)**: **Mathematically false**. Two errors:
1. Conclusion referenced `Wfn.W 1` (1-point distribution) but docstring
   claimed it was about Wick-rotated 2-point integral.
2. Used `f`-smeared spectral measure (from `kallen_lehmann_representation`)
   instead of the universal vacuum spectral measure.
**Action**: replaced with `wickRotated_W2_eq_laplaceFourier_spectralIntegral`
in bilinear form using universal `ρ`.

### `truncated_npoint_spectral_representation` and `truncated_spectral_spatialFourier_decay`
**Verdict (Gemini chat, 2026-05-04)**: **Fatal category error**. For n ≥ 3,
`W^T_n` does **not** possess a Borel spectral measure. Only the 2-point
case has one (positivity `‖φ(f)Ω‖² ≥ 0`). For n ≥ 3, the Fourier transform
of `W^T_n` is a tempered *distribution*, not a measure. The Källén-Lehmann
representation does not generalize this way.

The textbook proof (Glimm-Jaffe §19.4, Ruelle's cluster theorem) uses
**Wightman GNS Hilbert-space operator theory**, not n-point spectral measures.

**Action**: removed both axioms. Replaced with `wightman_gns_schwinger_bridge`
+ `vacuum_unique_zero_momentum`.

---

## Round 2 vetting outcomes (2026-05-04, Gemini chat)

After applying the four fixes from the first round, re-vetted:

* **`vacuum_expectation` correctness** — *Strictly correct without osConj*.
  `⟨Ω, Ψ_f⟩ = ∫ F_ext(wick x) · f(x) dx` for OPTR-supported `f`. No
  reflection needed because Ω is the trivial 0-point function (no second
  state to time-order against).

* **osConj asymmetry** — *Logically and physically consistent*.
  `schwinger_bridge` uses `f.osConj.tensorProduct g_a` because the inner
  product `⟨Ψ_f, U(a) Ψ_g⟩` is conjugate-linear in the bra and the bra is
  physically a "negative-time / incoming" state. `vacuum_expectation` has
  Ω as the bra — no reflection.

* **`truncated_spectral_AC_marginal` placeholder `True`** — *Anti-pattern,
  fix by replacing*. `True` makes the field vacuous. Cleaner formulation
  bypasses the SNAG-PVM API entirely by axiomatizing the actual analytic
  consequence:
  ```
  truncated_spatial_decay :
    ∀ ψ φ : H, ⟨Ω, ψ⟩ = 0 → ⟨Ω, φ⟩ = 0 →
      Tendsto (fun a => ⟨ψ, U(a) φ⟩) (spatial cobounded) (𝓝 0)
  ```
  Renamed accordingly. Applied 2026-05-04.

* **No factorization axiom needed**. `quantize_add` + `quantize_smul` plus
  Hilbert-space orthogonal decomposition `Ψ = ⟨Ω,Ψ⟩Ω + Ψ⊥` is sufficient:
  the connected (Ψ⊥-Ψ⊥) term decays by `truncated_spatial_decay`; the
  (Ω-Ω) term gives `⟨Ψ_f,Ω⟩⟨Ω,Ψ_g⟩` exactly via `vac_inv`; cross terms are
  zero by `vacuum_unique` + orthogonality. No axiom needed for
  `quantize (f.tensorProduct g_a)` factorization.

**Status of round-2 fixes**: applied to `Spectral/ClusterFromKL.lean`.

---

## Open issues from latest vetting (2026-05-04, Gemini)

### Issue 1: `wightman_gns_schwinger_bridge` bundling antipattern

The current statement bundles `H, Ω, Ψ_f, Ψ_g, U` + 5 properties into a
single existential per `(f, g)` pair. **Antipattern**: each (f, g) pair
generates a different, unrelated Hilbert space at the level of Lean types.

**Fix**: convert to a `WightmanReconstruction` class parameterized by `Wfn`:

```lean
class WightmanReconstruction {d : ℕ} (Wfn : WightmanFunctions d) where
  H : Type*
  [normed : NormedAddCommGroup H]
  [inner : InnerProductSpace ℂ H]
  [complete : CompleteSpace H]
  Ω : H
  U : SpacetimeDim d → (H →L[ℂ] H)
  quantize : {n : ℕ} → SchwartzNPoint d n → H
  -- properties below as fields
  unitary_rep : ∀ a, U a ∈ unitary (H →L[ℂ] H)
  U_add : ∀ a b, U (a + b) = U a ∘L U b
  strong_cont : ∀ ψ : H, Continuous (fun a => U a ψ)
  vac_norm : ‖Ω‖ = 1
  vac_inv : ∀ a, U a Ω = Ω
  vacuum_unique : ∀ ψ : H, (∀ a, U a ψ = ψ) → ∃ c : ℂ, ψ = c • Ω
```

This makes the Hilbert space uniquely determined by `Wfn`, so all
sub-claims (vacuum unique, Schwinger bridge, etc.) refer to the **same**
H.

### Issue 2: Domain escape (OS time reflection missing)

The current bridge writes:

```
∫ F_ext(wick(x)) (f.tensorProduct g_a)(x) dx = ⟨Ψ_f, U(a) Ψ_g⟩
```

But **F_ext is undefined where the imaginary parts of consecutive points
cross zero**. With both `f` and `g_a` in OPTR (positive ordered times),
the joint config has imaginary times jumping from large (n-block end) to
small (m-block start) — F_ext is divergent at this transition.

**Fix**: apply OS time reflection (`osConj`) to `f` so that `f`-block
times become negative-and-decreasing, and the appended `(f̃, g_a)` config
has strictly increasing times globally.

```lean
∫ F_ext(wick x) (f.osConj.tensorProduct g_a)(x) dx = ⟨Ψ_f, U(a) Ψ_g⟩
```

This is the **OS bridge** the project's existing infrastructure was
designed for — exactly what xi yin's PR #80 refactor preserved.

### Issue 3: Missing vacuum expectation bridge

To derive cluster `⟨Ψ_f, U(a) Ψ_g⟩ → ⟨Ψ_f, Ω⟩ ⟨Ω, Ψ_g⟩`, we need:

```
⟨Ω, Ψ_f⟩ = ∫ F_ext(wick x) (f̃.tensorProduct ?)(x) dx
```

(or an analogous standalone expression). The current bridge only relates
the **joint** integral to the inner product; we need the **disconnected**
integrals to also have GNS-side counterparts.

**Fix**: extend the bridge axiom (or add a sister axiom) asserting
`⟨Ω, Ψ_f⟩ = ∫ F_ext(wick x_n) f(x_n) dx_n` for OPTR-supported `f` (or the
osConj-corrected version).

### Issue 4: Riemann-Lebesgue AC marginal mismatch

Our `spectral_riemann_lebesgue` requires the spectral measure to have an
**absolutely continuous spatial marginal**. The vacuum-uniqueness axiom only
guarantees no atom at `p = 0`. **No atom at 0 ≠ AC spatial marginal**:
singular continuous measures exist.

The textbook resolution: spectral measures of QFT operator-theoretic
states are supported on mass hyperboloids `p² ≥ m²`, which naturally
project to AC spatial marginals via `dp⁰ / 2E_p`. But this requires
either:

- **Detailed analysis** of mass hyperboloids (Jost-Hepp lemma and
  Radon-Nikodym derivatives) — substantial textbook content (~weeks).
- **Direct axiom** asserting AC spatial marginal as a property of the
  truncated state-specific measure.

**Recommended fix**: add an explicit axiom asserting AC spatial marginal
on the truncated state-specific complex measure. Cited by Glimm-Jaffe
§6.2 + Reed-Simon II §IX.8.

---

## Summary of open work

After this round of vetting:

1. **Refactor** `wightman_gns_schwinger_bridge` from existential bundling to
   `WightmanReconstruction` class. **Substantial restructuring**.

2. **Add** OS time reflection (`osConj`) on `f` in the Schwinger bridge.
   Mechanical fix, ~1 line in the axiom statement.

3. **Add** vacuum expectation bridge axiom: `⟨Ω, Ψ_f⟩ = ∫ F_ext(...) f(x)`.
   ~10 lines.

4. **Add** AC-spatial-marginal axiom for truncated state-specific measure.
   ~10 lines.

5. **Re-vet** the refactored axioms via Gemini.

6. **Refactor** `cluster_2point_from_KL` and `cluster_npoint_from_KL`
   proofs to use the new class-based + corrected axioms.

Total: ~1–2 days of focused refactoring work.

---

## Key insight

The vetting exercise has been **highly valuable**:

- 2 out of 13 vetted axioms were **mathematically false** (`truncated_npoint_spectral_representation`, `truncated_spectral_spatialFourier_decay`).
- 1 axiom was **silently wrong** (`continuous_translate_schwartz` with operator-norm continuity).
- 1 axiom had a **statement-vs-docstring mismatch** (`wickRotatedIntegral_eq_laplaceFourier_spectralIntegral`).
- 1 axiom had a **domain escape bug** flagged but not yet fixed
  (`wightman_gns_schwinger_bridge` needs `osConj`).

Without vetting, we would have spent weeks deriving from false foundations
and getting wrong proofs. The textbook-axiom + Gemini-vetting workflow is
working as designed.

---

## Pivot — 2026-05-05/06: from spectral / KL route to Ruelle 1962

The Källén-Lehmann route encountered structural obstacles (Issues 1–4
above) that were taking weeks to resolve. After consulting Gemini deep-think
(`history/gemini_deep_think.md`) on the analytic cluster question,
identified Araki-Hepp-Ruelle 1962 (Helv. Phys. Acta 35) as the canonical
reference: their **Theorem 2** proves the pointwise analytic cluster.

The route is approved (`docs/cluster_via_ruelle_plan.md`).

### 2026-05-07 update: hypothesis-structure rather than production axioms

Per PR #82 review (xiyin137), the Ruelle textbook content is **not**
introduced as production `axiom` declarations. Instead, it is packaged
as a **conditional-input structure**

```lean
structure RuelleAnalyticClusterHypotheses (Wfn : WightmanFunctions d) (n m : ℕ) : Prop where
  bound : <uniform-in-a polynomial bound, joint-PET-conditioned>
  pointwise : <pointwise factorization on PET, eventually-in-a>
```

with both fields hypothesizing **joint-PET membership** (the analytic
domain of `W_analytic_BHW (n+m)` in the Lean repo) at every evaluation
point, since the joint Wick-rotated config does not always lie in the
standard forward tube `T(n+m)` (only in the permuted variant PET).

### Hypothesis 1: `bound` field

**Statement**: there exist constants `C, N, R > 0` such that for all
forward-tube `z₁, z₂`, spatial `a` with `|⃗a| > R`, and joint-PET
membership of the appended config:
```
‖W_analytic_BHW(append z₁ (z₂ + (0, a)))‖ ≤ C · (1 + ‖z₁‖ + ‖z₂‖)^N.
```
**Crucial property**: `C, N` are **independent of `a`** — the spectral-gap
content of R4 (distributional cluster) lifted to the analytic level.

**Verdict (Gemini deep-think, 2026-05-05)**: **Standard** — corresponds
to the spectral consequence of Streater-Wightman §3.4 and Jost VI.1.

**Sources**: `DT` (deep-think), `LP` (Streater-Wightman §3.4, Jost VI.1).

### Hypothesis 2: `pointwise` field

**Statement**: for all forward-tube `z₁, z₂` with eventual joint-PET
membership of the appended config along the spatial-cobounded filter,
```
W_analytic_BHW(append z₁ (z₂ + (0, a))) → W_analytic_BHW(z₁) · W_analytic_BHW(z₂).
```

**Verdict (Gemini deep-think, 2026-05-05)**: **Standard** — corresponds
to Theorem 2 of Araki-Hepp-Ruelle 1962, adapted from the standard forward
tube to PET (where our Wick-rotated joint configurations naturally live).

**Sources**: `DT` (deep-think), `LP` (Araki-Hepp-Ruelle 1962 Theorem 2 —
"On the asymptotic behaviour of Wightman functions in space-like
directions", Helv. Phys. Acta 35, 164).

### Status

* **Production trust delta**: 0 new axioms.
* **Conditional cluster bridge** (`RuelleClusterBound.lean`): closes
  `W_analytic_cluster_integral`, `wickRotatedBoundaryPairing_cluster`,
  and `schwinger_E4_cluster_OPTR_case` as conditional theorems taking
  `RuelleAnalyticClusterHypotheses` as a parameter.
* **Källén-Lehmann route**: parked in
  `Proofideas/cluster_from_kallen_lehmann.lean` and
  `Proofideas/kallen_lehmann.lean`.
* **L1–L7 proof roadmap** for discharging the hypotheses from R4 +
  spectrum condition: parked in `Proofideas/ruelle_blueprint.lean`.
* **L2 (no zero-momentum atom)**: in production at
  `OSReconstruction/Wightman/Spectral/Ruelle/L2_NoZeroMomentumAtom.lean`.
  Conditional reduction `gns_orthogonal_spatial_cobounded_decay_of`
  is fully proved from L5 + a `L2SpectralData` hypothesis. The
  unconditional `gns_orthogonal_spatial_cobounded_decay` discharges
  via the new axiom `gns_l2_spectral_data_axiom` (see entry 10 below).
* **L5 (spectral Riemann-Lebesgue)**: in production at
  `OSReconstruction/Wightman/Spectral/Ruelle/L5_SpectralRiemannLebesgue.lean`.
  Fully PROVED (no sorrys, no project axioms beyond Mathlib).

---

## Production-axiom additions (Option B for L2)

### 10. `gns_l2_spectral_data_axiom`
**File**: `Wightman/Spectral/Ruelle/L2_NoZeroMomentumAtom.lean`.

**Statement**: for a `WightmanFunctions d` family `Wfn` and a pair of
states `Φ, ψ` in `GNSHilbertSpace Wfn` with both states orthogonal to
the GNS vacuum, there exists a finite Borel measure `μ` on the
spacetime momentum space `Fin (d+1) → ℝ` such that:
1. `μ` has AC spatial marginal w.r.t. Lebesgue.
2. The matrix element `⟨Φ, U(a) ψ⟩` for spatial `a` (with `a 0 = 0`)
   equals the spatial Fourier transform of `μ`.

This is the GNS-spectral-side packaging of:
* SNAG application (existing `snag_theorem` axiom, vetted Standard).
* Polarization for off-diagonal pairs.
* Spectrum support on V̄+ \ {0} for Ω⊥ (R4 cluster + vacuum uniqueness).
* AC spatial marginal via mass-hyperboloid foliation (the deep textbook
  input).

**References**:
* Glimm-Jaffe, *Quantum Physics: A Functional Integral Point of View*,
  §6.2 — spectral support of vacuum expectation values; mass
  hyperboloid analysis.
* Reed-Simon, *Methods of Modern Mathematical Physics II*, §IX.8 —
  SNAG / Stone's theorem and absolutely continuous spectral measures.
* Streater-Wightman, *PCT, Spin and Statistics, and All That*, §3.5 —
  cluster decomposition and vacuum uniqueness.

**Status**: pending vetting (DT). The textbook content is standard for
physical Wightman QFTs satisfying R0–R4. The AC marginal claim is the
load-bearing input; in the absence of a mass gap (lowest mass `m > 0`),
AC follows from R4-cluster + spectrum support analysis on the
truncated states; with mass gap, it follows directly from the
mass-hyperboloid foliation `dp⁰ / 2E_p`.

**Discharge plan** (future work): formalize the mass-hyperboloid
spectral analysis on Ω⊥. Probably 1–3 weeks of focused QFT-spectral
formalization.

### 11. L4 spectral-data axiom (WITHHELD)

**File**: `Wightman/Spectral/Ruelle/L4_UniformPolynomialBound.lean`.

**Status (2026-05-08)**: **Production axiom intentionally withheld.**

A first attempt drafted `wightman_l4_spectral_data_axiom : L4SpectralData
Wfn n m`, mirroring `gns_l2_spectral_data_axiom` in shape — a polarized
Fourier representation of the joint analytic continuation
`W_analytic_BHW (n+m)` along the spatial-shift parameter, with each
polarization-piece measure having total mass polynomially bounded in
`(‖z₁‖, ‖z₂‖)`.

**Vetting verdict (Gemini chat, 2026-05-08)**: **FLAGGED — vacuous /
unsatisfiable**. The bound shape inherited from
`RuelleAnalyticClusterHypotheses.bound` (uniform `C, N` over the entire
`ForwardTube d n × ForwardTube d m`, polynomial only in `‖z‖`) is
**unsatisfiable for any actual Wightman QFT**, including the free
scalar field. Counterexample: for `n = m = 2`, Wick's theorem gives a
disconnected pairing `W₂(z₁,₁, z₁,₂) · W₂(z₂,₁ + a, z₂,₂ + a)` whose
first factor is independent of `a` and blows up as `(z₁,₁ - z₁,₂) →
∂V+` (allowed within the open `ForwardTube d 2`); the polynomial
bound `C(1+‖z₁‖+‖z₂‖)^N` cannot capture this internal singularity.

**The textbook bound** (Streater-Wightman Theorem 3.1.1) includes a
boundary-distance regulator `(1 + Δ(Im z)⁻¹)^M` which is missing from
the current `RuelleAnalyticClusterHypotheses.bound` shape.

**Effect**: axiomatizing the current `L4SpectralData` shape would
make the system inconsistent (False would be provable, since no
witness exists in any model). The axiom was removed.

**What was kept**: the structural definition `L4SpectralData` and the
conditional reduction `ruelle_analytic_cluster_bound_of` — the latter
is `(possibly-vacuous antecedent) → (possibly-vacuous consequent)` and
remains valid regardless of whether either side is satisfiable.

**Project follow-up**: see
`docs/ruelle_bound_vacuity_concern.md` for the full analysis and
proposed repair options (Option A: boundary-distance regulator;
Option B: pointwise-uniform constants via quantifier reordering).
Coordinate with @xiyin137 before changing the
`RuelleAnalyticClusterHypotheses` interface (shared-repo policy).

### Audit table

| Axiom | File:Line | Rating | Sources | Notes |
|-------|-----------|--------|---------|-------|
| `gns_l2_spectral_data_axiom` | L2_NoZeroMomentumAtom.lean | Pending DT | LP (Glimm-Jaffe §6.2, Reed-Simon II §IX.8, Streater-Wightman §3.5) | Single explicit axiom for the GNS-spectral L2 chain; consumed only by `gns_orthogonal_spatial_cobounded_decay`. Pending vetting via Gemini deep-think. |
| `wightman_l4_spectral_data_axiom` (WITHHELD) | L4_UniformPolynomialBound.lean | Flagged (Vacuous) | GR (Gemini chat 2026-05-08), LP (Streater-Wightman 3.1.1, BLT 11.2) | Removed after Gemini vetting. Inherits unsatisfiable bound shape from `RuelleAnalyticClusterHypotheses.bound`. See `docs/ruelle_bound_vacuity_concern.md`. |
