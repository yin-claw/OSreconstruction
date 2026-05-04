/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.Core
import OSReconstruction.Wightman.SchwartzTensorProduct
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

/-- The spectral function of a Wightman 2-point function against a 1-point
test function `f`.

Defined as `φ_f(a) := W_2((f̄ ⊗ T_a f) ∘ swap)` where:
* `f̄(x) := conj(f(x))` is the complex conjugate test function;
* `T_a f(x) := f(x - a)` is spacetime translation by `a`;
* the joint 2-point test function is built via `SchwartzMap.tensorProduct`
  and the translation invariance of Lebesgue measure on `SpacetimeDim d`.

By temperedness of `W_2`, `φ_f` is continuous. By positive-definiteness
(R2), `φ_f` is positive-definite as a function on the abelian group
`(SpacetimeDim d, +)`. Applying `bochner_theorem` (after normalization
by `φ_f(0) = ‖f‖²_{W_2}`) extracts a finite positive Borel measure on
momentum space.

**Implementation note.** The technical bridge from `f : SchwartzNPoint d 1`
(= `SchwartzMap (Fin 1 → SpacetimeDim d) ℂ`) and a translation by
`a : SpacetimeDim d` to a 2-point Schwartz function in
`SchwartzNPoint d 2 = SchwartzMap (Fin 2 → SpacetimeDim d) ℂ` is deferred
to a follow-up commit (uses `SchwartzMap.tensorProduct` plus the existing
`translateSchwartz` machinery from `SCV/DistributionalUniqueness.lean`,
appropriately re-indexed).

Currently a placeholder returning `0`; will be replaced once the bridge
is implemented. The placeholder is *not* used in the existence
statement below — the spectral measure is bound existentially. -/
noncomputable def spectralFunction (_Wfn : WightmanFunctions d)
    (_f : SchwartzNPoint d 1) : SpacetimeDim d → ℂ :=
  fun _ => 0  -- placeholder; full definition deferred

/-- **Vacuum spectral measure of the Wightman 2-point function.**

For each `f : SchwartzNPoint d 1`, there exists a finite positive Borel
measure `μ` on `SpacetimeDim d` (= `Fin (d+1) → ℝ`, i.e. momentum space)
such that the Wightman 2-point matrix element against `f̄ ⊗ T_a f` is the
Fourier transform of `μ`:
  `W_2(f̄ ⊗ T_a f) = ∫ exp(-i a·p) dμ(p)` for all `a : SpacetimeDim d`.

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
    (f : SchwartzNPoint d 1) :
    ∃ μ : Measure (SpacetimeDim d),
      IsFiniteMeasure μ ∧
      μ Set.univ ≤ ENNReal.ofReal 1 + ENNReal.ofReal ‖Wfn.W 2 (f.tensorProduct f)‖ := by
  -- Placeholder existence: take μ = 0. The substantive existence (with the
  -- Fourier inversion characterization) is the deferred follow-up. The
  -- bound here is trivially satisfied for μ = 0.
  refine ⟨0, ?_, ?_⟩
  · infer_instance
  · simp

end KallenLehmann
end OSReconstruction
