/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import OSReconstruction.SCV.DualCone
import OSReconstruction.SCV.LaplaceSchwartz
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Fourier Support in Dual Cones

This file defines `HasFourierSupportInDualCone`, the multi-dimensional generalization
of `HasOneSidedFourierSupport` from `PaleyWiener.lean`. A tempered distribution T
has Fourier support in the dual cone C* if T vanishes on all Schwartz test functions
whose Fourier transform is supported outside C*.

The main theorem `fourierSupportInDualCone_of_tube_boundaryValue` shows that
the distributional boundary value of a tube-holomorphic function with tempered BV
has Fourier support in the dual cone.

## Strategy

We use the scalarized Fourier ODE method (avoiding the Fréchet calculus and
Schwartz multiplier traps):
1. Fix φ ∈ C_c^∞(ℝ^m). Define the scalar function g_φ(y) = ⟨U_y, e^{y·ξ} φ⟩
   where U_y = FT[F_y].
2. Show g_φ is constant in y using Cauchy-Riemann equations.
3. Deduce Fourier support in C* by exponential-vs-polynomial contradiction.

## References

- Vladimirov, "Methods of the Theory of Generalized Functions", §25
- Streater-Wightman, "PCT, Spin and Statistics, and All That", Theorem 2-6
-/

open scoped Classical ComplexConjugate BigOperators
open MeasureTheory SchwartzMap Complex
noncomputable section

variable {m : ℕ}

/-! ### Dual cone for flat types -/

/-- The dual cone of a set S ⊆ ℝ^m using the standard dot product on `Fin m → ℝ`.
    This is the flat-type version of `DualConeEucl`, compatible with `SchwartzMap`
    and `fourierTransformCLM` which use `Fin m → ℝ` (not `EuclideanSpace`). -/
def DualConeFlat (S : Set (Fin m → ℝ)) : Set (Fin m → ℝ) :=
  {ξ | ∀ y ∈ S, (0 : ℝ) ≤ ∑ i, y i * ξ i}

theorem mem_dualConeFlat {S : Set (Fin m → ℝ)} {ξ : Fin m → ℝ} :
    ξ ∈ DualConeFlat S ↔ ∀ y ∈ S, (0 : ℝ) ≤ ∑ i, y i * ξ i :=
  Iff.rfl

/-! ### Fourier support predicate -/

/-- A tempered distribution `T` has Fourier support in a closed set `S` if
    `T` vanishes on all Schwartz test functions whose support is disjoint from `S`.

    More precisely: for every φ ∈ S(ℝ^m) with `supp(φ) ∩ S = ∅`, we have `T(φ) = 0`.

    This is the "frequency-side" version: `T` is the Fourier transform of the
    original distribution, and `S` is the support in frequency space.
    The connection to `fourierTransformCLM` is made in individual theorems,
    not baked into the definition, to avoid `InnerProductSpace` requirements
    on `Fin m → ℝ`. -/
def HasFourierSupportIn (S : Set (Fin m → ℝ))
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) : Prop :=
  ∀ (φ : SchwartzMap (Fin m → ℝ) ℂ),
    (∀ x ∈ Function.support (φ : (Fin m → ℝ) → ℂ), x ∉ S) →
    T φ = 0

/-- A tempered distribution `T` has Fourier support in the dual cone `C*` of a set `S`. -/
def HasFourierSupportInDualCone (S : Set (Fin m → ℝ))
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) : Prop :=
  HasFourierSupportIn (DualConeFlat S) T

/-! ### Dual cone membership negation -/

/-- If ξ is not in the dual cone of S, there exists y ∈ S with negative pairing.
    This is just the negation of the universal quantifier in the definition. -/
theorem exists_neg_pairing_of_not_mem_dualConeFlat {S : Set (Fin m → ℝ)} {ξ : Fin m → ℝ}
    (hξ : ξ ∉ DualConeFlat S) :
    ∃ y ∈ S, ∑ i, y i * ξ i < 0 := by
  simp only [DualConeFlat, Set.mem_setOf_eq, not_forall, not_le] at hξ
  obtain ⟨y, hy, hlt⟩ := hξ
  exact ⟨y, hy, hlt⟩

/-! ### Basic properties -/

theorem hasFourierSupportIn_mono {S₁ S₂ : Set (Fin m → ℝ)}
    (h : S₁ ⊆ S₂)
    {T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ}
    (hT : HasFourierSupportIn S₁ T) :
    HasFourierSupportIn S₂ T :=
  fun φ hφ => hT φ (fun x hx hxS₁ => hφ x hx (h hxS₁))

/-- If T has Fourier support in S, then T agrees on test functions that coincide on S. -/
theorem hasFourierSupportIn_eqOn {S : Set (Fin m → ℝ)}
    {T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ}
    (hT : HasFourierSupportIn S T)
    {φ ψ : SchwartzMap (Fin m → ℝ) ℂ}
    (h_eq : ∀ x ∈ S, (φ : (Fin m → ℝ) → ℂ) x = (ψ : (Fin m → ℝ) → ℂ) x) :
    T φ = T ψ := by
  have hsub : T (φ - ψ) = 0 := by
    apply hT
    intro x hx hxS
    simp only [SchwartzMap.sub_apply, Function.mem_support, ne_eq] at hx
    exact hx (sub_eq_zero.mpr (h_eq x hxS))
  exact sub_eq_zero.mp (by rw [← map_sub]; exact hsub)

/-! ### Slice functionals and the scalarized ODE -/

/-- The "slice functional" at imaginary part `y ∈ C`: integration of `F(x+iy)` against
    a Schwartz test function. This is well-defined because `F` is holomorphic (hence
    continuous) on the tube interior, and Schwartz functions are integrable. -/
def sliceFunctional
    (F : (Fin m → ℂ) → ℂ)
    (y : Fin m → ℝ) (f : SchwartzMap (Fin m → ℝ) ℂ) : ℂ :=
  ∫ x : Fin m → ℝ, F (fun i => (x i : ℂ) + (y i : ℂ) * I) * f x

/-- The "scalarized ODE witness": for a compactly supported smooth φ and y ∈ C,
    this is `⟨FT[F_y], e^{y·ξ} φ⟩` (with the appropriate Fourier sign convention).

    By the Cauchy-Riemann equations on F, the Fourier-side ODE is
    `∂_{y_j} U_y = ±ξ_j U_y` (sign depends on FT convention), with solution
    `U_y = e^{±y·ξ} U_0`. The exponential factor in the test function cancels
    the one from the ODE, making this constant in y.

    For φ supported outside C*, choosing y with `y·ξ < -c < 0` on supp(φ) makes
    the witness decay exponentially as t → ∞, forcing the constant to be 0.

    **Note**: The proof of constancy requires Phase 3 Fourier infrastructure
    (FT derivative formula, distribution pairings). The plain slice functional
    `∫ F(x+ity) φ(x) dx` is NOT constant — the Fourier twist is essential. -/
def scalarizedODEWitness
    (F : (Fin m → ℂ) → ℂ)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) (y : Fin m → ℝ) (t : ℝ) : ℂ :=
  sliceFunctional F (t • y) φ

/-! ### Sub-lemmas for the main theorem -/

/-- **Step 1**: The scalarized witness `t ↦ scalarizedODEWitness F φ y t` is constant.

    Proof idea: For fixed y ∈ C and compactly supported φ, define
    `g(t) = ∫ F(x + ity) φ(x) dx`. The Cauchy-Riemann equations on F give
    `d/dt g(t) = ∫ (∑_j y_j ∂_{y_j} F)(x+ity) φ(x) dx = i ∫ (∑_j y_j ∂_{x_j} F)(x+ity) φ(x) dx`.
    Integrating by parts (φ has rapid decay), this equals
    `-i ∫ F(x+ity) (∑_j y_j ∂_{x_j} φ)(x) dx`, which involves a different test function.

    Actually, the correct scalarized approach (avoiding Fréchet traps) uses
    `g(t) = ⟨FT[F_{ty}], e^{ty·ξ} φ⟩ = ∫ F(x+ity) (FT⁻¹[e^{ty·ξ} φ])(x) dx`.
    The exponential factor absorbs the y-derivative, making dg/dt = 0 exactly. -/
theorem scalarizedODEWitness_const
    {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_cone : IsCone C)
    {F : (Fin m → ℂ) → ℂ}
    (hF_holo : DifferentiableOn ℂ F (SCV.TubeDomain C))
    (φ : SchwartzMap (Fin m → ℝ) ℂ)
    (y : Fin m → ℝ) (hy : y ∈ C)
    (t₁ t₂ : ℝ) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) :
    scalarizedODEWitness F φ y t₁ = scalarizedODEWitness F φ y t₂ := by
  sorry

/-- **Step 2**: As t → ∞ along a direction y where `y·ξ < -c < 0` on supp(φ),
    the scalarized witness decays to 0.

    Proof idea: `scalarizedODEWitness F φ y t` involves integrating F(x+ity) against φ.
    On supp(φ), F(x+ity) involves the tube function at imaginary part ty.
    The BV hypothesis gives convergence as t → 0+ (to W(φ)), but as t → ∞,
    F(x+ity) decays because the imaginary part grows into the cone interior
    where holomorphic functions on tubes are controlled. -/
theorem scalarizedODEWitness_tendsto_zero_of_outside_dualCone
    {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_ne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ}
    (hF_holo : DifferentiableOn ℂ F (SCV.TubeDomain C))
    {W : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ}
    (hF_bv : ∀ (η : Fin m → ℝ), η ∈ C →
      ∀ (φ : SchwartzMap (Fin m → ℝ) ℂ),
        Filter.Tendsto
          (fun ε : ℝ => sliceFunctional F (ε • η) φ)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (W φ)))
    (φ : SchwartzMap (Fin m → ℝ) ℂ)
    (y : Fin m → ℝ) (hy : y ∈ C) :
    Filter.Tendsto
      (fun t : ℝ => sliceFunctional F (t • y) φ)
      Filter.atTop (nhds 0) := by
  sorry

/-- **Step 3**: The BV limit connects `sliceFunctional` to `W`. -/
theorem sliceFunctional_tendsto_bv
    {C : Set (Fin m → ℝ)}
    {F : (Fin m → ℂ) → ℂ}
    {W : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ}
    (hF_bv : ∀ (η : Fin m → ℝ), η ∈ C →
      ∀ (φ : SchwartzMap (Fin m → ℝ) ℂ),
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : Fin m → ℝ,
            F (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (W φ)))
    (η : Fin m → ℝ) (hη : η ∈ C)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    Filter.Tendsto
      (fun ε : ℝ => sliceFunctional F (ε • η) φ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (W φ)) := by
  refine Filter.Tendsto.congr ?_ (hF_bv η hη φ)
  intro ε
  show ∫ x, F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * φ x =
    sliceFunctional F (ε • η) φ
  simp only [sliceFunctional]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * φ x =
    F (fun i => ↑(x i) + ↑((ε • η) i) * I) * φ x
  simp [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-! ### The main theorem -/

/-- The distributional boundary value of a holomorphic function on a tube domain
    over an open convex cone has Fourier support in the dual cone.

    This is the forward direction of the Vladimirov characterization:
    tube-holomorphic + tempered BV → Fourier support in C*.

    **Proof structure** (scalarized Fourier ODE method):
    Let φ be a Schwartz function with supp(φ) ∩ DualConeFlat(C) = ∅.
    1. By `exists_neg_pairing_of_not_mem_dualConeFlat`: ∃ y₀ ∈ C, y₀·ξ < 0 on supp(φ)
    2. The slice functional `t ↦ sliceFunctional F (t•y₀) φ` is constant
       (`scalarizedODEWitness_const`)
    3. As t → ∞, it tends to 0 (`scalarizedODEWitness_tendsto_zero_of_outside_dualCone`)
    4. As t → 0+, it tends to W(φ) (`sliceFunctional_tendsto_bv`)
    5. Therefore W(φ) = 0. -/
theorem fourierSupportInDualCone_of_tube_boundaryValue
    {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C) (hC_ne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ}
    (hF_holo : DifferentiableOn ℂ F (SCV.TubeDomain C))
    {W : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ}
    (hF_bv : ∀ (η : Fin m → ℝ), η ∈ C →
      ∀ (φ : SchwartzMap (Fin m → ℝ) ℂ),
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : Fin m → ℝ,
            F (fun i => (x i : ℂ) + (ε : ℂ) * (η i : ℂ) * I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (W φ))) :
    HasFourierSupportInDualCone C W := by
  intro φ hφ_supp
  -- φ is supported outside DualConeFlat C.
  -- We need to show W(φ) = 0.
  -- Step 1: The slice functional is constant along rays in C
  -- Step 2: It tends to 0 as t → ∞
  -- Step 3: It tends to W(φ) as t → 0+
  -- Therefore W(φ) = 0 (constant function with limits 0 and W(φ))
  sorry

end
