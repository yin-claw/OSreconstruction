/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWTranslation
import OSReconstruction.ComplexLieGroups.D1OrbitSet
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.JostWitnessGeneralSigma
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Schwinger Temperedness and Zero-Diagonal Pairing

This file isolates the E0 / temperedness front of the `R -> E` direction.
It is split out of `SchwingerAxioms.lean` so the remaining honest analytic
gaps around zero-diagonal pairing and continuity do not live in a >3000-line
monolith.

The key sanity-check theorem in this file is
`kernel_mul_zeroDiagonal_integrable_of_ae_infDist_mul_pow_le_polynomial`:
if a Euclidean kernel has only finite-order coincidence singularities and at
most polynomial growth at infinity, then it pairs integrably with every
`ZeroDiagonalSchwartz` test function. This is the abstract reason the corrected
OS-I temperedness surface is `°S` rather than full Schwartz space.
-/

open scoped Classical

noncomputable section

variable {d : ℕ} [NeZero d]
/-- Wick rotation of a single point preserves each component norm:
    `‖wickRotatePoint x i‖ = ‖x i‖` for each i.
    - i = 0: `‖I * ↑(x 0)‖ = |x 0|` since `‖I‖ = 1`
    - i > 0: `‖↑(x i)‖ = |x i|` since `Complex.norm_real` -/
theorem wickRotatePoint_component_norm_eq {d : ℕ}
    (x : Fin (d + 1) → ℝ) (i : Fin (d + 1)) :
    ‖wickRotatePoint x i‖ = ‖x i‖ := by
  simp only [wickRotatePoint]; split_ifs with h
  · subst h; rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
  · rw [Complex.norm_real]

/-- The norm of a Wick-rotated Euclidean configuration is at most the original norm.

    Since `‖wickRotatePoint(x k) i‖ = ‖x k i‖` componentwise, and the Pi norm
    is the sup over all components, the Wick-rotated norm equals the original.
    We prove ≤ which suffices for the polynomial growth argument. -/
theorem wickRotate_norm_le {d n : ℕ}
    (x : Fin n → Fin (d + 1) → ℝ) :
    ‖fun k => wickRotatePoint (x k)‖ ≤ ‖x‖ := by
  -- Both norms are Pi sup norms. We bound each component.
  -- Step 1: ∀ k i, ‖wickRotatePoint(x k) i‖ ≤ ‖x‖
  have hcomp : ∀ (k : Fin n) (i : Fin (d + 1)),
      ‖wickRotatePoint (x k) i‖ ≤ ‖x‖ := by
    intro k i
    rw [wickRotatePoint_component_norm_eq]
    exact (norm_le_pi_norm (x k) i).trans (norm_le_pi_norm x k)
  -- Step 2: ∀ k, ‖wickRotatePoint(x k)‖ ≤ ‖x‖
  have hk : ∀ k : Fin n, ‖wickRotatePoint (x k)‖ ≤ ‖x‖ := by
    intro k
    -- Component bound → pi norm bound (manual, to avoid norm instance issues)
    simp only [Pi.norm_def, Pi.nnnorm_def]
    rw [NNReal.coe_le_coe]
    apply Finset.sup_le
    intro i _
    have := hcomp k i
    -- ‖wickRotatePoint(x k) i‖ ≤ ‖x‖ is in terms of ℂ norm and ℝ nested pi norm
    -- We need: ‖wickRotatePoint(x k) i‖₊ ≤ sup_j sup_μ ‖x j μ‖₊
    simp only [Pi.norm_def, Pi.nnnorm_def] at this
    exact_mod_cast this
  -- Step 3: ‖fun k => wickRotatePoint(x k)‖ ≤ ‖x‖
  simp only [Pi.norm_def, Pi.nnnorm_def]
  rw [NNReal.coe_le_coe]
  apply Finset.sup_le
  intro k _
  have := hk k
  simp only [Pi.norm_def, Pi.nnnorm_def] at this
  exact_mod_cast this

/-- **Integrability of the Wick-rotated BHW kernel on the zero-diagonal test space.**

    This is the genuine analytic input behind the literal pointwise definition
    of `constructSchwingerFunctions`. A global polynomial bound on
    `W_analytic_BHW(Wick(x))` is overstrong in general: Euclidean Schwinger kernels
    can have genuine coincidence singularities, so one must combine growth control
    at spatial infinity with local Euclidean singularity analysis near the PET
    boundary/diagonal strata.

    On the corrected OS-I surface, the only honest general pairing statement is
    for `f ∈ ZeroDiagonalSchwartz`: those test functions kill the coincidence
    singularities, so the remaining content is decay at infinity.

    Blocked by: honest Euclidean singularity control for the BHW extension near
    coincidence configurations, together with the existing forward-tube boundary-value
    input. The previous intermediate theorems
    `polynomial_growth_forwardTube_full`, `polynomial_growth_on_PET`, and
    `bhw_euclidean_polynomial_bound` were overstrong and have been removed. -/
theorem wick_rotated_kernel_mul_zeroDiagonal_integrable {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) :
    ∀ f : ZeroDiagonalSchwartz d n,
      MeasureTheory.Integrable
        (fun x : NPointDomain d n =>
          (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) * f.1 x)
        MeasureTheory.volume := by
  sorry

/-- Compact-support cancellation theorem for zero-diagonal test functions.

    This isolates the measure-theoretic heart of the corrected OS-I pairing:
    if a kernel `K` has locally bounded product with a sufficiently high power of
    `dist(x, CoincidenceLocus)`, then every compactly supported
    `f ∈ ZeroDiagonalSchwartz` pairs integrably with `K`.

    What remains open for the BHW kernel is therefore not the cancellation step,
    but the analytic theorem asserting such a weighted local bound near the
    Euclidean coincidence strata. -/
theorem kernel_mul_zeroDiagonal_integrable_of_hasCompactSupport_of_infDist_mul_pow_bounded
    {d n : ℕ} [NeZero d] (K : NPointDomain d n → ℂ)
    (hK_meas : MeasureTheory.AEStronglyMeasurable K MeasureTheory.volume)
    (f : ZeroDiagonalSchwartz d n)
    (hcompact : HasCompactSupport ((f.1 : SchwartzNPoint d n) : NPointDomain d n → ℂ))
    (m : ℕ) (hcoin : (CoincidenceLocus d n).Nonempty)
    (hbound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ tsupport (((f.1 : SchwartzNPoint d n) : NPointDomain d n → ℂ)),
        ‖K x‖ * Metric.infDist x (CoincidenceLocus d n) ^ (m + 1) ≤ C) :
    MeasureTheory.Integrable
      (fun x : NPointDomain d n => K x * (f.1 : NPointDomain d n → ℂ) x)
      MeasureTheory.volume := by
  haveI : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)) :=
    MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  haveI : (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)).HasTemperateGrowth :=
    inferInstance
  let S : Set (NPointDomain d n) :=
    tsupport (((f.1 : SchwartzNPoint d n) : NPointDomain d n → ℂ))
  have hS_compact : IsCompact S := by
    simpa [S] using hcompact.isCompact
  have hS_meas : MeasurableSet S := hS_compact.isClosed.measurableSet
  obtain ⟨Cf, hCf_nonneg, hCf⟩ :=
    VanishesToInfiniteOrderOnCoincidence.norm_le_infDist_CoincidenceLocus_pow_succ_on_isCompact
      (f := f.1) f.2 hS_compact m hcoin
  obtain ⟨CK, hCK_nonneg, hCK⟩ := hbound
  have h_on_S :
      ∀ x ∈ S,
        ‖K x * (f.1 : NPointDomain d n → ℂ) x‖ ≤ CK * Cf := by
    intro x hx
    calc
      ‖K x * (f.1 : NPointDomain d n → ℂ) x‖ =
          ‖K x‖ * ‖(f.1 : NPointDomain d n → ℂ) x‖ := norm_mul _ _
      _ ≤ ‖K x‖ * (Cf * Metric.infDist x (CoincidenceLocus d n) ^ (m + 1)) := by
          gcongr
          exact hCf x hx
      _ = Cf * (‖K x‖ * Metric.infDist x (CoincidenceLocus d n) ^ (m + 1)) := by ring
      _ ≤ Cf * CK := by
          exact mul_le_mul_of_nonneg_left (hCK x hx) hCf_nonneg
      _ = CK * Cf := by ring
  have h_int_on_S :
      MeasureTheory.IntegrableOn
        (fun x : NPointDomain d n => K x * (f.1 : NPointDomain d n → ℂ) x)
        S MeasureTheory.volume := by
    refine MeasureTheory.IntegrableOn.of_bound hS_compact.measure_lt_top
      ((hK_meas.mul (f.1.integrable.aestronglyMeasurable)).restrict)
      (CK * Cf) ?_
    exact (MeasureTheory.ae_restrict_iff' hS_meas).2 <| Filter.Eventually.of_forall h_on_S
  have h_zero_off_S :
      Set.EqOn
        (fun x : NPointDomain d n => K x * (f.1 : NPointDomain d n → ℂ) x)
        (fun _ : NPointDomain d n => (0 : ℂ))
        Sᶜ := by
    intro x hx
    have hx_support : x ∉ Function.support ((f.1 : SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
      intro hx'
      exact hx (subset_tsupport _ hx')
    have hfx : ((f.1 : SchwartzNPoint d n) : NPointDomain d n → ℂ) x = 0 := by
      by_contra hne
      exact hx_support (by simpa [Function.mem_support, hne])
    simp [hfx]
  have h_int_on_Sc :
      MeasureTheory.IntegrableOn
        (fun x : NPointDomain d n => K x * (f.1 : NPointDomain d n → ℂ) x)
        Sᶜ MeasureTheory.volume := by
    exact MeasureTheory.integrableOn_zero.congr_fun h_zero_off_S.symm hS_meas.compl
  have h_int_univ :
      MeasureTheory.IntegrableOn
        (fun x : NPointDomain d n => K x * (f.1 : NPointDomain d n → ℂ) x)
        Set.univ MeasureTheory.volume := by
    simpa [S] using h_int_on_S.union h_int_on_Sc
  exact (MeasureTheory.integrableOn_univ.mp h_int_univ)

/-- Global reduction theorem for the corrected E0 lane.

    If a measurable kernel has at most polynomial growth at infinity after being
    weighted by a sufficiently high power of `dist(x, CoincidenceLocus)`, then it
    pairs integrably with every zero-diagonal Schwartz test function. This is the
    exact combination of the two genuine ingredients now available on the test-function
    side:

    1. infinite-order vanishing at the coincidence locus, and
    2. Schwartz decay at spatial infinity.

    This is the abstract sanity check behind the corrected OS-I axiom surface:
    kernels that are analytic away from coincidence points and no worse than
    inverse-power singular along the diagonal still define the honest Euclidean
    pairing on `ZeroDiagonalSchwartz`.

    For the actual BHW kernel, the remaining gap is therefore precisely the analytic
    theorem asserting the displayed weighted polynomial bound. -/
theorem kernel_mul_zeroDiagonal_integrable_of_ae_infDist_mul_pow_le_polynomial
    {d n : ℕ} [NeZero d] (K : NPointDomain d n → ℂ)
    (hK_meas : MeasureTheory.AEStronglyMeasurable K MeasureTheory.volume)
    (f : ZeroDiagonalSchwartz d n)
    (m M : ℕ) (hcoin : (CoincidenceLocus d n).Nonempty)
    (C_bd : ℝ) (hC : 0 ≤ C_bd)
    (hK_bound : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      ‖K x‖ * Metric.infDist x (CoincidenceLocus d n) ^ (m + 1) ≤
        C_bd * (1 + ‖x‖) ^ M) :
    MeasureTheory.Integrable
      (fun x : NPointDomain d n => K x * (f.1 : NPointDomain d n → ℂ) x)
      MeasureTheory.volume := by
  haveI : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)) :=
    MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  haveI : (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)).HasTemperateGrowth :=
    inferInstance
  set D := Module.finrank ℝ (NPointDomain d n)
  have hD_lt : (D : ℝ) < ↑(D + 1) := by
    push_cast
    linarith
  have htail_int :
      MeasureTheory.Integrable
        (fun x : NPointDomain d n => (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ)))
        MeasureTheory.volume :=
    integrable_one_add_norm hD_lt
  obtain ⟨Cf, hCf_nonneg, hCf⟩ :=
    VanishesToInfiniteOrderOnCoincidence.one_add_norm_pow_mul_norm_le_infDist_CoincidenceLocus_pow_succ
      (f := f.1) f.2 (M + D + 1) m hcoin
  have hdom_int :
      MeasureTheory.Integrable
        (fun x : NPointDomain d n => C_bd * Cf * (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ)))
        MeasureTheory.volume :=
    htail_int.const_mul (C_bd * Cf)
  apply hdom_int.mono' (hK_meas.mul f.1.integrable.aestronglyMeasurable)
  filter_upwards [hK_bound] with x hx
  let δ : ℝ := Metric.infDist x (CoincidenceLocus d n)
  have hδ_nonneg : 0 ≤ δ := Metric.infDist_nonneg
  have hf_weighted :
      (1 + ‖x‖) ^ (M + D + 1) * ‖(f.1 : NPointDomain d n → ℂ) x‖ ≤
        Cf * δ ^ (m + 1) := by
    simpa [δ] using hCf x
  by_cases hδ : δ = 0
  · have hprod_nonneg :
        0 ≤ (1 + ‖x‖) ^ (M + D + 1) * ‖(f.1 : NPointDomain d n → ℂ) x‖ := by
      positivity
    have hprod_zero :
        (1 + ‖x‖) ^ (M + D + 1) * ‖(f.1 : NPointDomain d n → ℂ) x‖ = 0 :=
      le_antisymm (by simpa [hδ] using hf_weighted) hprod_nonneg
    have hpow_ne : (1 + ‖x‖) ^ (M + D + 1) ≠ 0 := by positivity
    have hnorm_zero : ‖(f.1 : NPointDomain d n → ℂ) x‖ = 0 := by
      exact (mul_eq_zero.mp hprod_zero).resolve_left hpow_ne
    have hfx : (f.1 : NPointDomain d n → ℂ) x = 0 := norm_eq_zero.mp hnorm_zero
    calc
      ‖K x * (f.1 : NPointDomain d n → ℂ) x‖ = 0 := by simp [hfx]
      _ ≤ C_bd * Cf * (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ)) := by
        have htail_nonneg : 0 ≤ (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ)) := by
          apply Real.rpow_nonneg
          positivity
        exact mul_nonneg (mul_nonneg hC hCf_nonneg) htail_nonneg
  · have hδ_pos : 0 < δ := lt_of_le_of_ne hδ_nonneg (Ne.symm hδ)
    have hδpow_pos : 0 < δ ^ (m + 1) := pow_pos hδ_pos _
    have hpow_pos : 0 < (1 + ‖x‖) ^ (M + D + 1) := by positivity
    have hK' :
        ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ M / δ ^ (m + 1) := by
      rw [le_div_iff₀ hδpow_pos]
      simpa [δ, mul_comm, mul_left_comm, mul_assoc] using hx
    have hF' :
        ‖(f.1 : NPointDomain d n → ℂ) x‖ ≤
          Cf * δ ^ (m + 1) / (1 + ‖x‖) ^ (M + D + 1) := by
      rw [le_div_iff₀ hpow_pos]
      simpa [δ, mul_comm, mul_left_comm, mul_assoc] using hf_weighted
    have hpow_split :
        (1 + ‖x‖) ^ (M + D + 1) = (1 + ‖x‖) ^ M * (1 + ‖x‖) ^ (D + 1) := by
      rw [show M + D + 1 = M + (D + 1) by omega, pow_add]
    calc
      ‖K x * (f.1 : NPointDomain d n → ℂ) x‖ =
          ‖K x‖ * ‖(f.1 : NPointDomain d n → ℂ) x‖ := norm_mul _ _
      _ ≤
          (C_bd * (1 + ‖x‖) ^ M / δ ^ (m + 1)) *
            (Cf * δ ^ (m + 1) / (1 + ‖x‖) ^ (M + D + 1)) := by
              gcongr
      _ = C_bd * Cf * ((1 + ‖x‖) ^ (D + 1))⁻¹ := by
          rw [hpow_split]
          have hδpow_ne : δ ^ (m + 1) ≠ 0 := by positivity
          have hpowM_ne : (1 + ‖x‖) ^ M ≠ 0 := by positivity
          have hpowD_ne : (1 + ‖x‖) ^ (D + 1) ≠ 0 := by positivity
          field_simp [hδpow_ne, hpowM_ne, hpowD_ne]
      _ = C_bd * Cf * (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ)) := by
          rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

/-- Helper: the integral of a polynomial-growth kernel against a Schwartz function defines
    a continuous linear functional on Schwartz space.

    The mathematical content is standard (Reed-Simon I, Theorem V.10):
    |∫ K(x)f(x)dx| ≤ C_bd · I_dim · 2^(N+dim+1) · seminorm_{N+dim+1,0}(f)
    where I_dim = ∫ (1+|x|)^{-(dim+1)} dx is finite (dim = n*(d+1)).

    The proof requires:
    - `SchwartzMap.one_add_le_sup_seminorm_apply` for decay of Schwartz functions
    - `integrable_one_add_norm` for integrability of (1+|x|)^{-r} when r > dim
    - `SchwartzMap.mkCLMtoNormedSpace` to assemble the CLM from the seminorm bound
    - `HasTemperateGrowth` instance for `volume` on `NPointDomain d n`

    Currently blocked by: `IsAddHaarMeasure` for `volume` on `Fin n → Fin (d+1) → ℝ`
    (nested Pi type). Mathlib provides the instance for single-level Pi types
    (`Fin n → ℝ`) but not for nested Pi types. The mathematical content is
    unambiguous — this is a standard functional analysis result. -/
theorem schwartz_polynomial_kernel_continuous {d n : ℕ} [NeZero d]
    (K : NPointDomain d n → ℂ)
    (hK_meas : MeasureTheory.AEStronglyMeasurable K MeasureTheory.volume)
    (C_bd : ℝ) (N : ℕ) (hC : C_bd > 0)
    (hK_bound : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N) :
    Continuous (fun f : SchwartzNPoint d n => ∫ x, K x * f x) := by
  -- Provide the IsAddHaarMeasure instance for the nested pi type (not found by inferInstance)
  haveI : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)) :=
    MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  -- Strategy: construct a CLM via mkCLMtoNormedSpace and extract continuity
  suffices h : ∃ (A : SchwartzNPoint d n →L[ℂ] ℂ), ∀ f, A f = ∫ x, K x * f x by
    obtain ⟨A, hA⟩ := h; simp_rw [← hA]; exact A.continuous
  -- Key: (1+t)^N ≤ 2^N * (1 + t^N) for t ≥ 0
  have h_binom_ineq : ∀ (t : ℝ), 0 ≤ t → (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N) := by
    intro t ht
    have h2t : 1 + t ≤ 2 * max 1 t :=
      calc 1 + t ≤ max 1 t + max 1 t := add_le_add (le_max_left _ _) (le_max_right _ _)
        _ = 2 * max 1 t := by ring
    calc (1 + t) ^ N
        ≤ (2 * max 1 t) ^ N := pow_le_pow_left₀ (by positivity) h2t N
      _ = 2 ^ N * (max 1 t) ^ N := by rw [mul_pow]
      _ ≤ 2 ^ N * (1 + t ^ N) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rcases le_total t 1 with h | h
          · rw [max_eq_left h]; simp [one_pow]; linarith [pow_nonneg ht N]
          · rw [max_eq_right h]; linarith [show (1 : ℝ) ^ N = 1 from one_pow N]
  -- Helper: K*f is integrable for any Schwartz f
  have hKf_int : ∀ f : SchwartzNPoint d n,
      MeasureTheory.Integrable (fun x => K x * f x) MeasureTheory.volume := by
    intro f
    have hf_int := f.integrable (μ := MeasureTheory.volume)
    have hf_pow_int := f.integrable_pow_mul MeasureTheory.volume N
    -- Majorant: g(x) = C_bd * 2^N * (‖f(x)‖ + ‖x‖^N * ‖f(x)‖) is integrable
    have hg_int : MeasureTheory.Integrable
        (fun x => C_bd * 2 ^ N * (‖(f : NPointDomain d n → ℂ) x‖ +
          ‖x‖ ^ N * ‖(f : NPointDomain d n → ℂ) x‖)) MeasureTheory.volume :=
      (hf_int.norm.add hf_pow_int).const_mul (C_bd * 2 ^ N)
    apply hg_int.mono' (hK_meas.mul f.integrable.aestronglyMeasurable)
    filter_upwards [hK_bound] with x hx
    simp only [Pi.mul_apply, norm_mul]
    calc ‖K x‖ * ‖(f : NPointDomain d n → ℂ) x‖
        ≤ C_bd * (1 + ‖x‖) ^ N * ‖(f : NPointDomain d n → ℂ) x‖ :=
          mul_le_mul_of_nonneg_right hx (norm_nonneg _)
      _ ≤ C_bd * (2 ^ N * (1 + ‖x‖ ^ N)) * ‖(f : NPointDomain d n → ℂ) x‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left (h_binom_ineq ‖x‖ (norm_nonneg _)) (le_of_lt hC)
      _ = C_bd * 2 ^ N * (‖(f : NPointDomain d n → ℂ) x‖ +
            ‖x‖ ^ N * ‖(f : NPointDomain d n → ℂ) x‖) := by ring
  refine ⟨SchwartzMap.mkCLMtoNormedSpace (𝕜 := ℂ) (fun f => ∫ x, K x * f x) ?_ ?_ ?_,
    fun f => rfl⟩
  · -- Additivity: ∫ K*(f+g) = ∫ K*f + ∫ K*g
    intro f g; simp only [SchwartzMap.add_apply, mul_add]
    exact MeasureTheory.integral_add (hKf_int f) (hKf_int g)
  · -- Scalar: ∫ K*(a•f) = a • ∫ K*f
    intro a f; simp only [SchwartzMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [show ∀ x : NPointDomain d n, K x * (a * f x) = a * (K x * f x) from
      fun x => by ring]
    exact MeasureTheory.integral_const_mul a _
  · -- Seminorm bound: ∃ s C, 0 ≤ C ∧ ∀ f, ‖∫ K*f‖ ≤ C * (s.sup seminormFamily) f
    -- Let D = finrank, M = N + D + 1
    set D := Module.finrank ℝ (NPointDomain d n)
    set M := N + D + 1
    -- I_D = ∫ (1+‖x‖)^(-(D+1)) < ∞
    have hD_lt : (D : ℝ) < ↑(D + 1) := by push_cast; linarith
    have hI_int : MeasureTheory.Integrable
        (fun x : NPointDomain d n => (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ)))
        MeasureTheory.volume :=
      integrable_one_add_norm hD_lt
    set I_D := ∫ x : NPointDomain d n, (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ))
    -- The constant
    set C_sem := C_bd * 2 ^ M * I_D
    refine ⟨Finset.Iic (M, 0), C_sem, ?_, ?_⟩
    · -- 0 ≤ C_sem
      apply mul_nonneg (mul_nonneg (le_of_lt hC) (by positivity))
      apply MeasureTheory.integral_nonneg
      intro x; apply Real.rpow_nonneg; linarith [norm_nonneg x]
    · -- The bound: ‖∫ K*f‖ ≤ C_sem * (s.sup seminormFamily) f
      intro f
      -- Abbreviate the seminorm
      set sem := (Finset.Iic (M, 0)).sup (schwartzSeminormFamily ℂ (NPointDomain d n) ℂ)
      -- From one_add_le_sup_seminorm_apply: (1+‖x‖)^M * ‖f(x)‖ ≤ 2^M * sem(f)
      have hsem_bound : ∀ x : NPointDomain d n,
          (1 + ‖x‖) ^ M * ‖(f : NPointDomain d n → ℂ) x‖ ≤ 2 ^ M * sem f := by
        intro x
        have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (M, 0))
          (le_refl M) (le_refl 0) f x
        rwa [norm_iteratedFDeriv_zero] at h
      -- Pointwise bound: ‖K x * f x‖ ≤ C_bd * 2^M * sem(f) * (1+‖x‖)^(-(D+1))
      have hpointwise : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
          ‖K x * (f : NPointDomain d n → ℂ) x‖ ≤
            C_bd * 2 ^ M * sem f * (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ)) := by
        filter_upwards [hK_bound] with x hx
        have h1x_pos : (0 : ℝ) < 1 + ‖x‖ := by linarith [norm_nonneg x]
        have h1xD1_pos : (0 : ℝ) < (1 + ‖x‖) ^ (D + 1) := pow_pos h1x_pos _
        -- Rewrite rpow as inverse of natural power
        rw [Real.rpow_neg (le_of_lt h1x_pos), Real.rpow_natCast]
        rw [norm_mul]
        -- ‖K x‖ * ‖f x‖ ≤ C_bd * (1+‖x‖)^N * ‖f x‖
        have step1 : ‖K x‖ * ‖(f : NPointDomain d n → ℂ) x‖ ≤
            C_bd * (1 + ‖x‖) ^ N * ‖(f : NPointDomain d n → ℂ) x‖ :=
          mul_le_mul_of_nonneg_right hx (norm_nonneg _)
        -- (1+‖x‖)^N * ‖f x‖ ≤ 2^M * sem(f) / (1+‖x‖)^(D+1)
        -- From: (1+‖x‖)^M * ‖f x‖ ≤ 2^M * sem(f) and M = N + D + 1
        have step2 : (1 + ‖x‖) ^ N * ‖(f : NPointDomain d n → ℂ) x‖ ≤
            2 ^ M * sem f * ((1 + ‖x‖) ^ (D + 1))⁻¹ := by
          rw [le_mul_inv_iff₀ h1xD1_pos]
          calc (1 + ‖x‖) ^ N * ‖(f : NPointDomain d n → ℂ) x‖ * (1 + ‖x‖) ^ (D + 1)
              = (1 + ‖x‖) ^ (N + (D + 1)) * ‖(f : NPointDomain d n → ℂ) x‖ := by
                rw [pow_add]; ring
            _ = (1 + ‖x‖) ^ M * ‖(f : NPointDomain d n → ℂ) x‖ := by
                congr 1
            _ ≤ 2 ^ M * sem f := hsem_bound x
        calc ‖K x‖ * ‖(f : NPointDomain d n → ℂ) x‖
            ≤ C_bd * (1 + ‖x‖) ^ N * ‖(f : NPointDomain d n → ℂ) x‖ := step1
          _ = C_bd * ((1 + ‖x‖) ^ N * ‖(f : NPointDomain d n → ℂ) x‖) := by ring
          _ ≤ C_bd * (2 ^ M * sem f * ((1 + ‖x‖) ^ (D + 1))⁻¹) :=
              mul_le_mul_of_nonneg_left step2 (le_of_lt hC)
          _ = C_bd * 2 ^ M * sem f * ((1 + ‖x‖) ^ (D + 1))⁻¹ := by ring
      -- Integrate the pointwise bound
      calc ‖(fun f => ∫ x, K x * f x) f‖
          = ‖∫ x, K x * (f : NPointDomain d n → ℂ) x‖ := by rfl
        _ ≤ ∫ x, ‖K x * (f : NPointDomain d n → ℂ) x‖ :=
            MeasureTheory.norm_integral_le_integral_norm _
        _ ≤ ∫ x, C_bd * 2 ^ M * sem f * (1 + ‖x‖) ^ (-(↑(D + 1) : ℝ)) :=
            MeasureTheory.integral_mono_ae (hKf_int f).norm
              (hI_int.const_mul (C_bd * 2 ^ M * sem f)) hpointwise
        _ = C_bd * 2 ^ M * sem f * I_D := by
            rw [MeasureTheory.integral_const_mul]
        _ = C_bd * 2 ^ M * I_D * sem f := by ring
        _ = C_sem * sem f := by rfl

/-- A polynomial-growth kernel is integrable against every Schwartz function. -/
theorem schwartz_polynomial_kernel_integrable {d n : ℕ} [NeZero d]
    (K : NPointDomain d n → ℂ)
    (hK_meas : MeasureTheory.AEStronglyMeasurable K MeasureTheory.volume)
    (C_bd : ℝ) (N : ℕ) (hC : C_bd > 0)
    (hK_bound : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N) :
    ∀ f : SchwartzNPoint d n,
      MeasureTheory.Integrable (fun x => K x * f x) MeasureTheory.volume := by
  -- This is the `hKf_int` argument from `schwartz_polynomial_kernel_continuous`.
  haveI : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)) :=
    MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  have h_binom_ineq : ∀ (t : ℝ), 0 ≤ t → (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N) := by
    intro t ht
    have h2t : 1 + t ≤ 2 * max 1 t :=
      calc 1 + t ≤ max 1 t + max 1 t := add_le_add (le_max_left _ _) (le_max_right _ _)
        _ = 2 * max 1 t := by ring
    calc (1 + t) ^ N
        ≤ (2 * max 1 t) ^ N := pow_le_pow_left₀ (by positivity) h2t N
      _ = 2 ^ N * (max 1 t) ^ N := by rw [mul_pow]
      _ ≤ 2 ^ N * (1 + t ^ N) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rcases le_total t 1 with h | h
          · rw [max_eq_left h]; simp [one_pow]; linarith [pow_nonneg ht N]
          · rw [max_eq_right h]; linarith [show (1 : ℝ) ^ N = 1 from one_pow N]
  intro f
  have hf_int := f.integrable (μ := MeasureTheory.volume)
  have hf_pow_int := f.integrable_pow_mul MeasureTheory.volume N
  have hg_int : MeasureTheory.Integrable
      (fun x => C_bd * 2 ^ N * (‖(f : NPointDomain d n → ℂ) x‖ +
        ‖x‖ ^ N * ‖(f : NPointDomain d n → ℂ) x‖)) MeasureTheory.volume :=
    (hf_int.norm.add hf_pow_int).const_mul (C_bd * 2 ^ N)
  apply hg_int.mono' (hK_meas.mul f.integrable.aestronglyMeasurable)
  filter_upwards [hK_bound] with x hx
  simp only [Pi.mul_apply, norm_mul]
  calc ‖K x‖ * ‖(f : NPointDomain d n → ℂ) x‖
      ≤ C_bd * (1 + ‖x‖) ^ N * ‖(f : NPointDomain d n → ℂ) x‖ :=
        mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ ≤ C_bd * (2 ^ N * (1 + ‖x‖ ^ N)) * ‖(f : NPointDomain d n → ℂ) x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (h_binom_ineq ‖x‖ (norm_nonneg _)) (le_of_lt hC)
    _ = C_bd * 2 ^ N * (‖(f : NPointDomain d n → ℂ) x‖ +
          ‖x‖ ^ N * ‖(f : NPointDomain d n → ℂ) x‖) := by ring

/-- **Continuity of Schwartz integration against a polynomially bounded kernel.**

    If K : D → ℂ is measurable and satisfies the a.e. polynomial bound
    ‖K(x)‖ ≤ C · (1 + ‖x‖)^N, then the linear functional f ↦ ∫ K(x)·f(x) dx
    is continuous on Schwartz space.

    Ref: Reed-Simon I, Theorem V.10; Hormander, Theorem 7.1.18 -/
theorem schwartz_continuous_of_polynomial_bound {d n : ℕ} [NeZero d]
    (K : NPointDomain d n → ℂ)
    (hK_meas : MeasureTheory.AEStronglyMeasurable K MeasureTheory.volume)
    (C_bd : ℝ) (N : ℕ) (hC : C_bd > 0)
    (hK_bound : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume,
      ‖K x‖ ≤ C_bd * (1 + ‖x‖) ^ N) :
    Continuous (fun f : SchwartzNPoint d n => ∫ x, K x * f x) :=
  schwartz_polynomial_kernel_continuous K hK_meas C_bd N hC hK_bound

/-- **The Wick-rotated BHW kernel is a.e. strongly measurable.**

    The function x ↦ F_ext(Wick(x)) is a.e. strongly measurable on NPointDomain.
    This follows from the fact that F_ext is holomorphic (hence continuous) on the
    permuted extended tube, Wick rotation is continuous, and a.e. Euclidean points
    lie in PET (by `ae_euclidean_points_in_permutedTube`). -/
theorem bhw_euclidean_kernel_measurable {d n : ℕ} [NeZero d]
    (Wfn : WightmanFunctions d) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : NPointDomain d n =>
        (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)))
      MeasureTheory.volume := by
  -- Strategy: F_ext is continuous on PET (holomorphic ⇒ continuous). Wick is continuous.
  -- The composition is ContinuousOn on S = Wick⁻¹(PET), which is open and has full measure.
  -- ContinuousOn.aestronglyMeasurable gives AEStronglyMeasurable on μ.restrict S.
  -- Since μ(Sᶜ) = 0, piecewise with 0 on Sᶜ gives the result.
  set F_ext := (W_analytic_BHW Wfn n).val
  set wick : NPointDomain d n → (Fin n → Fin (d + 1) → ℂ) :=
    fun x k => wickRotatePoint (x k)
  set S := wick ⁻¹' (PermutedExtendedTube d n)
  -- F_ext is continuous on PET
  have hF_cont : ContinuousOn F_ext (PermutedExtendedTube d n) :=
    (W_analytic_BHW Wfn n).property.1.continuousOn
  -- wickRotatePoint is continuous as a function Fin (d+1) → ℝ → Fin (d+1) → ℂ
  have hwickpt_cont : Continuous (wickRotatePoint (d := d)) := by
    apply continuous_pi; intro μ
    simp only [wickRotatePoint]
    split_ifs
    · exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 0))
    · exact Complex.continuous_ofReal.comp (continuous_apply μ)
  -- wick : NPointDomain d n → Fin n → Fin (d+1) → ℂ is continuous
  have hwick_cont : Continuous wick := by
    apply continuous_pi; intro k
    exact hwickpt_cont.comp (continuous_apply k)
  -- PET is open, so S is open and measurable
  have hPET_open : IsOpen (PermutedExtendedTube d n) :=
    BHW_permutedExtendedTube_eq (d := d) (n := n) ▸ BHW.isOpen_permutedExtendedTube
  have hS_open : IsOpen S := hPET_open.preimage hwick_cont
  have hS_meas : MeasurableSet S := hS_open.measurableSet
  -- F_ext ∘ wick is ContinuousOn S
  have hcomp_cont : ContinuousOn (fun x => F_ext (wick x)) S :=
    hF_cont.comp hwick_cont.continuousOn (Set.mapsTo_preimage wick _)
  -- Sᶜ has measure zero (ae_euclidean_points_in_permutedTube)
  have hSc_null : MeasureTheory.volume Sᶜ = 0 :=
    MeasureTheory.mem_ae_iff.mp ae_euclidean_points_in_permutedTube
  -- AEStronglyMeasurable on μ.restrict S
  have h_on_S : MeasureTheory.AEStronglyMeasurable
      (fun x => F_ext (wick x)) (MeasureTheory.volume.restrict S) :=
    hcomp_cont.aestronglyMeasurable hS_meas
  -- Since Sᶜ has measure zero, volume.restrict S = volume
  have hrestr : MeasureTheory.volume.restrict S = MeasureTheory.volume :=
    MeasureTheory.Measure.restrict_eq_self_of_ae_mem
      (MeasureTheory.mem_ae_iff.mpr hSc_null)
  change MeasureTheory.AEStronglyMeasurable (fun x => F_ext (wick x))
    MeasureTheory.volume
  rw [← hrestr]
  exact h_on_S

/-- On compact Euclidean regions whose Wick images stay inside PET,
    the BHW Euclidean kernel is uniformly bounded.

    This is the genuine local regularity statement available from the current
    analytic continuation infrastructure: away from the PET boundary, the kernel
    is just the restriction of a holomorphic function and therefore locally
    bounded. The remaining E0 difficulty is to control what happens near the
    Euclidean singular locus where the Wick image approaches the PET boundary,
    together with the behavior at spatial infinity. -/
private theorem bhw_euclidean_kernel_bounded_on_compact_in_permutedExtendedTube
    {d n : ℕ} [NeZero d] (Wfn : WightmanFunctions d)
    {K : Set (NPointDomain d n)} (hK : IsCompact K)
    (hPET : ∀ x ∈ K, (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n) :
    ∃ C : ℝ, ∀ x ∈ K,
      ‖(W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))‖ ≤ C := by
  set F_ext : (Fin n → Fin (d + 1) → ℂ) → ℂ := (W_analytic_BHW Wfn n).val
  set wick : NPointDomain d n → (Fin n → Fin (d + 1) → ℂ) :=
    fun x k => wickRotatePoint (x k)
  have hF_cont : ContinuousOn F_ext (PermutedExtendedTube d n) :=
    (W_analytic_BHW Wfn n).property.1.continuousOn
  have hwickpt_cont : Continuous (wickRotatePoint (d := d)) := by
    apply continuous_pi
    intro μ
    simp only [wickRotatePoint]
    split_ifs
    · exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 0))
    · exact Complex.continuous_ofReal.comp (continuous_apply μ)
  have hwick_cont : Continuous wick := by
    apply continuous_pi
    intro k
    exact hwickpt_cont.comp (continuous_apply k)
  have hkernel_cont : ContinuousOn (fun x : NPointDomain d n => ‖F_ext (wick x)‖) K := by
    refine (hF_cont.comp hwick_cont.continuousOn ?_).norm
    intro x hx
    simpa [wick] using hPET x hx
  obtain ⟨C, hC⟩ :=
    hK.exists_bound_of_continuousOn (f := fun x : NPointDomain d n => ‖F_ext (wick x)‖)
      hkernel_cont
  refine ⟨C, ?_⟩
  intro x hx
  simpa [F_ext, wick] using hC x hx

/-- Corollary of local PET boundedness on compact Euclidean regions with strictly
    increasing positive time coordinates. -/
private theorem bhw_euclidean_kernel_bounded_on_compact_positiveOrdered
    {d n : ℕ} [NeZero d] (Wfn : WightmanFunctions d)
    {K : Set (NPointDomain d n)} (hK : IsCompact K)
    (hord : ∀ x ∈ K, ∀ k j : Fin n, k < j → x k 0 < x j 0)
    (hpos : ∀ x ∈ K, ∀ k : Fin n, 0 < x k 0) :
    ∃ C : ℝ, ∀ x ∈ K,
      ‖(W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))‖ ≤ C := by
  refine bhw_euclidean_kernel_bounded_on_compact_in_permutedExtendedTube
    (Wfn := Wfn) hK ?_
  intro x hx
  have hFT : (fun k => wickRotatePoint (x k)) ∈ ForwardTube d n :=
      euclidean_ordered_in_forwardTube x (hord x hx) (hpos x hx)
  have hFT_BHW : (fun k => wickRotatePoint (x k)) ∈ BHW.ForwardTube d n := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using hFT
  have hPET_BHW : (fun k => wickRotatePoint (x k)) ∈ BHW.PermutedExtendedTube d n :=
    BHW.forwardTube_subset_permutedExtendedTube hFT_BHW
  simpa [BHW_permutedExtendedTube_eq (d := d) (n := n)] using hPET_BHW

/-- On compact Euclidean regions whose points stay pairwise distinct and lie in a
    common open half-space, the BHW Euclidean kernel is uniformly bounded.

    This packages the pointwise geometry now available in
    `euclidean_commonHalfSpace_in_permutedTube`: after a suitable Euclidean
    rotation, such configurations have distinct positive times, hence lie in PET. -/
private theorem bhw_euclidean_kernel_bounded_on_compact_commonHalfSpace
    {d n : ℕ} [NeZero d] (Wfn : WightmanFunctions d)
    {K : Set (NPointDomain d n)} (hK : IsCompact K)
    (hOmega : ∀ x ∈ K, x ∈ OmegaRegion d n)
    (hhs : ∃ v : Fin (d + 1) → ℝ, ∀ x ∈ K, ∀ i : Fin n, ∑ μ, v μ * x i μ > 0) :
    ∃ C : ℝ, ∀ x ∈ K,
      ‖(W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))‖ ≤ C := by
  rcases hhs with ⟨v, hv⟩
  refine bhw_euclidean_kernel_bounded_on_compact_in_permutedExtendedTube
    (Wfn := Wfn) hK ?_
  intro x hx
  exact euclidean_commonHalfSpace_in_permutedTube (d := d) x (hOmega x hx) ⟨v, hv x hx⟩

/-- The Wick-rotated BHW kernel is integrable against any compactly supported
    Schwartz function whose topological support stays inside PET.

    This isolates the genuinely easy half of the Euclidean pairing problem:
    away from the PET boundary/diagonal singular strata, the kernel is continuous
    and therefore bounded on the compact support. The unresolved part of
    `wick_rotated_kernel_mul_zeroDiagonal_integrable` is exactly what happens
    when the support approaches the coincidence strata. -/
theorem wick_rotated_kernel_mul_schwartz_integrable_of_hasCompactSupport_of_tsupport_in_permutedTube
    {d n : ℕ} [NeZero d] (Wfn : WightmanFunctions d) (f : SchwartzNPoint d n)
    (hcompact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hPET : ∀ x ∈ tsupport (f : NPointDomain d n → ℂ),
      (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n) :
    MeasureTheory.Integrable
      (fun x : NPointDomain d n =>
        (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) * f x)
      MeasureTheory.volume := by
  haveI : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)) :=
    MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  haveI : (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)).HasTemperateGrowth :=
    inferInstance
  let K : NPointDomain d n → ℂ :=
    fun x => (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))
  have hK_meas :
      MeasureTheory.AEStronglyMeasurable K MeasureTheory.volume :=
    bhw_euclidean_kernel_measurable (Wfn := Wfn)
  obtain ⟨C, hC⟩ :=
    bhw_euclidean_kernel_bounded_on_compact_in_permutedExtendedTube
      (Wfn := Wfn) hcompact.isCompact hPET
  let C' : ℝ := max C 0
  have hf_int : MeasureTheory.Integrable (fun x : NPointDomain d n => f x) MeasureTheory.volume :=
    f.integrable (μ := MeasureTheory.volume)
  have hdom_int : MeasureTheory.Integrable (fun x : NPointDomain d n => C' * ‖f x‖)
      MeasureTheory.volume :=
    hf_int.norm.const_mul C'
  apply hdom_int.mono' (hK_meas.mul hf_int.aestronglyMeasurable)
  filter_upwards with x
  by_cases hx : x ∈ tsupport (f : NPointDomain d n → ℂ)
  · have hKx : ‖K x‖ ≤ C' := (hC x hx).trans (le_max_left _ _)
    calc
      ‖K x * f x‖ = ‖K x‖ * ‖f x‖ := norm_mul _ _
      _ ≤ C' * ‖f x‖ := mul_le_mul_of_nonneg_right hKx (norm_nonneg _)
  · have hx_support : x ∉ Function.support (f : NPointDomain d n → ℂ) := by
      intro hx'
      exact hx (subset_tsupport _ hx')
    have hfx : f x = 0 := by
      by_contra hne
      exact hx_support (by simpa [Function.mem_support, hne])
    calc
      ‖K x * f x‖ = 0 := by simp [hfx]
      _ ≤ C' * ‖f x‖ := by
        exact mul_nonneg (le_max_right _ _) (norm_nonneg _)

/-- The Wick-rotated BHW kernel is integrable against compactly supported
    Schwartz functions supported on configurations that stay pairwise distinct
    inside a common open half-space.

    This is the intrinsic Euclidean version of the previous PET-support lemma:
    the support hypothesis is stated on real configurations rather than directly
    on their Wick images. The common-half-space geometry is exactly what lets the
    Wick-rotated support sit inside PET pointwise. -/
theorem wick_rotated_kernel_mul_schwartz_integrable_of_hasCompactSupport_of_tsupport_in_commonHalfSpace
    {d n : ℕ} [NeZero d] (Wfn : WightmanFunctions d) (f : SchwartzNPoint d n)
    (hcompact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hOmega : tsupport (f : NPointDomain d n → ℂ) ⊆ OmegaRegion d n)
    (hhs : ∃ v : Fin (d + 1) → ℝ,
      ∀ x ∈ tsupport (f : NPointDomain d n → ℂ), ∀ i : Fin n, ∑ μ, v μ * x i μ > 0) :
    MeasureTheory.Integrable
      (fun x : NPointDomain d n =>
        (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) * f x)
      MeasureTheory.volume := by
  let K : NPointDomain d n → ℂ :=
    fun x => (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))
  have hK_meas :
      MeasureTheory.AEStronglyMeasurable K MeasureTheory.volume :=
    bhw_euclidean_kernel_measurable (Wfn := Wfn)
  obtain ⟨C, hC⟩ :=
    bhw_euclidean_kernel_bounded_on_compact_commonHalfSpace
      (Wfn := Wfn) hcompact.isCompact
      (fun x hx => hOmega hx)
      hhs
  haveI : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)) :=
    MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  haveI : (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)).HasTemperateGrowth :=
    inferInstance
  let C' : ℝ := max C 0
  have hf_int : MeasureTheory.Integrable (fun x : NPointDomain d n => f x) MeasureTheory.volume :=
    f.integrable (μ := MeasureTheory.volume)
  have hdom_int : MeasureTheory.Integrable (fun x : NPointDomain d n => C' * ‖f x‖)
      MeasureTheory.volume :=
    hf_int.norm.const_mul C'
  apply hdom_int.mono' (hK_meas.mul hf_int.aestronglyMeasurable)
  filter_upwards with x
  by_cases hx : x ∈ tsupport (f : NPointDomain d n → ℂ)
  · have hKx : ‖K x‖ ≤ C' := (hC x hx).trans (le_max_left _ _)
    calc
      ‖K x * f x‖ = ‖K x‖ * ‖f x‖ := norm_mul _ _
      _ ≤ C' * ‖f x‖ := mul_le_mul_of_nonneg_right hKx (norm_nonneg _)
  · have hx_support : x ∉ Function.support (f : NPointDomain d n → ℂ) := by
      intro hx'
      exact hx (subset_tsupport _ hx')
    have hfx : f x = 0 := by
      by_contra hne
      exact hx_support (by simpa [Function.mem_support, hne])
    calc
      ‖K x * f x‖ = 0 := by simp [hfx]
      _ ≤ C' * ‖f x‖ := by
        exact mul_nonneg (le_max_right _ _) (norm_nonneg _)

omit [NeZero d] in
private def translateNPointDomain (a : SpacetimeDim d) {n : ℕ} :
    NPointDomain d n → NPointDomain d n :=
  fun x i => x i - a

omit [NeZero d] in
private theorem translateNPointDomain_antilipschitz (a : SpacetimeDim d) {n : ℕ} :
    AntilipschitzWith 1 (translateNPointDomain (d := d) (n := n) a) := by
  refine AntilipschitzWith.of_le_mul_dist ?_
  intro x y
  have hsub :
      x - y = translateNPointDomain (d := d) (n := n) a x -
        translateNPointDomain (d := d) (n := n) a y := by
    ext i μ
    simp [translateNPointDomain, sub_eq_add_neg]
    abel_nf
  simpa [one_mul, dist_eq_norm] using le_of_eq (congrArg norm hsub)

omit [NeZero d] in
private theorem translateNPointDomain_hasTemperateGrowth (a : SpacetimeDim d) {n : ℕ} :
    Function.HasTemperateGrowth (translateNPointDomain (d := d) (n := n) a) := by
  let c : NPointDomain d n := fun _ => -a
  have hconst : Function.HasTemperateGrowth (fun _ : NPointDomain d n => c) :=
    Function.HasTemperateGrowth.const c
  have hid : Function.HasTemperateGrowth (fun x : NPointDomain d n => x) := by
    simpa using (ContinuousLinearMap.id ℝ (NPointDomain d n)).hasTemperateGrowth
  simpa [translateNPointDomain, c, sub_eq_add_neg, Pi.add_apply] using hid.add hconst

/-- Compactly supported coincidence-free Schwartz functions pair integrably with
    the Wick-rotated BHW kernel.

    This removes the remaining *local* singularity issue on compact sets away from
    the coincidence locus. The proof shifts the compact support far enough in
    Euclidean time so that every translated configuration lies in a common open
    half-space, applies the previous common-half-space integrability theorem
    there, and transports integrability back using measure-preserving translation
    plus the a.e. Euclidean translation invariance of the BHW kernel. -/
theorem wick_rotated_kernel_mul_schwartz_integrable_of_hasCompactSupport_of_tsupport_in_OmegaRegion
    {d n : ℕ} [NeZero d] (Wfn : WightmanFunctions d) (f : SchwartzNPoint d n)
    (hcompact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hOmega : tsupport (f : NPointDomain d n → ℂ) ⊆ OmegaRegion d n) :
    MeasureTheory.Integrable
      (fun x : NPointDomain d n =>
        (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k)) * f x)
      MeasureTheory.volume := by
  let K : NPointDomain d n → ℂ :=
    fun x => (W_analytic_BHW Wfn n).val (fun k => wickRotatePoint (x k))
  have hK_meas :
      MeasureTheory.AEStronglyMeasurable K MeasureTheory.volume :=
    bhw_euclidean_kernel_measurable (Wfn := Wfn)
  haveI : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)) :=
    MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite
  haveI : (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)).HasTemperateGrowth :=
    inferInstance
  obtain ⟨C, hC⟩ :=
    hcompact.isCompact.exists_bound_of_continuousOn
      (f := fun x : NPointDomain d n => ‖x‖) continuous_norm.continuousOn
  let T : ℝ := max C 0 + 1
  let a : SpacetimeDim d := fun μ => if μ = 0 then T else 0
  let aN : NPointDomain d n := fun _ => a
  let τ : NPointDomain d n → NPointDomain d n := translateNPointDomain (d := d) (n := n) a
  let g : SchwartzNPoint d n :=
    SchwartzMap.compCLMOfAntilipschitz ℂ
      (translateNPointDomain_hasTemperateGrowth (d := d) (n := n) a)
      (translateNPointDomain_antilipschitz (d := d) (n := n) a) f
  have hg_apply : ∀ x : NPointDomain d n, g x = f (τ x) := by
    intro x
    simp [g, τ]
  have hg_compact : HasCompactSupport (g : NPointDomain d n → ℂ) := by
    simpa [g, τ, translateNPointDomain, sub_eq_add_neg]
      using hcompact.comp_homeomorph (Homeomorph.addRight (-aN))
  have hτ_tsupport :
      tsupport (g : NPointDomain d n → ℂ) =
        (Homeomorph.addRight (-aN)) ⁻¹' tsupport (f : NPointDomain d n → ℂ) := by
    simpa [g, τ, translateNPointDomain, aN, sub_eq_add_neg] using
      (tsupport_comp_eq_preimage (g := (f : NPointDomain d n → ℂ))
        (Homeomorph.addRight (-aN)))
  have hτ_mem : ∀ x ∈ tsupport (g : NPointDomain d n → ℂ),
      τ x ∈ tsupport (f : NPointDomain d n → ℂ) := by
    intro x hx
    simpa [hτ_tsupport, τ, translateNPointDomain, aN, sub_eq_add_neg] using hx
  have hg_Omega : tsupport (g : NPointDomain d n → ℂ) ⊆ OmegaRegion d n := by
    intro x hx i j hij
    have hx' := hτ_mem x hx
    have hdist := hOmega hx' i j hij
    intro hEq
    apply hdist
    simpa [τ, translateNPointDomain, hEq]
  have hT_pos : 0 < T := by
    have : 0 ≤ max C 0 := le_max_right _ _
    linarith
  have hg_hs :
      ∃ v : Fin (d + 1) → ℝ,
        ∀ x ∈ tsupport (g : NPointDomain d n → ℂ), ∀ i : Fin n, ∑ μ, v μ * x i μ > 0 := by
    refine ⟨fun μ => if μ = 0 then (1 : ℝ) else 0, ?_⟩
    intro x hx i
    have hx' := hτ_mem x hx
    have hτ_norm : ‖τ x‖ ≤ C := by
      simpa using hC (τ x) hx'
    have hcoord_norm : ‖(τ x i) 0‖ ≤ ‖τ x‖ := by
      exact (norm_le_pi_norm (τ x i) 0).trans (norm_le_pi_norm (τ x) i)
    have hcoord_lower : -‖τ x‖ ≤ (τ x i) 0 := by
      calc
        -‖τ x‖ ≤ -‖(τ x i) 0‖ := by linarith
        _ ≤ (τ x i) 0 := by
          simpa [Real.norm_eq_abs] using neg_abs_le ((τ x i) 0)
    have htime : 0 < x i 0 := by
      have hx_eq : x i 0 = (τ x i) 0 + T := by
        simp [τ, translateNPointDomain, a, T]
      rw [hx_eq]
      have hmax : C ≤ max C 0 := le_max_left _ _
      linarith
    simpa using htime
  have hg_int :=
    wick_rotated_kernel_mul_schwartz_integrable_of_hasCompactSupport_of_tsupport_in_commonHalfSpace
      (Wfn := Wfn) g hg_compact hg_Omega hg_hs
  have hg_add : ∀ x : NPointDomain d n, g (x + aN) = f x := by
    intro x
    rw [hg_apply]
    congr 1
    ext i μ
    simp [τ, translateNPointDomain, aN, sub_eq_add_neg]
  have hg_shift_int :
      MeasureTheory.Integrable
        (fun x : NPointDomain d n => K (x + aN) * f x) MeasureTheory.volume := by
    have hEq :
        (fun x : NPointDomain d n => K (x + aN) * f x) =
          (fun x : NPointDomain d n => (K x * g x)) ∘ fun x => x + aN := by
      funext x
      simp [hg_add]
    rw [hEq]
    exact hg_int.comp_add_right aN
  have hf_int : MeasureTheory.Integrable (fun x : NPointDomain d n => f x) MeasureTheory.volume :=
    f.integrable (μ := MeasureTheory.volume)
  let P : NPointDomain d n → Prop :=
    fun x => (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n
  have hP_ae : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume, P x :=
    ae_euclidean_points_in_permutedTube
  have hP_shift_ae : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume, P (x + aN) := by
    exact (MeasureTheory.eventually_add_right_iff
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (NPointDomain d n)))
      (t := aN) (p := P)).2 hP_ae
  have hK_ae : ∀ᵐ (x : NPointDomain d n) ∂MeasureTheory.volume, K x = K (x + aN) := by
    filter_upwards [hP_ae, hP_shift_ae] with x hx hx_shift
    have hx' : (fun k => wickRotatePoint (x k)) ∈ PermutedExtendedTube d n := by
      simpa [P] using hx
    have hx_shift0 : (fun k => wickRotatePoint (x k + a)) ∈ PermutedExtendedTube d n := by
      simpa [P, aN] using hx_shift
    have hwick_add :
        (fun k => wickRotatePoint (x k + a)) =
          (fun k μ => wickRotatePoint (x k) μ + wickRotatePoint a μ) := by
      ext k μ
      by_cases hμ : μ = 0
      · subst hμ
        simp [wickRotatePoint, mul_add]
      · simp [wickRotatePoint, hμ]
    have hx_shift' :
        (fun k μ => wickRotatePoint (x k) μ + wickRotatePoint a μ) ∈
          PermutedExtendedTube d n := by
      simpa [hwick_add] using hx_shift0
    simpa [K, aN, hwick_add] using
      (bhw_translation_invariant Wfn (wickRotatePoint a)
        (fun k => wickRotatePoint (x k)) hx' hx_shift').symm
  exact hg_shift_int.congr <| hK_ae.mono fun x hx => by
    simpa [K] using congrArg (fun z : ℂ => z * f x) hx.symm

/-- The constructed Schwinger functional is continuous on the OS-I
    zero-diagonal test space.

    This is the honest E0 surface currently needed in `OsterwalderSchraderAxioms`.
    Unlike the deleted full-Schwartz theorem fronts, this matches the corrected
    OS-I axiom surface after the zero-diagonal repair. -/
theorem constructedSchwinger_tempered_zeroDiagonal (Wfn : WightmanFunctions d) (n : ℕ) :
    Continuous (constructSchwingerFunctions Wfn n) := by
  sorry
