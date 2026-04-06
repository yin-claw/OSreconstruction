/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValues
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSemigroup

/-!
# Theorem 3 Positivity Infrastructure

This file contains the live production infrastructure for theorem 3
`bvt_W_positive`.

The endorsed route is now:
1. right-half-plane identity theorem,
2. single-component semigroup bridge on `{Re(z) > 0}`,
3. OS I Section 4.3 transport infrastructure,
4. quadratic identity on the transformed image,
5. final closure to arbitrary `BorchersSequence`.

The old same-test-function comparison route is false, even at `t = 0`, so this
file should not try to identify `WightmanInnerProduct (bvt_W ...)` with
`OSInnerProduct OS.S` on the same raw test data. The transport map is
essential.
-/

open scoped Classical NNReal
open BigOperators Finset Complex

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## Part 1: Identity theorem on the right half-plane -/

/-- Two holomorphic functions on {Re(z) > 0} that agree on (0,∞) agree everywhere.
This is the standard identity theorem for connected domains. -/
theorem identity_theorem_right_halfplane
    (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.re})
    (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.re})
    (hagree : ∀ t : ℝ, 0 < t → f (t : ℂ) = g (t : ℂ)) :
    ∀ z : ℂ, 0 < z.re → f z = g z := by
  have hU_open : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hU_preconn : IsPreconnected {z : ℂ | 0 < z.re} := by
    apply Convex.isPreconnected
    intro z hz w hw a b ha hb hab
    simp only [Set.mem_setOf_eq] at hz hw ⊢
    calc (a • z + b • w).re = a * z.re + b * w.re := by
            simp [Complex.add_re]
      _ > 0 := by
        rcases ha.lt_or_eq with ha' | ha'
        · have : b * w.re ≥ 0 := mul_nonneg hb hw.le
          have : a * z.re > 0 := mul_pos ha' hz
          linarith
        · have hab' : b = 1 := by linarith
          simp [← ha', hab', hw]
  have hf_an : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.re} := hf.analyticOnNhd hU_open
  have hg_an : AnalyticOnNhd ℂ g {z : ℂ | 0 < z.re} := hg.analyticOnNhd hU_open
  have h1_mem : (1 : ℂ) ∈ {z : ℂ | 0 < z.re} := by simp
  have hfg_an : AnalyticAt ℂ (f - g) 1 := (hf_an 1 h1_mem).sub (hg_an 1 h1_mem)
  have hfreq : ∃ᶠ z in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, (f - g) z = 0 := by
    rw [Filter.Frequently]
    intro hev
    rw [Filter.Eventually] at hev
    rw [(nhdsWithin_basis_open 1 {(1 : ℂ)}ᶜ).mem_iff] at hev
    obtain ⟨u, ⟨h1u, hu_open⟩, hus⟩ := hev
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu_open 1 h1u
    have hmem : ((1 + ε / 2 : ℝ) : ℂ) ∈ u := by
      apply hball
      rw [Metric.mem_ball, Complex.dist_eq]
      have hsub : ((1 + ε / 2 : ℝ) : ℂ) - 1 = ((ε / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hsub]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      linarith
    have hne : ((1 + ε / 2 : ℝ) : ℂ) ≠ (1 : ℂ) := by
      intro heq
      have := congr_arg Complex.re heq
      simp at this; linarith [half_pos hε]
    have hzero : (f - g) ((1 + ε / 2 : ℝ) : ℂ) = 0 := by
      simp only [Pi.sub_apply, sub_eq_zero]; exact hagree (1 + ε / 2) (by linarith)
    exact hus ⟨hmem, hne⟩ hzero
  have hev : ∀ᶠ z in nhds (1 : ℂ), (f - g) z = 0 :=
    hfg_an.frequently_zero_iff_eventually_zero.mp hfreq
  have hfg_an_on : AnalyticOnNhd ℂ (f - g) {z : ℂ | 0 < z.re} := hf_an.sub hg_an
  have heqOn : Set.EqOn (f - g) 0 {z : ℂ | 0 < z.re} :=
    hfg_an_on.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU_preconn h1_mem hev
  intro z hz
  have := heqOn hz
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact this

/-! ## Part 2: Semigroup bridge for single-component pairs -/

/-- For single-component positive-time Borchers sequences, the two holomorphic
extensions `bvt_singleSplit_xiShiftHolomorphicValue` and
`OSInnerProductTimeShiftHolomorphicValue` agree on the entire right half-plane.

Both are holomorphic on {Re(z) > 0} and both equal OS.S at real t > 0. -/
theorem bvt_xiShift_eq_osInnerProduct_holomorphicValue_single
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (z : ℂ) (hz : 0 < z.re) :
    bvt_singleSplit_xiShiftHolomorphicValue
        (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact z =
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) z := by
  apply identity_theorem_right_halfplane
  · exact differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue
      (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact
  · exact OSInnerProductTimeShiftHolomorphicValue_differentiableOn
      (d := d) OS lgc
      (PositiveTimeBorchersSequence.single n f hf_ord)
      (PositiveTimeBorchersSequence.single m g hg_ord)
  · intro t ht
    -- LHS at real t > 0: equals OS.S(n+m)(osConj f ⊗ timeShift_t g)
    rw [bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift
      (d := d) (OS := OS) (lgc := lgc) hm f hf_ord hf_compact g hg_ord hg_compact t ht]
    -- RHS at real t > 0: equals sum over k of OS.S(k+m)(...)
    rw [OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_right_single
      (d := d) (OS := OS) (lgc := lgc)
      (F := PositiveTimeBorchersSequence.single n f hf_ord)
      (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact) (t := t) ht]
    -- The sum collapses: single n f has bound = n, so only k = n contributes
    simp only [PositiveTimeBorchersSequence.single_toBorchersSequence,
      BorchersSequence.single_bound]
    rw [Finset.sum_range_succ]
    simp only [BorchersSequence.single_funcs_eq]
    have hvanish :
        ∑ k ∈ Finset.range n,
          OS.S (k + m) (ZeroDiagonalSchwartz.ofClassical
            (((BorchersSequence.single n f).funcs k).osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t g))) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hk_ne : k ≠ n := by
        have := Finset.mem_range.mp hk; omega
      rw [BorchersSequence.single_funcs_ne hk_ne]
      have : (0 : SchwartzNPoint d k).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) t g) = 0 := by
        simp [SchwartzNPoint.osConjTensorProduct, SchwartzNPoint.osConj_zero,
          SchwartzMap.tensorProduct_zero_left]
      rw [this]
      rw [ZeroDiagonalSchwartz.ofClassical_zero]
      exact (OS.E0_linear (k + m)).map_zero
    rw [hvanish, zero_add]
  · exact hz

/-! ## Part 3: Sorry 3 — Wightman positive-definiteness

CRITICAL ROUTE CORRECTION (Entry #277):

The former Package C (`hschw`) — equating `OS.S(osConj f ⊗ timeShift_t g)` with
`bvt_W(conj f ⊗ timeShift_t g)` — is MATHEMATICALLY FALSE.

Reason: `timeShiftSchwartzNPoint t` is a real time translation. On the OS/Euclidean
side it corresponds to the contraction semigroup `e^{-tH}` (decaying). On the
Wightman/Minkowski side it corresponds to the unitary group `e^{itH}` (oscillating).
The equation `e^{-tH} = e^{itH}` is false for nontrivial H.

The entire production reduction chain through `hschw` consumes a false hypothesis.

The correct route is OS I Section 4.3: construct the transport map
`u : BorchersSequence d → OSHilbertSpace OS` via Fourier-Laplace transform,
and prove `W(f* × f) = ‖u(f)‖²_H ≥ 0` directly. This does NOT go through
any time-shifted Schwinger-vs-Wightman comparison. -/

/-- The Euclidean positive-time degree-`n` test space from OS I Section 4.3.

This is the paper's `S_+(ℝ^{4n})`: Schwartz `n`-point test functions whose
topological support lies in the ordered positive-time region. -/
def EuclideanPositiveTimeComponent (d n : ℕ) [NeZero d] :=
  {f : SchwartzNPoint d n //
    tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n}

/-- An equivalent submodule presentation of the Euclidean positive-time domain.

The blueprint allows either the subtype or submodule form, as long as it
represents the same Section-4.3 Euclidean input space. This submodule surface
will be convenient when the transport map is eventually stated as a continuous
linear map. -/
def euclideanPositiveTimeSubmodule (d n : ℕ) [NeZero d] :
    Submodule ℂ (SchwartzNPoint d n) where
  carrier := {f |
    tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n}
  zero_mem' := by
    change tsupport (((0 : SchwartzNPoint d n) : NPointDomain d n → ℂ)) ⊆
      OrderedPositiveTimeRegion d n
    rw [show (((0 : SchwartzNPoint d n) : NPointDomain d n → ℂ)) = 0 by rfl]
    simpa using (empty_subset (OrderedPositiveTimeRegion d n) :
      (∅ : Set (NPointDomain d n)) ⊆ OrderedPositiveTimeRegion d n)
  add_mem' := by
    intro f g hf hg x hx
    have hx' := tsupport_add
      ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ)
      ((g : SchwartzNPoint d n) : NPointDomain d n → ℂ) hx
    exact hx'.elim (hf ·) (hg ·)
  smul_mem' := by
    intro c f hf
    exact (tsupport_smul_subset_right
      (fun _ : NPointDomain d n => c)
      ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ)).trans hf

@[simp] theorem mem_euclideanPositiveTimeSubmodule
    {n : ℕ} (f : SchwartzNPoint d n) :
    f ∈ euclideanPositiveTimeSubmodule (d := d) n ↔
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n := Iff.rfl

/-- The momentum-space positive-energy region appearing in OS I `(4.20)`.

At the current theorem-surface level we model `S(R_+^{4n})` as Schwartz
functions on `NPointDomain d n` whose support lies in the half-space
`q_k^0 ≥ 0` for every momentum variable. This matches the literal indicator
`1_{q_k^0 ≥ 0}` in the paper formula and is the first honest current-code
representation of the positive-energy codomain. -/
def PositiveEnergyRegion (d n : ℕ) [NeZero d] : Set (NPointDomain d n) :=
  {q | ∀ k : Fin n, 0 ≤ q k 0}

/-- The positive-energy Schwartz codomain from OS I Lemma 4.1, represented as a
support-restricted Schwartz subtype on momentum variables. -/
def PositiveEnergySchwartzComponent (d n : ℕ) [NeZero d] :=
  {f : SchwartzNPoint d n //
    tsupport (f : NPointDomain d n → ℂ) ⊆ PositiveEnergyRegion d n}

/-- Equivalent submodule presentation of the positive-energy Schwartz codomain. -/
def positiveEnergySchwartzSubmodule (d n : ℕ) [NeZero d] :
    Submodule ℂ (SchwartzNPoint d n) where
  carrier := {f |
    tsupport (f : NPointDomain d n → ℂ) ⊆ PositiveEnergyRegion d n}
  zero_mem' := by
    change tsupport (((0 : SchwartzNPoint d n) : NPointDomain d n → ℂ)) ⊆
      PositiveEnergyRegion d n
    rw [show (((0 : SchwartzNPoint d n) : NPointDomain d n → ℂ)) = 0 by rfl]
    simpa using (empty_subset (PositiveEnergyRegion d n) :
      (∅ : Set (NPointDomain d n)) ⊆ PositiveEnergyRegion d n)
  add_mem' := by
    intro f g hf hg x hx
    have hx' := tsupport_add
      ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ)
      ((g : SchwartzNPoint d n) : NPointDomain d n → ℂ) hx
    exact hx'.elim (hf ·) (hg ·)
  smul_mem' := by
    intro c f hf
    exact (tsupport_smul_subset_right
      (fun _ : NPointDomain d n => c)
      ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ)).trans hf

@[simp] theorem mem_positiveEnergySchwartzSubmodule
    {n : ℕ} (f : SchwartzNPoint d n) :
    f ∈ positiveEnergySchwartzSubmodule (d := d) n ↔
      tsupport (f : NPointDomain d n → ℂ) ⊆ PositiveEnergyRegion d n := Iff.rfl

/-- The sequence-level positive-energy Minkowski test space assembled from the
degreewise codomain of OS I Section 4.3. This is the honest current-code ambient
carrier for transformed-image sequences before we impose image membership. -/
structure PositiveEnergyBorchersSequence (d : ℕ) [NeZero d] where
  toBorchersSequence : BorchersSequence d
  positiveEnergy_tsupport : ∀ n,
    tsupport ((toBorchersSequence.funcs n : SchwartzNPoint d n) :
      NPointDomain d n → ℂ) ⊆ PositiveEnergyRegion d n

namespace PositiveEnergyBorchersSequence

/-- The positive-energy Borchers sequence concentrated in degree `n` with
component `f`. -/
def single (n : ℕ) (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆ PositiveEnergyRegion d n) :
    PositiveEnergyBorchersSequence d where
  toBorchersSequence := BorchersSequence.single n f
  positiveEnergy_tsupport m := by
    by_cases h : m = n
    · subst h
      simpa using hf
    · have hzero :
        (((BorchersSequence.single n f).funcs m : SchwartzNPoint d m) :
          NPointDomain d m → ℂ) = 0 := by
        simp [BorchersSequence.single, h]
      rw [hzero]
      simpa using (empty_subset (PositiveEnergyRegion d m) :
        (∅ : Set (NPointDomain d m)) ⊆ PositiveEnergyRegion d m)

instance : Coe (PositiveEnergyBorchersSequence d) (BorchersSequence d) :=
  ⟨PositiveEnergyBorchersSequence.toBorchersSequence⟩

instance : Zero (PositiveEnergyBorchersSequence d) where
  zero :=
    ⟨0, fun n => by
      simpa using (empty_subset (PositiveEnergyRegion d n) :
        (∅ : Set (NPointDomain d n)) ⊆ PositiveEnergyRegion d n)⟩

instance : Add (PositiveEnergyBorchersSequence d) where
  add F G :=
    ⟨(F : BorchersSequence d) + (G : BorchersSequence d), fun n x hx => by
      have hx' :
          x ∈ tsupport
            ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
              NPointDomain d n → ℂ) +
              (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
                NPointDomain d n → ℂ)) := by
        simpa [BorchersSequence.add_funcs] using hx
      have hx'' := (tsupport_add
        ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ))
        ((((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ))) hx'
      exact hx''.elim (fun hxF => F.positiveEnergy_tsupport n hxF)
        (fun hxG => G.positiveEnergy_tsupport n hxG)⟩

instance : Neg (PositiveEnergyBorchersSequence d) where
  neg F := ⟨-(F : BorchersSequence d), fun n => by
    rw [show (((-(F : BorchersSequence d)).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) = -(((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ) by rfl]
    rw [tsupport_neg]
    exact F.positiveEnergy_tsupport n⟩

instance : SMul ℂ (PositiveEnergyBorchersSequence d) where
  smul c F :=
    ⟨c • (F : BorchersSequence d), fun n =>
      (tsupport_smul_subset_right
        (fun _ : NPointDomain d n => c)
        ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ))).trans (F.positiveEnergy_tsupport n)⟩

instance : Sub (PositiveEnergyBorchersSequence d) where
  sub F G :=
    ⟨(F : BorchersSequence d) - (G : BorchersSequence d), fun n x hx => by
      have hx' :
          x ∈ tsupport
            ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
              NPointDomain d n → ℂ) -
              (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
                NPointDomain d n → ℂ)) := by
        simpa [BorchersSequence.sub_funcs] using hx
      have hx'' := (tsupport_sub
        ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ))
        ((((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ))) hx'
      exact hx''.elim (fun hxF => F.positiveEnergy_tsupport n hxF)
        (fun hxG => G.positiveEnergy_tsupport n hxG)⟩

@[simp] theorem zero_toBorchersSequence :
    ((0 : PositiveEnergyBorchersSequence d) : BorchersSequence d) = 0 := rfl

@[simp] theorem add_toBorchersSequence (F G : PositiveEnergyBorchersSequence d) :
    ((F + G : PositiveEnergyBorchersSequence d) : BorchersSequence d) =
      (F : BorchersSequence d) + (G : BorchersSequence d) := rfl

@[simp] theorem neg_toBorchersSequence (F : PositiveEnergyBorchersSequence d) :
    ((-F : PositiveEnergyBorchersSequence d) : BorchersSequence d) =
      - (F : BorchersSequence d) := rfl

@[simp] theorem smul_toBorchersSequence (c : ℂ) (F : PositiveEnergyBorchersSequence d) :
    ((c • F : PositiveEnergyBorchersSequence d) : BorchersSequence d) =
      c • (F : BorchersSequence d) := rfl

@[simp] theorem sub_toBorchersSequence (F G : PositiveEnergyBorchersSequence d) :
    ((F - G : PositiveEnergyBorchersSequence d) : BorchersSequence d) =
      (F : BorchersSequence d) - (G : BorchersSequence d) := rfl

@[simp] theorem single_toBorchersSequence (n : ℕ) (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆ PositiveEnergyRegion d n) :
    ((single n f hf : PositiveEnergyBorchersSequence d) : BorchersSequence d) =
      BorchersSequence.single n f := rfl

end PositiveEnergyBorchersSequence

namespace PositiveEnergySchwartzComponent

variable {n : ℕ}

/-- A positive-energy component viewed as the corresponding single positive-energy
Borchers sequence. This is the Minkowski-side ambient object that will later be
restricted to the Section 4.3 transformed image. -/
def toPositiveEnergySingle
    (f : PositiveEnergySchwartzComponent d n) :
    PositiveEnergyBorchersSequence d :=
  PositiveEnergyBorchersSequence.single n f.1 f.2

@[simp] theorem toPositiveEnergySingle_toBorchersSequence
    (f : PositiveEnergySchwartzComponent d n) :
    ((toPositiveEnergySingle (d := d) f : PositiveEnergyBorchersSequence d) :
      BorchersSequence d) = BorchersSequence.single n f.1 := by
  simp [toPositiveEnergySingle]

end PositiveEnergySchwartzComponent

namespace EuclideanPositiveTimeComponent

variable {n : ℕ}

/-- A positive-time component viewed as the corresponding single positive-time
Borchers sequence. This is the Euclidean-side input object whose image under
the eventual Section 4.3 transport map will be compared against the Wightman
quadratic form. -/
def toPositiveTimeSingle
    (f : EuclideanPositiveTimeComponent d n) :
    PositiveTimeBorchersSequence d :=
  PositiveTimeBorchersSequence.single n f.1 f.2

@[simp] theorem toPositiveTimeSingle_toBorchersSequence
    (f : EuclideanPositiveTimeComponent d n) :
    ((toPositiveTimeSingle (d := d) f : PositiveTimeBorchersSequence d) :
      BorchersSequence d) = BorchersSequence.single n f.1 := by
  simp [toPositiveTimeSingle]

end EuclideanPositiveTimeComponent

/-- The honest OS Hilbert-space vector determined by a positive-time Euclidean
Borchers sequence. Package I will later define the Minkowski-side transport map
by choosing a Euclidean preimage and landing in this existing vector. -/
noncomputable def positiveTimeBorchersVector
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    OSHilbertSpace OS :=
  (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))

@[simp] theorem positiveTimeBorchersVector_inner_eq
    (OS : OsterwalderSchraderAxioms d)
    (F G : PositiveTimeBorchersSequence d) :
    @inner ℂ (OSHilbertSpace OS) _ (positiveTimeBorchersVector (d := d) OS F)
      (positiveTimeBorchersVector (d := d) OS G) =
      PositiveTimeBorchersSequence.osInner OS F G := by
  change @inner ℂ (OSHilbertSpace OS) _
      (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
      (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS)) =
      PositiveTimeBorchersSequence.osInner OS F G
  rw [UniformSpace.Completion.inner_coe]
  simp [OSPreHilbertSpace.inner_eq]

@[simp] theorem positiveTimeBorchersVector_norm_sq_eq
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    ‖positiveTimeBorchersVector (d := d) OS F‖ ^ 2 =
      (PositiveTimeBorchersSequence.osInner OS F F).re := by
  have hnorm :
      RCLike.re
        (@inner ℂ (OSHilbertSpace OS) _ (positiveTimeBorchersVector (d := d) OS F)
          (positiveTimeBorchersVector (d := d) OS F)) =
        ‖positiveTimeBorchersVector (d := d) OS F‖ ^ 2 := by
    simpa using
      (inner_self_eq_norm_sq (𝕜 := ℂ) (positiveTimeBorchersVector (d := d) OS F))
  rw [← hnorm, positiveTimeBorchersVector_inner_eq]
  simp

theorem positiveTimeBorchersVector_self_nonneg
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    0 ≤ ‖positiveTimeBorchersVector (d := d) OS F‖ ^ 2 := by
  rw [positiveTimeBorchersVector_norm_sq_eq]
  exact PositiveTimeBorchersSequence.osInner_nonneg_self OS F

theorem positiveTimeBorchersVector_eq_of_funcs_eq
    (OS : OsterwalderSchraderAxioms d)
    {F G : PositiveTimeBorchersSequence d}
    (h : ∀ n, ((F : BorchersSequence d).funcs n) = ((G : BorchersSequence d).funcs n)) :
    positiveTimeBorchersVector (d := d) OS F =
      positiveTimeBorchersVector (d := d) OS G := by
  change (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS)) =
      (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS))
  exact congrArg (fun z : OSPreHilbertSpace OS => (z : OSHilbertSpace OS))
    (OSPreHilbertSpace.mk_eq_of_funcs_eq OS F G h)

noncomputable def euclideanPositiveTimeSingleVector
    (OS : OsterwalderSchraderAxioms d)
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n) :
    OSHilbertSpace OS :=
  positiveTimeBorchersVector (d := d) OS
    (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d) f)

@[simp] theorem euclideanPositiveTimeSingleVector_norm_sq_eq
    (OS : OsterwalderSchraderAxioms d)
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n) :
    ‖euclideanPositiveTimeSingleVector (d := d) OS f‖ ^ 2 =
      (PositiveTimeBorchersSequence.osInner OS
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d) f)
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d) f)).re := by
  simp [euclideanPositiveTimeSingleVector, positiveTimeBorchersVector_norm_sq_eq]

/-- The current-code realization of the degree-`n` Section 4.3 Fourier-Laplace
transport map.

The blueprint theorem surface is the map from `S_+(ℝ^{4n})` to the positive-energy
Schwartz codomain. In the current Lean encoding we realize both spaces using
their equivalent submodule presentations so the transport object can be stated
honestly as a continuous linear map. -/
noncomputable def os1TransportComponent
    (d n : ℕ) [NeZero d] :
    euclideanPositiveTimeSubmodule (d := d) n →L[ℂ]
      positiveEnergySchwartzSubmodule (d := d) n := by
  sorry

/-- The degree-`n` Section 4.3 transformed image in the current-code submodule
realization of the positive-energy Schwartz codomain. -/
def bvtTransportImage (d n : ℕ) [NeZero d] :
    Set (positiveEnergySchwartzSubmodule (d := d) n) :=
  Set.range (os1TransportComponent (d := d) n)

/-- Additive closure of the Section 4.3 transformed image. -/
theorem bvtTransportImage_add
    {n : ℕ}
    {f g : positiveEnergySchwartzSubmodule (d := d) n} :
    f ∈ bvtTransportImage (d := d) n →
    g ∈ bvtTransportImage (d := d) n →
    f + g ∈ bvtTransportImage (d := d) n := by
  rintro ⟨f0, rfl⟩ ⟨g0, rfl⟩
  refine ⟨f0 + g0, ?_⟩
  simp

/-- Scalar closure of the Section 4.3 transformed image. -/
theorem bvtTransportImage_smul
    {n : ℕ} {c : ℂ}
    {f : positiveEnergySchwartzSubmodule (d := d) n} :
    f ∈ bvtTransportImage (d := d) n →
    c • f ∈ bvtTransportImage (d := d) n := by
  rintro ⟨f0, rfl⟩
  refine ⟨c • f0, ?_⟩
  simp

/-- OS I Lemma 4.1 in the honest current-code submodule presentation:
the Section 4.3 transport map has dense range in the positive-energy Schwartz
codomain. -/
theorem os1TransportComponent_denseRange
    (n : ℕ) :
    DenseRange (os1TransportComponent (d := d) n) := by
  sorry

/-- The Section 4.3 transformed image is dense in the positive-energy Schwartz
codomain. -/
theorem bvtTransportImage_dense
    (n : ℕ) :
    Dense (bvtTransportImage (d := d) n) := by
  change DenseRange (os1TransportComponent (d := d) n)
  exact os1TransportComponent_denseRange (d := d) n

/-- Sorry 3: Wightman positive-definiteness for all BorchersSequence.

The correct proof route (OS I Section 4.3, equations 4.22-4.28):
1. define the positive-energy Schwartz image and the Section 4.3 transport map
   (using the honest current-code submodule model),
2. define the OS Hilbert-space vector attached to a transformed-image preimage,
3. prove the quadratic identity on that transformed-image core,
4. close positivity by density/continuity.

This requires Fourier-Laplace infrastructure connecting `bvt_F` to the
semigroup spectral measure and the corrected Section 4.3 image theorem.
See agents_chat Entries #306-#308. -/
theorem bvt_W_positive_direct
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ F : BorchersSequence d,
      (WightmanInnerProduct d (bvt_W OS lgc) F F).re ≥ 0 := by
  sorry

end
