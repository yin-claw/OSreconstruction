import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesBase
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanPositivity
import OSReconstruction.Wightman.Reconstruction.WickRotation.EuclideanPositiveTime
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43Codomain

/-!
# Theorem 3 On-Image Positivity Infrastructure

This file records the OS-route Stage-5 transformed-image package and the
boundary-vanishing obstruction discovered on the current branch.

Important current-graph note:
- this file imports `OSToWightmanPositivity.lean`, which packages the
  one-variable / matrix-element Stage-5 inputs it consumes;
- `OSToWightmanPositivity.lean` now depends only on the boundary-value base
  layer rather than the monolithic `OSToWightmanBoundaryValues.lean`;
- this removes the previous cycle obstruction and makes the on-image Stage-5
  package available for upstream import exposure;
- the remaining `bvt_W_positive` seam is mathematical, not graph-theoretic:
  the missing step is still the prior VEV / boundary-value identification into
  the boundary-vanishing supplier class.
-/

open scoped Topology Classical NNReal
open BigOperators Finset Complex

noncomputable section

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The degree-`n` Section 4.3 transformed image. -/
def bvtTransportImage (d n : ℕ) [NeZero d] :
    Set (Section43PositiveEnergyComponent (d := d) n) :=
  Set.range (os1TransportComponent d n)

/-- Additive closure of the transformed image. -/
theorem bvtTransportImage_add
    {n : ℕ} {f g : Section43PositiveEnergyComponent (d := d) n}
    (hf : f ∈ bvtTransportImage (d := d) n)
    (hg : g ∈ bvtTransportImage (d := d) n) :
    f + g ∈ bvtTransportImage (d := d) n := by
  rcases hf with ⟨f₀, rfl⟩
  rcases hg with ⟨g₀, rfl⟩
  exact ⟨f₀ + g₀, by simp [bvtTransportImage]⟩

/-- Scalar closure of the transformed image. -/
theorem bvtTransportImage_smul
    {n : ℕ} {c : ℂ} {f : Section43PositiveEnergyComponent (d := d) n}
    (hf : f ∈ bvtTransportImage (d := d) n) :
    c • f ∈ bvtTransportImage (d := d) n := by
  rcases hf with ⟨f₀, rfl⟩
  exact ⟨c • f₀, by simp [bvtTransportImage]⟩

/-- Finite Borchers data whose every component lies in the Section 4.3
transformed image. This is the honest current-code carrier for the later
on-image transport and Eq. `(4.28)` stages. -/
structure BvtTransportImageSequence (d : ℕ) [NeZero d] where
  toBorchers : BorchersSequence d
  image_mem : ∀ n,
    section43PositiveEnergyQuotientMap (d := d) n (toBorchers.funcs n) ∈
      bvtTransportImage (d := d) n

/-- Constructor-side packaging of the exact data needed to build a transformed-
image Borchers sequence.

This is the smallest current source-backed ingress below the later fixed-
surrogate consumer block: to place an ambient Borchers sequence on the
`BvtTransportImageSequence` side, it is enough to supply degreewise positive-
time preimages whose Section-4.3 transports match the ambient components in the
quotient codomain. No stronger wrapper, such as a full
`PositiveTimeBorchersSequence`, is required at this seam. -/
noncomputable def BvtTransportImageSequence.ofPreimageFamily
    (F : BorchersSequence d)
    (f : ∀ n, euclideanPositiveTimeSubmodule (d := d) n)
    (hf : ∀ n,
      os1TransportComponent d n (f n) =
        section43PositiveEnergyQuotientMap (d := d) n (F.funcs n)) :
    BvtTransportImageSequence d where
  toBorchers := F
  image_mem := fun n => by
    refine ⟨f n, ?_⟩
    simpa [bvtTransportImage] using hf n

/-- Exact degreewise ingress criterion for one ambient Section-4.3 component:
an ambient Schwartz representative lies in the transformed image precisely when
it admits a positive-time Euclidean preimage with the required transport
equality. This is the smallest current fixed-component witness surface below
`BvtTransportImageSequence.ofPreimageFamily`. -/
theorem section43PositiveEnergyQuotientMap_mem_bvtTransportImage_iff_exists_preimage
    {n : ℕ} (φ : SchwartzNPoint d n) :
    section43PositiveEnergyQuotientMap (d := d) n φ ∈ bvtTransportImage (d := d) n ↔
      ∃ f : euclideanPositiveTimeSubmodule (d := d) n,
        os1TransportComponent d n f =
          section43PositiveEnergyQuotientMap (d := d) n φ := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, hf⟩

/-- Degreewise witness extractor on the transformed-image carrier. For each
component of an existing `BvtTransportImageSequence`, the constructor-side
image hypothesis yields an explicit positive-time preimage and transport
equality. -/
theorem BvtTransportImageSequence.exists_component_preimage
    (F : BvtTransportImageSequence d) (n : ℕ) :
    ∃ f : euclideanPositiveTimeSubmodule (d := d) n,
      os1TransportComponent d n f =
        section43PositiveEnergyQuotientMap (d := d) n (F.toBorchers.funcs n) := by
  simpa using
    (section43PositiveEnergyQuotientMap_mem_bvtTransportImage_iff_exists_preimage
      (d := d) (n := n) (φ := F.toBorchers.funcs n)).mp (F.image_mem n)

@[simp] theorem BvtTransportImageSequence.ofPreimageFamily_toBorchers
    (F : BorchersSequence d)
    (f : ∀ n, euclideanPositiveTimeSubmodule (d := d) n)
    (hf : ∀ n,
      os1TransportComponent d n (f n) =
        section43PositiveEnergyQuotientMap (d := d) n (F.funcs n)) :
    (BvtTransportImageSequence.ofPreimageFamily (d := d) F f hf).toBorchers = F := rfl

/-- Constructor-side partial supplier ingress for the fixed-surrogate on-image
seam.

If an ambient approximating family already comes with explicit degreewise
positive-time preimages, then the transformed-image family `G` together with
its boundedness and componentwise-convergence fields is formal. This isolates
the remaining upstream seam precisely: after this theorem, the only missing
payload for the full fixed-surrogate supplier is the extra compact-support,
degree-`0`, and positive-real-time data on that explicit preimage family. -/
theorem exists_bounded_componentwise_onImage_family_of_preimageFamilies
    (F₀ : BorchersSequence d) {m : ℕ}
    (F : ℕ → BorchersSequence d)
    (hF : ∀ N, (F N).bound ≤ m)
    (hcomp : ∀ n, n ≤ m →
      Filter.Tendsto
        (fun N : ℕ => ((F N).funcs n : SchwartzNPoint d n))
        Filter.atTop
        (nhds (F₀.funcs n)))
    (f : ∀ N n, euclideanPositiveTimeSubmodule (d := d) n)
    (hf : ∀ N n,
      os1TransportComponent d n (f N n) =
        section43PositiveEnergyQuotientMap (d := d) n ((F N).funcs n)) :
    ∃ G : ℕ → BvtTransportImageSequence d,
      (∀ N, (G N).toBorchers.bound ≤ m) ∧
      (∀ n, n ≤ m →
        Filter.Tendsto
          (fun N : ℕ => (((G N).toBorchers.funcs n : SchwartzNPoint d n)))
          Filter.atTop
          (nhds (F₀.funcs n))) := by
  refine ⟨fun N =>
    BvtTransportImageSequence.ofPreimageFamily (d := d) (F N) (f N) (hf N), ?_, ?_⟩
  · intro N
    simpa using hF N
  · intro n hn
    simpa [BvtTransportImageSequence.ofPreimageFamily_toBorchers] using hcomp n hn

/-- Exact fixed-surrogate ingress up to, but not including, the positive-real
time comparison field `hreal`.

Starting from an explicit ambient approximating family together with degreewise
positive-time preimages, this packages the transformed-image family `G` and all
currently source-backed supplier fields that are strictly earlier than `hreal`:
boundedness, componentwise convergence to the fixed surrogate, preimage-side
compact support, ambient compact support, and family-level degree-`0` vanishing.

This is the earliest honest upstream theorem-sized pass available from the
current graph for the fixed-surrogate/on-image seam. The remaining missing
field is exactly the positive-real-time identification family `hreal`. -/
theorem exists_bounded_componentwise_onImage_supplier_data_of_preimageFamilies
    (F₀ : BorchersSequence d) {m : ℕ}
    (F : ℕ → BorchersSequence d)
    (hF : ∀ N, (F N).bound ≤ m)
    (hcomp : ∀ n, n ≤ m →
      Filter.Tendsto
        (fun N : ℕ => ((F N).funcs n : SchwartzNPoint d n))
        Filter.atTop
        (nhds (F₀.funcs n)))
    (f : ∀ N n, euclideanPositiveTimeSubmodule (d := d) n)
    (hf : ∀ N n,
      os1TransportComponent d n (f N n) =
        section43PositiveEnergyQuotientMap (d := d) n ((F N).funcs n))
    (hprecompact : ∀ N n, n ≤ (F N).bound →
      HasCompactSupport
        ((((f N n : euclideanPositiveTimeSubmodule (d := d) n) :
            SchwartzNPoint d n) : NPointDomain d n → ℂ)))
    (hambientCompact : ∀ N n, n ≤ (F N).bound →
      HasCompactSupport
        ((((F N).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ)))
    (hF0 : ∀ N, ((F N).funcs 0 : SchwartzNPoint d 0) = 0) :
    ∃ G : ℕ → BvtTransportImageSequence d,
      (∀ N, (G N).toBorchers.bound ≤ m) ∧
      (∀ n, n ≤ m →
        Filter.Tendsto
          (fun N : ℕ => (((G N).toBorchers.funcs n : SchwartzNPoint d n)))
          Filter.atTop
          (nhds (F₀.funcs n))) ∧
      (∀ N n, n ≤ (G N).toBorchers.bound →
        HasCompactSupport
          ((((f N n :
                euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n) : NPointDomain d n → ℂ))) ∧
      (∀ N n, n ≤ (G N).toBorchers.bound →
        HasCompactSupport
          ((((G N).toBorchers.funcs n : SchwartzNPoint d n) :
              NPointDomain d n → ℂ))) ∧
      (∀ N, ((G N).toBorchers.funcs 0 : SchwartzNPoint d 0) = 0) := by
  refine ⟨fun N =>
    BvtTransportImageSequence.ofPreimageFamily (d := d) (F N) (f N) (hf N), ?_, ?_, ?_, ?_, ?_⟩
  · intro N
    simpa using hF N
  · intro n hn
    simpa [BvtTransportImageSequence.ofPreimageFamily_toBorchers] using hcomp n hn
  · intro N n hn
    simpa using hprecompact N n (by simpa using hn)
  · intro N n hn
    simpa [BvtTransportImageSequence.ofPreimageFamily_toBorchers] using
      hambientCompact N n (by simpa using hn)
  · intro N
    simpa [BvtTransportImageSequence.ofPreimageFamily_toBorchers] using hF0 N

instance : Add (BvtTransportImageSequence d) where
  add F G :=
    { toBorchers := F.toBorchers + G.toBorchers
      image_mem := fun n => by
        have hsum :=
            bvtTransportImage_add (d := d)
              (hf := F.image_mem n) (hg := G.image_mem n)
        simpa [BorchersSequence.add_funcs, map_add] using hsum }

instance : SMul ℂ (BvtTransportImageSequence d) where
  smul c F :=
    { toBorchers := c • F.toBorchers
      image_mem := fun n => by
        have hsmul :=
            bvtTransportImage_smul (d := d) (c := c) (hf := F.image_mem n)
        simpa [BorchersSequence.smul_funcs] using hsmul }

@[simp] theorem add_toBorchers
    (F G : BvtTransportImageSequence d) :
    (F + G).toBorchers = F.toBorchers + G.toBorchers := rfl

@[simp] theorem smul_toBorchers
    (c : ℂ) (F : BvtTransportImageSequence d) :
    (c • F).toBorchers = c • F.toBorchers := rfl

/-- Positive-degree components on the transformed-image carrier already vanish
at the boundary point `0`. This is the raw-function shadow of the quotient-side
obstruction `not_denseRange_os1TransportComponent_succ`. -/
/- Earliest downstream codomain seam:
this obstruction cluster is the first theorem-sized consumer of the Section-4.3
positive-energy forgetful step on the live theorem-3 file graph, and it stays
strictly transformed-image / boundary-vanishing side. It still does not recover
`OrderedPositiveTimeRegion` or enter the `PositiveTimeBorchersSequence.osInner`
positivity chain. -/
theorem bvtTransportImageSequence_component_apply_zero
    (F : BvtTransportImageSequence d) {n : ℕ} (hn : 0 < n) :
    ((F.toBorchers.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) 0 = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rcases F.image_mem (m + 1) with ⟨f, hf⟩
  calc
    ((F.toBorchers.funcs (m + 1) : SchwartzNPoint d (m + 1)) :
        NPointDomain d (m + 1) → ℂ) 0
        =
      evalAtZeroDescendsToSection43PositiveEnergyComponent (d := d) m
        (section43PositiveEnergyQuotientMap (d := d) (m + 1)
          (F.toBorchers.funcs (m + 1))) := by
            symm
            exact evalAtZeroDescendsToSection43PositiveEnergyComponent_apply
              (d := d) m (F.toBorchers.funcs (m + 1))
    _ =
      evalAtZeroDescendsToSection43PositiveEnergyComponent (d := d) m
        (os1TransportComponent d (m + 1) f) := by
          simpa [bvtTransportImage] using congrArg
            (evalAtZeroDescendsToSection43PositiveEnergyComponent (d := d) m) hf.symm
    _ = 0 := by
          simpa using
            evalAtZeroDescendsToSection43PositiveEnergyComponent_os1TransportComponent
              (d := d) m f

/-- Any componentwise-Schwartz limit of transformed-image data still vanishes at
the positive-degree boundary point `0`. This is the exact obstruction to an
arbitrary raw on-image approximation family. -/
theorem eq_zero_of_tendsto_bvtTransportImageSequence_component
    {n : ℕ} (hn : 0 < n) (G : ℕ → BvtTransportImageSequence d)
    {φ : SchwartzNPoint d n}
    (hG :
      Filter.Tendsto
        (fun N : ℕ => ((G N).toBorchers.funcs n : SchwartzNPoint d n))
        Filter.atTop
        (nhds φ)) :
    (φ : NPointDomain d n → ℂ) 0 = 0 := by
  have hcont :
      Continuous (fun f : SchwartzNPoint d n => (f : NPointDomain d n → ℂ) 0) := by
    simpa [ContinuousLinearMap.comp_apply,
      SchwartzMap.toBoundedContinuousFunctionCLM_apply] using
      ((BoundedContinuousFunction.evalCLM ℂ (0 : NPointDomain d n)).continuous.comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (NPointDomain d n) ℂ).continuous)
  have hEval :
      Filter.Tendsto
        (fun N : ℕ =>
          (((G N).toBorchers.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) 0)
        Filter.atTop
        (nhds (((φ : SchwartzNPoint d n) : NPointDomain d n → ℂ) 0)) :=
    (hcont.continuousAt.tendsto : Filter.Tendsto
      (fun f : SchwartzNPoint d n => (f : NPointDomain d n → ℂ) 0)
      (nhds φ)
      (nhds (((φ : SchwartzNPoint d n) : NPointDomain d n → ℂ) 0))).comp hG
  have hconst :
      (fun N : ℕ =>
        (((G N).toBorchers.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) 0) =
      fun _ : ℕ => (0 : ℂ) := by
    funext N
    exact bvtTransportImageSequence_component_apply_zero (d := d) (G N) hn
  have hEvalZero :
      Filter.Tendsto
        (fun _ : ℕ => (0 : ℂ))
        Filter.atTop
        (nhds (((φ : SchwartzNPoint d n) : NPointDomain d n → ℂ) 0)) := by
    simpa [hconst] using hEval
  exact tendsto_nhds_unique hEvalZero tendsto_const_nhds

/-- The exact closure hypotheses used by
`bvt_wightmanInner_self_nonneg_of_bounded_onImage_approx` cannot hold for a raw
target whose positive-degree component has nonzero boundary value at `0`. -/
theorem not_exists_bounded_onImage_approx_of_component_apply_zero_ne
    (F : BorchersSequence d) {m n : ℕ}
    (hF : F.bound ≤ m) (hn : 0 < n)
    (hFn : ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) 0 ≠ 0) :
    ¬ ∃ G : ℕ → BvtTransportImageSequence d,
        (∀ N, (G N).toBorchers.bound ≤ m) ∧
        (∀ k, k ≤ m →
          Filter.Tendsto
            (fun N : ℕ => ((G N).toBorchers.funcs k : SchwartzNPoint d k))
            Filter.atTop
            (nhds (F.funcs k))) := by
  intro hG
  rcases hG with ⟨G, hGbound, hGcomp⟩
  have hnF : n ≤ F.bound := by
    by_contra hnF
    have hgt : F.bound < n := Nat.lt_of_not_ge hnF
    have hzero : (F.funcs n : SchwartzNPoint d n) = 0 := F.bound_spec n hgt
    exact hFn (by simpa [hzero])
  have hnm : n ≤ m := le_trans hnF hF
  have hzero :=
    eq_zero_of_tendsto_bvtTransportImageSequence_component
      (d := d) (n := n) hn (G := G) (φ := F.funcs n) (hG := hGcomp n hnm)
  exact hFn hzero

/-- Exact necessary boundary-vanishing consequence of the bounded on-image
closure hypotheses used by
`bvt_wightmanInner_self_nonneg_of_bounded_onImage_approx`. Any future
VEV/boundary-value reduction must therefore first identify the target with data
whose positive-degree components already vanish at the boundary point `0`. -/
theorem component_apply_zero_eq_zero_of_bounded_onImage_approx
    (F : BorchersSequence d) {m n : ℕ}
    (hF : F.bound ≤ m) (hn : 0 < n)
    (G : ℕ → BvtTransportImageSequence d)
    (hGbound : ∀ N, (G N).toBorchers.bound ≤ m)
    (hGcomp : ∀ k, k ≤ m →
      Filter.Tendsto
        (fun N : ℕ => ((G N).toBorchers.funcs k : SchwartzNPoint d k))
        Filter.atTop
        (nhds (F.funcs k))) :
    ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) 0 = 0 := by
  by_contra hFn
  exact
    (not_exists_bounded_onImage_approx_of_component_apply_zero_ne
      (d := d) (F := F) (m := m) (n := n) hF hn hFn) ⟨G, hGbound, hGcomp⟩

/-- Bounded on-image closure forces every positive-degree component of the
candidate target to vanish at the Section-4.3 boundary point `0`. This is the
exact packaged obstruction behind the current theorem-3 frontier: any future
public reduction to `bvt_wightmanInner_self_nonneg_of_bounded_onImage_approx`
must first land in the boundary-vanishing subspace, degree by degree. -/
theorem component_apply_zero_eq_zero_of_bounded_onImage_approx_all
    (F : BorchersSequence d) {m : ℕ}
    (hF : F.bound ≤ m)
    (G : ℕ → BvtTransportImageSequence d)
    (hGbound : ∀ N, (G N).toBorchers.bound ≤ m)
    (hGcomp : ∀ k, k ≤ m →
      Filter.Tendsto
        (fun N : ℕ => ((G N).toBorchers.funcs k : SchwartzNPoint d k))
        Filter.atTop
        (nhds (F.funcs k))) :
    ∀ n, 0 < n → ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) 0 = 0 := by
  intro n hn
  exact component_apply_zero_eq_zero_of_bounded_onImage_approx
    (d := d) (F := F) (m := m) (n := n) hF hn G hGbound hGcomp

/-- Existential no-go form of the bounded on-image closure obstruction. If a
bounded Borchers target has even one positive-degree component with nonzero
boundary value at `0`, then the current closure hypotheses feeding
`bvt_wightmanInner_self_nonneg_of_bounded_onImage_approx` are impossible.
This is the exact public obstruction behind the remaining theorem-3 seam: a
prior VEV / boundary-value reduction must first land in the boundary-vanishing
subspace before the existing closure theorem can apply. -/
theorem not_exists_bounded_onImage_approx_of_exists_component_apply_zero_ne
    (F : BorchersSequence d) {m : ℕ}
    (hF : F.bound ≤ m)
    (hbad : ∃ n, 0 < n ∧ ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) 0 ≠ 0) :
    ¬ ∃ G : ℕ → BvtTransportImageSequence d,
        (∀ N, (G N).toBorchers.bound ≤ m) ∧
        (∀ k, k ≤ m →
          Filter.Tendsto
            (fun N : ℕ => ((G N).toBorchers.funcs k : SchwartzNPoint d k))
            Filter.atTop
            (nhds (F.funcs k))) := by
  rintro ⟨G, hGbound, hGcomp⟩
  rcases hbad with ⟨n, hn, hFn⟩
  have hzero :=
    component_apply_zero_eq_zero_of_bounded_onImage_approx
      (d := d) (F := F) (m := m) (n := n) hF hn G hGbound hGcomp
  exact hFn hzero

namespace PositiveTimeBorchersSequence

/-- Exact carrier-side ingress for a fixed ambient Borchers surrogate.

If the ambient components already come with degreewise positive-time witnesses,
then packaging them as an honest `PositiveTimeBorchersSequence` is formal. This
is the earliest source-backed carrier constructor strictly before the later
compact-family/on-image supplier package. -/
noncomputable def ofSubmoduleFamily
    (F : BorchersSequence d)
    (f : ∀ n, euclideanPositiveTimeSubmodule (d := d) n)
    (hf : ∀ n,
      (((f n : euclideanPositiveTimeSubmodule (d := d) n) :
          SchwartzNPoint d n)) = F.funcs n) :
    PositiveTimeBorchersSequence d where
  toBorchersSequence := F
  ordered_tsupport := by
    intro n
    simpa [hf n] using (f n).2

@[simp] theorem ofSubmoduleFamily_toBorchers
    (F : BorchersSequence d)
    (f : ∀ n, euclideanPositiveTimeSubmodule (d := d) n)
    (hf : ∀ n,
      (((f n : euclideanPositiveTimeSubmodule (d := d) n) :
          SchwartzNPoint d n)) = F.funcs n) :
    ((ofSubmoduleFamily (d := d) F f hf : PositiveTimeBorchersSequence d) :
      BorchersSequence d) = F := rfl

/-- Sharp localization of the earliest honest fixed-surrogate ingress data.

An ambient Borchers surrogate lies on the honest positive-time carrier exactly
when its components admit degreewise witnesses in the positive-time submodule.
This isolates the upstream theorem surface now missing before the canonical
compact-family supplier can start: a source theorem must construct these
componentwise witnesses for the chosen fixed surrogate `F`, not merely quotient-
side transformed-image equalities. -/
theorem exists_positiveTimeBorchersSequence_with_toBorchers_eq_iff_exists_submoduleFamily
    (F : BorchersSequence d) :
    (∃ G : PositiveTimeBorchersSequence d, (G : BorchersSequence d) = F) ↔
      ∃ f : ∀ n, euclideanPositiveTimeSubmodule (d := d) n,
        ∀ n,
          (((f n : euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n)) = F.funcs n := by
  constructor
  · rintro ⟨G, rfl⟩
    refine ⟨fun n => ⟨((G : BorchersSequence d).funcs n), G.ordered_tsupport n⟩, ?_⟩
    intro n
    rfl
  · rintro ⟨f, hf⟩
    refine ⟨ofSubmoduleFamily (d := d) F f hf, ?_⟩
    rfl

/-- Every honest positive-time Euclidean Borchers sequence already determines a
point of the Section 4.3 transformed-image carrier degreewise. This is the
direct bridge from the existing dense OS-side vector package into the new
on-image transport range. -/
noncomputable def toBvtTransportImageSequence
    (F : PositiveTimeBorchersSequence d) :
    BvtTransportImageSequence d where
  toBorchers := (F : BorchersSequence d)
  image_mem := fun n => by
    refine ⟨⟨(F : BorchersSequence d).funcs n, F.ordered_tsupport n⟩, ?_⟩
    simp [bvtTransportImage, os1TransportComponent_apply]

@[simp] theorem toBvtTransportImageSequence_toBorchers
    (F : PositiveTimeBorchersSequence d) :
    (toBvtTransportImageSequence (d := d) F).toBorchers = (F : BorchersSequence d) := rfl

/- Exact constructor-seam note:
`toBvtTransportImageSequence` is only a forward map from already positive-time
data. The current source now does have the minimal converse carrier packaging
`ofSubmoduleFamily` /
`exists_positiveTimeBorchersSequence_with_toBorchers_eq_iff_exists_submoduleFamily`,
which shows that the exact earlier fixed-surrogate ingress data is a degreewise
positive-time submodule family matching the ambient components of `F₀`.
What is still missing upstream is not that carrier packaging itself, but a
source theorem from boundary-value/VEV data that constructs such a family (or
equivalently the transformed-image supplier family needed downstream). -/

/-- Honest positive-time Euclidean data already lies on the boundary-vanishing
side of the Section-4.3 obstruction: every positive-degree component vanishes
at the boundary point `0`. Any later public reduction to positive-time or
transformed-image data must therefore factor through this constraint rather
than bypass it. -/
theorem component_apply_zero_eq_zero
    (F : PositiveTimeBorchersSequence d) {n : ℕ} (hn : 0 < n) :
    (((F : BorchersSequence d).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) 0 = 0 := by
  simpa using
    bvtTransportImageSequence_component_apply_zero (d := d)
      (F := toBvtTransportImageSequence (d := d) F) hn

/-- On the canonical compact positive-time family
`N ↦ PositiveTimeBorchersSequence.toBvtTransportImageSequence
      (compactApproxPositiveTimeBorchers F N)`,
the ambient transformed-image components inherit the compact support of the
legacy cutoff approximants. This is exactly the remaining supplier field
`hambientCompact` on that explicit family. -/
theorem compactApproxPositiveTime_toBvtTransportImageSequence_hambientCompact
    (F : PositiveTimeBorchersSequence d) :
    ∀ N n,
      n ≤ (PositiveTimeBorchersSequence.toBvtTransportImageSequence (d := d)
        (compactApproxPositiveTimeBorchers (d := d) F N)).toBorchers.bound →
      HasCompactSupport
        ((((PositiveTimeBorchersSequence.toBvtTransportImageSequence (d := d)
              (compactApproxPositiveTimeBorchers (d := d) F N)).toBorchers.funcs n :
            SchwartzNPoint d n) : NPointDomain d n → ℂ)) := by
  intro N n _hn
  simpa [PositiveTimeBorchersSequence.toBvtTransportImageSequence] using
    (compactApproxPositiveTimeBorchers_component_compact (d := d) F N n)

/-- On the canonical compact positive-time family
`N ↦ PositiveTimeBorchersSequence.toBvtTransportImageSequence
      (compactApproxPositiveTimeBorchers F N)`,
the supplier's family-level degree-`0` zero field `hG0` reduces to the single
ambient hypothesis that the original positive-time target already has zero
degree-`0` component. -/
private theorem compactApproxPositiveTime_onImage_component_zero_of_component_zero
    (F : PositiveTimeBorchersSequence d)
    (hF0 : (((F : BorchersSequence d).funcs 0 : SchwartzNPoint d 0)) = 0) :
    ∀ N,
      ((PositiveTimeBorchersSequence.toBvtTransportImageSequence (d := d)
          (compactApproxPositiveTimeBorchers (d := d) F N)).toBorchers.funcs 0 :
        SchwartzNPoint d 0) = 0 := by
  intro N
  change (SchwartzMap.smulLeftCLM ℂ _
      (((F : BorchersSequence d).funcs 0 : SchwartzNPoint d 0))) = 0
  rw [hF0]
  simp

end PositiveTimeBorchersSequence

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

@[simp] theorem euclideanPositiveTimeSingleVector_ofSubmodule_add
    (OS : OsterwalderSchraderAxioms d)
    {n : ℕ} (f g : euclideanPositiveTimeSubmodule (d := d) n) :
    euclideanPositiveTimeSingleVector (d := d) OS
        (EuclideanPositiveTimeComponent.ofSubmodule (f + g)) =
      euclideanPositiveTimeSingleVector (d := d) OS
        (EuclideanPositiveTimeComponent.ofSubmodule f) +
      euclideanPositiveTimeSingleVector (d := d) OS
        (EuclideanPositiveTimeComponent.ofSubmodule g) := by
  have hpre :
      let xfg : OSPreHilbertSpace OS :=
        ⟦EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule (f + g))⟧
      let xf : OSPreHilbertSpace OS :=
        ⟦EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule f)⟧
      let xg : OSPreHilbertSpace OS :=
        ⟦EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule g)⟧
      xfg = xf + xg := by
    dsimp
    change (Quotient.mk (osBorchersSetoid OS)
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule (f + g))) :
          OSPreHilbertSpace OS) =
      (Quotient.mk (osBorchersSetoid OS)
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule f) +
         EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule g)) :
          OSPreHilbertSpace OS)
    apply OSPreHilbertSpace.mk_eq_of_funcs_eq
    intro m
    by_cases hm : m = n
    · subst hm
      simp [EuclideanPositiveTimeComponent.toPositiveTimeSingle,
        EuclideanPositiveTimeComponent.ofSubmodule, BorchersSequence.add_funcs]
    · simp [EuclideanPositiveTimeComponent.toPositiveTimeSingle,
        EuclideanPositiveTimeComponent.ofSubmodule,
        PositiveTimeBorchersSequence.single_toBorchersSequence,
        BorchersSequence.add_funcs, hm]
  simpa [euclideanPositiveTimeSingleVector, positiveTimeBorchersVector,
    UniformSpace.Completion.coe_add] using
    congrArg (fun x : OSPreHilbertSpace OS => ((x : OSHilbertSpace OS))) hpre

@[simp] theorem euclideanPositiveTimeSingleVector_ofSubmodule_smul
    (OS : OsterwalderSchraderAxioms d)
    {n : ℕ} (c : ℂ) (f : euclideanPositiveTimeSubmodule (d := d) n) :
    euclideanPositiveTimeSingleVector (d := d) OS
        (EuclideanPositiveTimeComponent.ofSubmodule (c • f)) =
      c • euclideanPositiveTimeSingleVector (d := d) OS
        (EuclideanPositiveTimeComponent.ofSubmodule f) := by
  have hpre :
      let xcf : OSPreHilbertSpace OS :=
        ⟦EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule (c • f))⟧
      let xf : OSPreHilbertSpace OS :=
        ⟦EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule f)⟧
      xcf = c • xf := by
    dsimp
    change (Quotient.mk (osBorchersSetoid OS)
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule (c • f))) :
          OSPreHilbertSpace OS) =
      (Quotient.mk (osBorchersSetoid OS)
        (c • EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule f)) :
          OSPreHilbertSpace OS)
    apply OSPreHilbertSpace.mk_eq_of_funcs_eq
    intro m
    by_cases hm : m = n
    · subst hm
      simp [EuclideanPositiveTimeComponent.toPositiveTimeSingle,
        EuclideanPositiveTimeComponent.ofSubmodule, BorchersSequence.smul_funcs]
    · simp [EuclideanPositiveTimeComponent.toPositiveTimeSingle,
        EuclideanPositiveTimeComponent.ofSubmodule,
        PositiveTimeBorchersSequence.single_toBorchersSequence,
        BorchersSequence.smul_funcs, hm]
  simpa [euclideanPositiveTimeSingleVector, positiveTimeBorchersVector,
    UniformSpace.Completion.coe_smul] using
    congrArg (fun x : OSPreHilbertSpace OS => ((x : OSHilbertSpace OS))) hpre

@[simp] theorem euclideanPositiveTimeSingleVector_ofSubmodule_zero
    (OS : OsterwalderSchraderAxioms d)
    {n : ℕ} :
    euclideanPositiveTimeSingleVector (d := d) OS
        (EuclideanPositiveTimeComponent.ofSubmodule
          (0 : euclideanPositiveTimeSubmodule (d := d) n)) = 0 := by
  have hpre :
      let x0 : OSPreHilbertSpace OS :=
        ⟦EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule
            (0 : euclideanPositiveTimeSubmodule (d := d) n))⟧
      x0 = 0 := by
    dsimp
    change (Quotient.mk (osBorchersSetoid OS)
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule
            (0 : euclideanPositiveTimeSubmodule (d := d) n))) :
          OSPreHilbertSpace OS) =
      (0 : OSPreHilbertSpace OS)
    apply OSPreHilbertSpace.mk_eq_of_funcs_eq
    intro m
    by_cases hm : m = n
    · subst hm
      simp [EuclideanPositiveTimeComponent.toPositiveTimeSingle,
        EuclideanPositiveTimeComponent.ofSubmodule]
    · simp [EuclideanPositiveTimeComponent.toPositiveTimeSingle,
        EuclideanPositiveTimeComponent.ofSubmodule,
        PositiveTimeBorchersSequence.single_toBorchersSequence, hm]
  simpa [euclideanPositiveTimeSingleVector, positiveTimeBorchersVector,
    UniformSpace.Completion.coe_zero] using
    congrArg (fun x : OSPreHilbertSpace OS => ((x : OSHilbertSpace OS))) hpre

private noncomputable def bvtTransportImagePreimage
    (F : BvtTransportImageSequence d) (n : ℕ) :
    euclideanPositiveTimeSubmodule (d := d) n :=
  Classical.choose (F.image_mem n)

@[simp] private theorem bvtTransportImagePreimage_spec
    (F : BvtTransportImageSequence d) (n : ℕ) :
    os1TransportComponent d n (bvtTransportImagePreimage (d := d) F n) =
      section43PositiveEnergyQuotientMap (d := d) n (F.toBorchers.funcs n) :=
  Classical.choose_spec (F.image_mem n)

/-- If a transformed-image sequence is introduced from an explicit degreewise
positive-time preimage family, then the later canonical chosen preimages
`bvtTransportImagePreimage` recover exactly that supplied family. This is the
smallest constructor-side compatibility step needed to feed an explicit
ambient-to-image family into the downstream fixed-surrogate/on-image consumer
cluster without reproving representative equality componentwise. -/
@[simp] private theorem bvtTransportImagePreimage_of_ofPreimageFamily
    (F : BorchersSequence d)
    (f : ∀ n, euclideanPositiveTimeSubmodule (d := d) n)
    (hf : ∀ n,
      os1TransportComponent d n (f n) =
        section43PositiveEnergyQuotientMap (d := d) n (F.funcs n))
    (n : ℕ) :
    bvtTransportImagePreimage (d := d)
        (BvtTransportImageSequence.ofPreimageFamily (d := d) F f hf) n =
      f n := by
  apply os1TransportComponent_injective (d := d) (n := n)
  simpa [BvtTransportImageSequence.ofPreimageFamily_toBorchers] using
    (bvtTransportImagePreimage_spec (d := d)
      (F := BvtTransportImageSequence.ofPreimageFamily (d := d) F f hf) n).trans (hf n).symm

/-- Positive-degree `hH_imag_os` supplier on the transformed-image carrier.

This theorem is downstream of the live fixed-pair scalarization seam. It only
reuses the already-existing `bvt_singleSplit_xiShiftHolomorphicValue` bridge
for the canonical chosen preimages, so it is not the upstream theorem that
future Stage-5 work should try to generalize.

Source-first status:
- the honest missing upstream theorem is still the fixed ambient/preimage-pair
  upper-half-plane scalarization isolated in
  `OSToWightmanPositivity.lean` under the
  `section43_fixedPair_upperHalfPlaneScalarization` route note;
- that theorem should quantify only the ambient representatives, positive-time
  preimages, and the transport equalities, and it should produce
  `∃ Hs : ℂ → ℂ, DifferentiableOn ℂ Hs SCV.upperHalfPlane ∧ ...`;
- compact-support hypotheses and the shifted index hypothesis `hk_pos` belong
  only to this downstream consumer because they come from the existing
  `singleSplit` package, not from the actual scalarization seam.

So this theorem is still useful as the current on-image consumer, but it should
not be mistaken for the theorem-sized upstream assembly target. -/
private theorem exists_hH_imag_os_bvtTransportImagePreimage
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d)
    {n k : ℕ} (hk_pos : 0 < k)
    (hf_compact :
      HasCompactSupport
        ((((bvtTransportImagePreimage (d := d) F n :
              euclideanPositiveTimeSubmodule (d := d) n) :
            SchwartzNPoint d n) : NPointDomain d n → ℂ)))
    (hg_compact :
      HasCompactSupport
        ((((bvtTransportImagePreimage (d := d) F k :
              euclideanPositiveTimeSubmodule (d := d) k) :
            SchwartzNPoint d k) : NPointDomain d k → ℂ))) :
    ∃ H : ℂ → ℂ,
      ∀ t : ℝ, 0 < t →
        H ((t : ℂ) * Complex.I) =
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n
              ((bvtTransportImagePreimage (d := d) F n :
                  euclideanPositiveTimeSubmodule (d := d) n) :
                SchwartzNPoint d n)
              (bvtTransportImagePreimage (d := d) F n).2)
            (PositiveTimeBorchersSequence.single k
              ((bvtTransportImagePreimage (d := d) F k :
                  euclideanPositiveTimeSubmodule (d := d) k) :
                SchwartzNPoint d k)
              (bvtTransportImagePreimage (d := d) F k).2) (t : ℂ) := by
  refine ⟨fun z =>
    bvt_singleSplit_xiShiftHolomorphicValue
      (d := d) OS lgc hk_pos
      ((bvtTransportImagePreimage (d := d) F n :
          euclideanPositiveTimeSubmodule (d := d) n) :
        SchwartzNPoint d n)
      (bvtTransportImagePreimage (d := d) F n).2
      hf_compact
      ((bvtTransportImagePreimage (d := d) F k :
          euclideanPositiveTimeSubmodule (d := d) k) :
        SchwartzNPoint d k)
      (bvtTransportImagePreimage (d := d) F k).2
      hg_compact
      (-Complex.I * z), ?_⟩
  intro t ht
  have hrot : -Complex.I * ((t : ℂ) * Complex.I) = (t : ℂ) := by
    calc
      -Complex.I * ((t : ℂ) * Complex.I) = -Complex.I * (Complex.I * (t : ℂ)) := by
        rw [mul_comm ((t : ℂ)) Complex.I]
      _ = (-Complex.I * Complex.I) * (t : ℂ) := by
        rw [mul_assoc]
      _ = (1 : ℂ) * (t : ℂ) := by
        simp
      _ = (t : ℂ) := by
        simp
  have hbridge :=
    bvt_xiShift_eq_osInnerProduct_holomorphicValue_single
      (d := d) OS lgc (n := n) (m := k) hk_pos
      ((bvtTransportImagePreimage (d := d) F n :
          euclideanPositiveTimeSubmodule (d := d) n) :
        SchwartzNPoint d n)
      (bvtTransportImagePreimage (d := d) F n).2
      hf_compact
      ((bvtTransportImagePreimage (d := d) F k :
          euclideanPositiveTimeSubmodule (d := d) k) :
        SchwartzNPoint d k)
      (bvtTransportImagePreimage (d := d) F k).2
      hg_compact
      (t : ℂ) ht
  simpa [hrot] using hbridge

/-- Internal per-pair Lemma-4.2 witness-package reducer on the transformed-image
carrier.

The current infrastructure already supplies two of the three ingredients:
1. `exists_hH_imag_os_bvtTransportImagePreimage` gives the required
   imaginary-axis OS matrix-element trace for the canonical chosen preimages;
2. the public boundary-value theorem `bvt_boundary_values` gives the ambient
   canonical-shell limit to the right-time-shifted Wightman pairing.

So the remaining extra datum is precisely the positive-real-time identification
between that right-time-shifted ambient Wightman pairing and the OS matrix
element. Once that is supplied, the exact internal `hpair` witness package
consumed downstream follows formally. The endorsed public seam should therefore
be stated in terms of `hreal`, not in terms of `hpair`. -/
private theorem exists_hpair_bvtTransportImagePreimage_of_timeShift_eq_on_positiveReals
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d)
    {n k : ℕ} (hk_pos : 0 < k)
    (hf_compact :
      HasCompactSupport
        ((((bvtTransportImagePreimage (d := d) F n :
              euclideanPositiveTimeSubmodule (d := d) n) :
            SchwartzNPoint d n) : NPointDomain d n → ℂ)))
    (hg_compact :
      HasCompactSupport
        ((((bvtTransportImagePreimage (d := d) F k :
              euclideanPositiveTimeSubmodule (d := d) k) :
            SchwartzNPoint d k) : NPointDomain d k → ℂ)))
    (hreal :
      ∀ t : ℝ, 0 < t →
        bvt_W OS lgc (n + k)
          ((F.toBorchers.funcs n).conjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t (F.toBorchers.funcs k))) =
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n
              ((bvtTransportImagePreimage (d := d) F n :
                  euclideanPositiveTimeSubmodule (d := d) n) :
                SchwartzNPoint d n)
              (bvtTransportImagePreimage (d := d) F n).2)
            (PositiveTimeBorchersSequence.single k
              ((bvtTransportImagePreimage (d := d) F k :
                  euclideanPositiveTimeSubmodule (d := d) k) :
                SchwartzNPoint d k)
              (bvtTransportImagePreimage (d := d) F k).2) (t : ℂ)) :
    ∃ H : ℂ → ℂ,
      (∀ t : ℝ, 0 < t →
        H ((t : ℂ) * Complex.I) =
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n
              ((bvtTransportImagePreimage (d := d) F n :
                  euclideanPositiveTimeSubmodule (d := d) n) :
                SchwartzNPoint d n)
              (bvtTransportImagePreimage (d := d) F n).2)
            (PositiveTimeBorchersSequence.single k
              ((bvtTransportImagePreimage (d := d) F k :
                  euclideanPositiveTimeSubmodule (d := d) k) :
                SchwartzNPoint d k)
              (bvtTransportImagePreimage (d := d) F k).2) (t : ℂ)) ∧
      (∀ t : ℝ, 0 < t →
        Filter.Tendsto
          (fun ε : ℝ =>
            ∫ y : NPointDomain d (n + k),
              bvt_F OS lgc (n + k)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hk_pos⟩ 0
                  (fun j μ =>
                    ↑(y j μ) +
                      ε * ↑(canonicalForwardConeDirection (d := d) (n + k) j μ) *
                        Complex.I)
                  (t : ℂ)) *
                ((F.toBorchers.funcs n).conjTensorProduct
                  (F.toBorchers.funcs k)) y)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (H ((t : ℂ) * Complex.I)))) := by
  rcases exists_hH_imag_os_bvtTransportImagePreimage
      (d := d) (OS := OS) (lgc := lgc) (F := F) (n := n) (k := k) hk_pos
      hf_compact hg_compact with ⟨H, hH_imag_os⟩
  refine ⟨H, hH_imag_os, ?_⟩
  intro t ht
  have hboundary :
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ y : NPointDomain d (n + k),
            bvt_F OS lgc (n + k)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hk_pos⟩ 0
                (fun j μ =>
                  ↑(y j μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + k) j μ) *
                      Complex.I)
                (t : ℂ)) *
              ((F.toBorchers.funcs n).conjTensorProduct
                (F.toBorchers.funcs k)) y)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (bvt_W OS lgc (n + k)
            ((F.toBorchers.funcs n).conjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t (F.toBorchers.funcs k))))) := by
    let η0 := canonicalForwardConeDirection (d := d) (n + k)
    have hη0 : InForwardCone d (n + k) η0 :=
      canonicalForwardConeDirection_mem (d := d) (n + k)
    have hbase :
        Filter.Tendsto
          (fun ε : ℝ =>
            ∫ x : NPointDomain d (n + k),
              bvt_F OS lgc (n + k) (fun j μ =>
                ↑(x j μ) + ε * ↑(η0 j μ) * Complex.I) *
              ((F.toBorchers.funcs n).conjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t (F.toBorchers.funcs k))) x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (bvt_W OS lgc (n + k)
              ((F.toBorchers.funcs n).conjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t (F.toBorchers.funcs k))))) := by
      simpa [η0] using
        (bvt_boundary_values (d := d) OS lgc (n + k)
          ((F.toBorchers.funcs n).conjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t (F.toBorchers.funcs k)))
          η0 hη0)
    have hEq :
        (fun ε : ℝ =>
          ∫ y : NPointDomain d (n + k),
            bvt_F OS lgc (n + k)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hk_pos⟩ 0
                (fun j μ =>
                  ↑(y j μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + k) j μ) *
                      Complex.I)
                (t : ℂ)) *
              ((F.toBorchers.funcs n).conjTensorProduct
                (F.toBorchers.funcs k)) y)
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun ε : ℝ =>
          ∫ x : NPointDomain d (n + k),
            bvt_F OS lgc (n + k) (fun j μ =>
              ↑(x j μ) +
                ε * ↑(η0 j μ) * Complex.I) *
            ((F.toBorchers.funcs n).conjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t (F.toBorchers.funcs k))) x) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      let Ψ : (Fin (n + k) → Fin (d + 1) → ℂ) → ℂ := fun z =>
        bvt_F OS lgc (n + k) (fun j μ =>
          (if μ = 0 then (-Complex.I) * z j μ else z j μ) +
            ε * ↑(η0 j μ) * Complex.I)
      calc
        ∫ y : NPointDomain d (n + k),
            bvt_F OS lgc (n + k)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hk_pos⟩ 0
                (fun j μ =>
                  ↑(y j μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + k) j μ) *
                      Complex.I)
                (t : ℂ)) *
              ((F.toBorchers.funcs n).conjTensorProduct
                (F.toBorchers.funcs k)) y
          =
            ∫ y : NPointDomain d (n + k),
              Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hk_pos⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              ((F.toBorchers.funcs n).conjTensorProduct
                (F.toBorchers.funcs k)) y := by
              refine MeasureTheory.integral_congr_ae ?_
              filter_upwards with y
              have hshell :
                  bvt_F OS lgc (n + k)
                    (xiShift ⟨n, Nat.lt_add_of_pos_right hk_pos⟩ 0
                      (fun j μ =>
                        ↑(y j μ) +
                          ε * ↑(canonicalForwardConeDirection (d := d) (n + k) j μ) *
                            Complex.I)
                      (t : ℂ)) =
                    Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hk_pos⟩ 0
                      (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) := by
                unfold Ψ
                congr 1
                ext j μ
                by_cases hμ : μ = 0
                · subst hμ
                  by_cases hj : n ≤ j.val
                  · simp [wickRotatePoint, xiShift, hj]
                    have hy :
                        ↑(y j 0) + ↑ε * ↑(η0 j 0) * Complex.I + ↑t =
                          -(Complex.I * (Complex.I * ↑(y j 0) + ↑t * Complex.I)) +
                            ↑ε * ↑(η0 j 0) * Complex.I := by
                      calc
                        ↑(y j 0) + ↑ε * ↑(η0 j 0) * Complex.I + ↑t
                            =
                          -(((-1 : ℂ) * ↑(y j 0)) + ((-1 : ℂ) * ↑t)) +
                            ↑ε * ↑(η0 j 0) * Complex.I := by
                                ring
                        _ =
                          -(((Complex.I * Complex.I) * ↑(y j 0)) +
                              ((Complex.I * Complex.I) * ↑t)) +
                            ↑ε * ↑(η0 j 0) * Complex.I := by
                                simp [Complex.I_mul_I]
                        _ =
                          -(Complex.I * (Complex.I * ↑(y j 0) + ↑t * Complex.I)) +
                            ↑ε * ↑(η0 j 0) * Complex.I := by
                                ring
                    simpa [η0, add_assoc, add_left_comm, add_comm] using hy
                  · simp [wickRotatePoint, xiShift, hj]
                    have hy :
                        ↑(y j 0) + ↑ε * ↑(η0 j 0) * Complex.I =
                          -(Complex.I * (Complex.I * ↑(y j 0))) +
                            ↑ε * ↑(η0 j 0) * Complex.I := by
                      calc
                        ↑(y j 0) + ↑ε * ↑(η0 j 0) * Complex.I
                            =
                          -((-1 : ℂ) * ↑(y j 0)) + ↑ε * ↑(η0 j 0) * Complex.I := by
                              ring
                        _ =
                          -((Complex.I * Complex.I) * ↑(y j 0)) +
                            ↑ε * ↑(η0 j 0) * Complex.I := by
                              simp [Complex.I_mul_I]
                        _ =
                          -(Complex.I * (Complex.I * ↑(y j 0))) +
                            ↑ε * ↑(η0 j 0) * Complex.I := by
                              ring
                    simpa [η0, add_assoc, add_left_comm, add_comm] using hy
                · by_cases hj : n ≤ j.val
                  · simp [wickRotatePoint, xiShift, hμ, hj, η0]
                  · simp [wickRotatePoint, xiShift, hμ, hj, η0]
              rw [hshell]
        _ =
            ∫ x : NPointDomain d (n + k),
              Ψ (fun i => wickRotatePoint (x i)) *
              ((F.toBorchers.funcs n).conjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t (F.toBorchers.funcs k))) x := by
              symm
              exact simpleTensor_timeShift_integral_eq_xiShift_conj
                (d := d) (n := n) (m := k) (hm := hk_pos)
                (f := F.toBorchers.funcs n) (g := F.toBorchers.funcs k)
                (t := t) (Ψ := Ψ)
        _ =
            ∫ x : NPointDomain d (n + k),
              bvt_F OS lgc (n + k) (fun j μ =>
                ↑(x j μ) + ε * ↑(η0 j μ) * Complex.I) *
              ((F.toBorchers.funcs n).conjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t (F.toBorchers.funcs k))) x := by
              refine MeasureTheory.integral_congr_ae ?_
              filter_upwards with x
              have hshell :
                  Ψ (fun i => wickRotatePoint (x i)) =
                    bvt_F OS lgc (n + k) (fun j μ =>
                      ↑(x j μ) + ε * ↑(η0 j μ) * Complex.I) := by
                unfold Ψ
                congr 1
                ext j μ
                by_cases hμ : μ = 0
                · subst hμ
                  simp [wickRotatePoint]
                  calc
                    -(Complex.I * (Complex.I * ↑(x j 0)))
                        = -((Complex.I * Complex.I) * ↑(x j 0)) := by
                            ring
                    _ = -((-1 : ℂ) * ↑(x j 0)) := by
                          simp [Complex.I_mul_I]
                    _ = ↑(x j 0) := by
                          ring
                · simp [wickRotatePoint, hμ, η0]
              rw [hshell]
    exact Filter.Tendsto.congr' hEq.symm hbase
  have htarget :
      bvt_W OS lgc (n + k)
        ((F.toBorchers.funcs n).conjTensorProduct
          (timeShiftSchwartzNPoint (d := d) t (F.toBorchers.funcs k))) =
      H ((t : ℂ) * Complex.I) := by
    calc
      bvt_W OS lgc (n + k)
          ((F.toBorchers.funcs n).conjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t (F.toBorchers.funcs k))) =
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n
            ((bvtTransportImagePreimage (d := d) F n :
                euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n)
            (bvtTransportImagePreimage (d := d) F n).2)
          (PositiveTimeBorchersSequence.single k
            ((bvtTransportImagePreimage (d := d) F k :
                euclideanPositiveTimeSubmodule (d := d) k) :
              SchwartzNPoint d k)
            (bvtTransportImagePreimage (d := d) F k).2) (t : ℂ) :=
          hreal t ht
      _ = H ((t : ℂ) * Complex.I) := by
          symm
          exact hH_imag_os t ht
  simpa [htarget] using hboundary

/-- On the transformed-image carrier, the Stage-5 Lemma-4.2 matrix-element
consumer is independent of which positive-time preimages are used to certify
that the ambient components lie in the image. Any convenient preimage pair that
maps to the two ambient components can be replaced by the canonical chosen
preimages coming from `bvtTransportImagePreimage`. This is the exact
representative/preimage identification step needed before the existing
on-image package can consume a locally constructed upper-half-plane witness. -/
theorem lemma42_matrix_element_time_interchange_onImage_of_repr_eq_transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d)
    {n k : ℕ} (hk_pos : 0 < k)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (hf_repr :
      os1TransportComponent d n f =
        section43PositiveEnergyQuotientMap (d := d) n (F.toBorchers.funcs n))
    (hf_compact : HasCompactSupport (((f : SchwartzNPoint d n) : NPointDomain d n → ℂ)))
    (g : euclideanPositiveTimeSubmodule (d := d) k)
    (hg_repr :
      os1TransportComponent d k g =
        section43PositiveEnergyQuotientMap (d := d) k (F.toBorchers.funcs k))
    (hg_compact : HasCompactSupport (((g : SchwartzNPoint d k) : NPointDomain d k → ℂ)))
    (hψ_compact :
      HasCompactSupport ((((F.toBorchers.funcs k : SchwartzNPoint d k) :
        NPointDomain d k → ℂ))))
    (H : ℂ → ℂ)
    (hH_imag_os :
      ∀ t : ℝ, 0 < t →
        H ((t : ℂ) * Complex.I) =
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n (f : SchwartzNPoint d n) f.2)
            (PositiveTimeBorchersSequence.single k (g : SchwartzNPoint d k) g.2) (t : ℂ))
    (hlimit :
      ∀ t : ℝ, 0 < t →
        Filter.Tendsto
          (fun ε : ℝ =>
            ∫ y : NPointDomain d (n + k),
              bvt_F OS lgc (n + k)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hk_pos⟩ 0
                  (fun j μ =>
                    ↑(y j μ) +
                      ε * ↑(canonicalForwardConeDirection (d := d) (n + k) j μ) *
                        Complex.I)
                  (t : ℂ)) *
                ((F.toBorchers.funcs n).conjTensorProduct
                  (F.toBorchers.funcs k)) y)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (H ((t : ℂ) * Complex.I)))) :
    bvt_W OS lgc (n + k)
      ((F.toBorchers.funcs n).conjTensorProduct (F.toBorchers.funcs k)) =
    OS.S (n + k)
      (ZeroDiagonalSchwartz.ofClassical
        ((((bvtTransportImagePreimage (d := d) F n :
              euclideanPositiveTimeSubmodule (d := d) n) :
            SchwartzNPoint d n).osConjTensorProduct
          ((bvtTransportImagePreimage (d := d) F k :
              euclideanPositiveTimeSubmodule (d := d) k) :
            SchwartzNPoint d k)))) := by
  have hf_eq : f = bvtTransportImagePreimage (d := d) F n := by
    apply os1TransportComponent_injective (d := d) (n := n)
    rw [hf_repr, bvtTransportImagePreimage_spec]
  have hg_eq : g = bvtTransportImagePreimage (d := d) F k := by
    apply os1TransportComponent_injective (d := d) (n := k)
    rw [hg_repr, bvtTransportImagePreimage_spec]
  subst hf_eq
  subst hg_eq
  exact lemma42_matrix_element_time_interchange
    (d := d) (OS := OS) (lgc := lgc) (hm := hk_pos)
    (φ := F.toBorchers.funcs n) (ψ := F.toBorchers.funcs k)
    (f := ((bvtTransportImagePreimage (d := d) F n :
        euclideanPositiveTimeSubmodule (d := d) n) : SchwartzNPoint d n))
    (hf_ord := (bvtTransportImagePreimage (d := d) F n).2)
    (hf_compact := hf_compact)
    (g := ((bvtTransportImagePreimage (d := d) F k :
        euclideanPositiveTimeSubmodule (d := d) k) : SchwartzNPoint d k))
    (hg_ord := (bvtTransportImagePreimage (d := d) F k).2)
    (hg_compact := hg_compact)
    (hψ_compact := hψ_compact)
    (H := H) hH_imag_os hlimit

@[simp] private theorem bvtTransportImagePreimage_of_positiveTime
    (F : PositiveTimeBorchersSequence d) (n : ℕ) :
    bvtTransportImagePreimage (d := d)
        (PositiveTimeBorchersSequence.toBvtTransportImageSequence (d := d) F) n =
      ⟨(F : BorchersSequence d).funcs n, F.ordered_tsupport n⟩ := by
  apply os1TransportComponent_injective (d := d) (n := n)
  simpa [PositiveTimeBorchersSequence.toBvtTransportImageSequence,
    os1TransportComponent_apply] using
    (bvtTransportImagePreimage_spec (d := d)
      (F := PositiveTimeBorchersSequence.toBvtTransportImageSequence (d := d) F) n)

/-- The Section 4.3 Hilbert transport on the transformed-image core. It is
defined by choosing a positive-time Euclidean preimage degreewise and summing
the resulting OS Hilbert vectors over the finite Borchers bound. -/
noncomputable def bvt_transport_to_osHilbert_onImage
    (OS : OsterwalderSchraderAxioms d)
    (F : BvtTransportImageSequence d) :
    OSHilbertSpace OS :=
  (Finset.range (F.toBorchers.bound + 1)).sum fun n =>
    euclideanPositiveTimeSingleVector (d := d) OS
      (EuclideanPositiveTimeComponent.ofSubmodule
        (bvtTransportImagePreimage (d := d) F n))

/-- The on-image transport does not depend on which positive-time Euclidean
preimage family is used to represent the transformed-image data. The proof uses
only `os1TransportComponent_injective`, not any density theorem. -/
theorem bvt_transport_to_osHilbert_onImage_wellDefined
    (OS : OsterwalderSchraderAxioms d)
    (F : BvtTransportImageSequence d)
    (g : ∀ n, euclideanPositiveTimeSubmodule (d := d) n)
    (hg : ∀ n,
      os1TransportComponent d n (g n) =
        section43PositiveEnergyQuotientMap (d := d) n (F.toBorchers.funcs n)) :
    bvt_transport_to_osHilbert_onImage OS F =
      (Finset.range (F.toBorchers.bound + 1)).sum fun n =>
        euclideanPositiveTimeSingleVector (d := d) OS
          (EuclideanPositiveTimeComponent.ofSubmodule (g n)) := by
  unfold bvt_transport_to_osHilbert_onImage
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hpre :
      bvtTransportImagePreimage (d := d) F n = g n := by
    apply os1TransportComponent_injective (d := d) (n := n)
    rw [bvtTransportImagePreimage_spec, hg]
  simp [hpre]

private theorem bvt_transport_to_osHilbert_onImage_eq_padded_sum
    (OS : OsterwalderSchraderAxioms d)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hm : F.toBorchers.bound ≤ m) :
    bvt_transport_to_osHilbert_onImage OS F =
      (Finset.range (m + 1)).sum fun n =>
        if h : n ≤ F.toBorchers.bound then
          euclideanPositiveTimeSingleVector (d := d) OS
            (EuclideanPositiveTimeComponent.ofSubmodule
              (bvtTransportImagePreimage (d := d) F n))
        else 0 := by
  let v : ℕ → OSHilbertSpace OS := fun n =>
    euclideanPositiveTimeSingleVector (d := d) OS
      (EuclideanPositiveTimeComponent.ofSubmodule
        (bvtTransportImagePreimage (d := d) F n))
  unfold bvt_transport_to_osHilbert_onImage
  have hprefix :
      (Finset.range (F.toBorchers.bound + 1)).sum
          (fun n => if h : n ≤ F.toBorchers.bound then v n else 0) =
        (Finset.range (F.toBorchers.bound + 1)).sum v := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hle : n ≤ F.toBorchers.bound := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    simp [v, hle]
  have hmdecomp : m + 1 = (F.toBorchers.bound + 1) + (m - F.toBorchers.bound) := by
    omega
  have htail :
      ((Finset.range (m - F.toBorchers.bound)).sum fun k =>
        if h : F.toBorchers.bound + 1 + k ≤ F.toBorchers.bound then
          v (F.toBorchers.bound + 1 + k)
        else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro k hk
    have hnot : ¬ F.toBorchers.bound + 1 + k ≤ F.toBorchers.bound := by
      omega
    simp [v, hnot]
  have hpad :
      (Finset.range (m + 1)).sum
          (fun n => if h : n ≤ F.toBorchers.bound then v n else 0) =
        (Finset.range (F.toBorchers.bound + 1)).sum
          (fun n => if h : n ≤ F.toBorchers.bound then v n else 0) := by
    rw [hmdecomp, Finset.sum_range_add, htail, add_zero]
  calc
    (Finset.range (F.toBorchers.bound + 1)).sum v =
      (Finset.range (F.toBorchers.bound + 1)).sum
        (fun n => if h : n ≤ F.toBorchers.bound then v n else 0) := by
          symm
          exact hprefix
    _ =
      (Finset.range (m + 1)).sum
        (fun n => if h : n ≤ F.toBorchers.bound then v n else 0) := by
          symm
          exact hpad

theorem bvt_transport_to_osHilbert_onImage_add
    (OS : OsterwalderSchraderAxioms d)
    (F G : BvtTransportImageSequence d) :
    bvt_transport_to_osHilbert_onImage OS (F + G) =
      bvt_transport_to_osHilbert_onImage OS F +
      bvt_transport_to_osHilbert_onImage OS G := by
  let m := max F.toBorchers.bound G.toBorchers.bound
  have hfg :
      ∀ n,
        os1TransportComponent d n
            ((if h : n ≤ F.toBorchers.bound then
                bvtTransportImagePreimage (d := d) F n
              else 0) +
              (if h : n ≤ G.toBorchers.bound then
                bvtTransportImagePreimage (d := d) G n
              else 0)) =
          section43PositiveEnergyQuotientMap (d := d) n
            ((F + G).toBorchers.funcs n) := by
    intro n
    have hspecF :
        section43PositiveEnergyQuotientMap (d := d) n
            (bvtTransportImagePreimage (d := d) F n : SchwartzNPoint d n) =
          section43PositiveEnergyQuotientMap (d := d) n (F.toBorchers.funcs n) := by
      simpa [os1TransportComponent_apply] using
        (bvtTransportImagePreimage_spec (d := d) F n)
    have hspecG :
        section43PositiveEnergyQuotientMap (d := d) n
            (bvtTransportImagePreimage (d := d) G n : SchwartzNPoint d n) =
          section43PositiveEnergyQuotientMap (d := d) n (G.toBorchers.funcs n) := by
      simpa [os1TransportComponent_apply] using
        (bvtTransportImagePreimage_spec (d := d) G n)
    by_cases hF : n ≤ F.toBorchers.bound
    · by_cases hG : n ≤ G.toBorchers.bound
      · simp [hF, hG, add_toBorchers, BorchersSequence.add_funcs, map_add,
          hspecF, hspecG]
      · have hGt : G.toBorchers.bound < n := by omega
        simp [hF, hG, G.toBorchers.bound_spec n hGt, add_toBorchers,
          BorchersSequence.add_funcs, map_add, hspecF]
    · have hFt : F.toBorchers.bound < n := by omega
      by_cases hG : n ≤ G.toBorchers.bound
      · simp [hF, hG, F.toBorchers.bound_spec n hFt, add_toBorchers,
          BorchersSequence.add_funcs, map_add, hspecG]
      · have hGt : G.toBorchers.bound < n := by omega
        simp [hF, hG, F.toBorchers.bound_spec n hFt, G.toBorchers.bound_spec n hGt,
          add_toBorchers, BorchersSequence.add_funcs, map_add]
  rw [bvt_transport_to_osHilbert_onImage_wellDefined (d := d) (OS := OS)
    (F := F + G) (g := fun n =>
      (if h : n ≤ F.toBorchers.bound then
        bvtTransportImagePreimage (d := d) F n
      else 0) +
      (if h : n ≤ G.toBorchers.bound then
        bvtTransportImagePreimage (d := d) G n
      else 0)) hfg]
  rw [bvt_transport_to_osHilbert_onImage_eq_padded_sum (d := d) (OS := OS)
    (F := F) (m := m) (by
      dsimp [m]
      exact le_max_left _ _)]
  rw [bvt_transport_to_osHilbert_onImage_eq_padded_sum (d := d) (OS := OS)
    (F := G) (m := m) (by
      dsimp [m]
      exact le_max_right _ _)]
  dsimp [m]
  have hsum :
      (Finset.range (max F.toBorchers.bound G.toBorchers.bound + 1)).sum
          (fun n =>
            euclideanPositiveTimeSingleVector (d := d) OS
              (EuclideanPositiveTimeComponent.ofSubmodule
                ((if h : n ≤ F.toBorchers.bound then
                    bvtTransportImagePreimage (d := d) F n
                  else 0) +
                  if h : n ≤ G.toBorchers.bound then
                    bvtTransportImagePreimage (d := d) G n
                  else 0))) =
        (Finset.range (max F.toBorchers.bound G.toBorchers.bound + 1)).sum
            (fun n =>
              (if h : n ≤ F.toBorchers.bound then
                euclideanPositiveTimeSingleVector (d := d) OS
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F n))
              else 0) +
              if h : n ≤ G.toBorchers.bound then
                euclideanPositiveTimeSingleVector (d := d) OS
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) G n))
              else 0) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    by_cases hF : n ≤ F.toBorchers.bound
    · by_cases hG : n ≤ G.toBorchers.bound
      · simp [hF, hG, euclideanPositiveTimeSingleVector_ofSubmodule_add]
      · simp [hF, hG, euclideanPositiveTimeSingleVector_ofSubmodule_add,
          euclideanPositiveTimeSingleVector_ofSubmodule_zero]
    · by_cases hG : n ≤ G.toBorchers.bound
      · simp [hF, hG, euclideanPositiveTimeSingleVector_ofSubmodule_add,
          euclideanPositiveTimeSingleVector_ofSubmodule_zero]
      · simp [hF, hG, euclideanPositiveTimeSingleVector_ofSubmodule_add,
          euclideanPositiveTimeSingleVector_ofSubmodule_zero]
  calc
    (Finset.range (max F.toBorchers.bound G.toBorchers.bound + 1)).sum
        (fun n =>
          euclideanPositiveTimeSingleVector (d := d) OS
            (EuclideanPositiveTimeComponent.ofSubmodule
              ((if n ≤ F.toBorchers.bound then
                  bvtTransportImagePreimage (d := d) F n
                else 0) +
                if n ≤ G.toBorchers.bound then
                  bvtTransportImagePreimage (d := d) G n
                else 0))) =
      (Finset.range (max F.toBorchers.bound G.toBorchers.bound + 1)).sum
        (fun n =>
          (if h : n ≤ F.toBorchers.bound then
            euclideanPositiveTimeSingleVector (d := d) OS
              (EuclideanPositiveTimeComponent.ofSubmodule
                (bvtTransportImagePreimage (d := d) F n))
          else 0) +
          if h : n ≤ G.toBorchers.bound then
            euclideanPositiveTimeSingleVector (d := d) OS
              (EuclideanPositiveTimeComponent.ofSubmodule
                (bvtTransportImagePreimage (d := d) G n))
          else 0) := hsum
    _ = _ := by
      rw [Finset.sum_add_distrib]
      rfl

theorem bvt_transport_to_osHilbert_onImage_smul
    (OS : OsterwalderSchraderAxioms d)
    (c : ℂ) (F : BvtTransportImageSequence d) :
    bvt_transport_to_osHilbert_onImage OS (c • F) =
      c • bvt_transport_to_osHilbert_onImage OS F := by
  have hF :
      ∀ n,
        os1TransportComponent d n (c • bvtTransportImagePreimage (d := d) F n) =
          section43PositiveEnergyQuotientMap (d := d) n
            ((c • F).toBorchers.funcs n) := by
    intro n
    rw [map_smul, bvtTransportImagePreimage_spec]
    simp [smul_toBorchers, BorchersSequence.smul_funcs]
  rw [bvt_transport_to_osHilbert_onImage_wellDefined (d := d) (OS := OS)
    (F := c • F) (g := fun n => c • bvtTransportImagePreimage (d := d) F n) hF]
  simp [bvt_transport_to_osHilbert_onImage, Finset.smul_sum,
    euclideanPositiveTimeSingleVector_ofSubmodule_smul]

private theorem positiveTime_preHilbert_eq_sum_singles
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    (⟦F⟧ : OSPreHilbertSpace OS) =
      ((Finset.range ((F : BorchersSequence d).bound + 1)).sum fun k =>
        (⟦PositiveTimeBorchersSequence.single k ((F : BorchersSequence d).funcs k)
            (F.ordered_tsupport k)⟧ : OSPreHilbertSpace OS) : OSPreHilbertSpace OS) := by
  suffices h :
      ∀ (s : Finset ℕ) (G : PositiveTimeBorchersSequence d),
        (∀ k, k ∉ s → ((G : BorchersSequence d).funcs k) = 0) →
        (⟦G⟧ : OSPreHilbertSpace OS) =
          ((s.sum fun k =>
            (⟦PositiveTimeBorchersSequence.single k ((G : BorchersSequence d).funcs k)
                (G.ordered_tsupport k)⟧ : OSPreHilbertSpace OS)) : OSPreHilbertSpace OS) from
    h (Finset.range (((F : BorchersSequence d).bound) + 1)) F (fun k hk =>
      (F : BorchersSequence d).bound_spec k (by
        simp only [Finset.mem_range, not_lt] at hk
        omega))
  intro s
  induction s using Finset.cons_induction with
  | empty =>
      intro G hG
      rw [Finset.sum_empty]
      show (⟦G⟧ : OSPreHilbertSpace OS) =
          (0 : OSPreHilbertSpace OS)
      rw [show (0 : OSPreHilbertSpace OS) =
          (⟦(0 : PositiveTimeBorchersSequence d)⟧ : OSPreHilbertSpace OS) from rfl]
      exact OSPreHilbertSpace.mk_eq_of_funcs_eq OS G 0 (fun k => by
        simp [hG k (by simp)])
  | @cons a s ha ih =>
      intro G hG
      rw [Finset.sum_cons]
      let G' : PositiveTimeBorchersSequence d :=
        { toBorchersSequence :=
            { funcs := fun k => if k = a then 0 else ((G : BorchersSequence d).funcs k)
              bound := max ((G : BorchersSequence d).bound) a
              bound_spec := fun k hk => by
                show (if k = a then (0 : SchwartzNPoint d k)
                  else ((G : BorchersSequence d).funcs k)) = 0
                split
                · rfl
                · next hka =>
                    exact (G : BorchersSequence d).bound_spec k (by omega) }
          ordered_tsupport := fun k => by
            by_cases hka : k = a
            · subst hka
              simpa using
                (empty_subset (OrderedPositiveTimeRegion d a) :
                  (∅ : Set (NPointDomain d a)) ⊆ OrderedPositiveTimeRegion d a)
            · simpa [hka] using G.ordered_tsupport k }
      have hG'supp : ∀ k, k ∉ s → ((G' : BorchersSequence d).funcs k) = 0 := by
        intro k hk
        simp only [G']
        by_cases hka : k = a
        · simp [hka]
        · simp [hka]
          exact hG k (fun hmem => (Finset.mem_cons.mp hmem).elim hka hk)
      have h_split :
          (Quotient.mk (osBorchersSetoid OS) G : OSPreHilbertSpace OS) =
            (Quotient.mk (osBorchersSetoid OS)
              (G' + PositiveTimeBorchersSequence.single a
                ((G : BorchersSequence d).funcs a) (G.ordered_tsupport a)) :
                  OSPreHilbertSpace OS) :=
        OSPreHilbertSpace.mk_eq_of_funcs_eq OS G
          (G' + PositiveTimeBorchersSequence.single a
            ((G : BorchersSequence d).funcs a) (G.ordered_tsupport a)) (fun k => by
              simp [G']
              by_cases hka : k = a
              · subst hka
                simp
              · simp [hka])
      rw [h_split]
      have hG'eq :
          (⟦G'⟧ : OSPreHilbertSpace OS) =
            ((s.sum fun k =>
              (⟦PositiveTimeBorchersSequence.single k ((G : BorchersSequence d).funcs k)
                  (G.ordered_tsupport k)⟧ : OSPreHilbertSpace OS)) : OSPreHilbertSpace OS) := by
        rw [show ((s.sum fun k =>
            (⟦PositiveTimeBorchersSequence.single k ((G : BorchersSequence d).funcs k)
                (G.ordered_tsupport k)⟧ : OSPreHilbertSpace OS)) : OSPreHilbertSpace OS) =
            ((s.sum fun k =>
              (⟦PositiveTimeBorchersSequence.single k ((G' : BorchersSequence d).funcs k)
                  (G'.ordered_tsupport k)⟧ : OSPreHilbertSpace OS)) : OSPreHilbertSpace OS) from by
              refine Finset.sum_congr rfl ?_
              intro k hk
              congr 1
              congr 1
              show ((G : BorchersSequence d).funcs k) =
                (if k = a then 0 else (G : BorchersSequence d).funcs k)
              split
              · next hka =>
                  subst hka
                  exact (ha hk).elim
              · rfl]
        exact ih G' hG'supp
      rw [show (Quotient.mk (osBorchersSetoid OS)
          (G' + PositiveTimeBorchersSequence.single a
            ((G : BorchersSequence d).funcs a) (G.ordered_tsupport a)) :
            OSPreHilbertSpace OS) =
          (Quotient.mk (osBorchersSetoid OS)
            (PositiveTimeBorchersSequence.single a
              ((G : BorchersSequence d).funcs a) (G.ordered_tsupport a) + G') :
              OSPreHilbertSpace OS) from
            OSPreHilbertSpace.mk_eq_of_funcs_eq OS _ _ (fun k => by
              simp [BorchersSequence.add_funcs, add_comm])]
      exact congrArg
        (fun x : OSPreHilbertSpace OS =>
          ((show OSPreHilbertSpace OS from
              (⟦PositiveTimeBorchersSequence.single a
                  ((G : BorchersSequence d).funcs a) (G.ordered_tsupport a)⟧)) + x))
        hG'eq

private theorem positiveTimeBorchersVector_eq_sum_singles
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    positiveTimeBorchersVector (d := d) OS F =
      (Finset.range (((F : BorchersSequence d).bound) + 1)).sum fun n =>
        euclideanPositiveTimeSingleVector (d := d) OS
          (EuclideanPositiveTimeComponent.ofSubmodule
            ⟨((F : BorchersSequence d).funcs n), F.ordered_tsupport n⟩) := by
  have h :=
    congrArg (fun x : OSPreHilbertSpace OS => ((x : OSHilbertSpace OS)))
      (positiveTime_preHilbert_eq_sum_singles (d := d) OS F)
  let xsingle : ℕ → OSPreHilbertSpace OS := fun n =>
    (⟦PositiveTimeBorchersSequence.single n ((F : BorchersSequence d).funcs n)
        (F.ordered_tsupport n)⟧ : OSPreHilbertSpace OS)
  have hcoe_sum :
      (↑((Finset.range (((F : BorchersSequence d).bound) + 1)).sum fun n =>
          xsingle n) : OSHilbertSpace OS) =
        (Finset.range (((F : BorchersSequence d).bound) + 1)).sum fun n =>
          ((xsingle n : OSPreHilbertSpace OS) : OSHilbertSpace OS) := by
    induction Finset.range (((F : BorchersSequence d).bound) + 1) using Finset.cons_induction with
    | empty =>
        simp [xsingle]
    | cons a s ha ih =>
        rw [Finset.sum_cons, UniformSpace.Completion.coe_add, Finset.sum_cons, ih]
  simpa [positiveTimeBorchersVector, euclideanPositiveTimeSingleVector, xsingle, hcoe_sum] using h

/-- The new transformed-image transport extends the old positive-time OS vector
package on the honest positive-time Euclidean core. This is the key bridge
needed before the final density closure for `bvt_W_positive`. -/
theorem bvt_transport_to_osHilbert_onImage_of_positiveTime
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    bvt_transport_to_osHilbert_onImage OS
        (PositiveTimeBorchersSequence.toBvtTransportImageSequence (d := d) F) =
      positiveTimeBorchersVector (d := d) OS F := by
  rw [bvt_transport_to_osHilbert_onImage_wellDefined (d := d) (OS := OS)
    (F := PositiveTimeBorchersSequence.toBvtTransportImageSequence (d := d) F)
    (g := fun n => ⟨((F : BorchersSequence d).funcs n), F.ordered_tsupport n⟩)]
  · simpa using (positiveTimeBorchersVector_eq_sum_singles (d := d) OS F).symm
  · intro n
    simp [PositiveTimeBorchersSequence.toBvtTransportImageSequence,
      os1TransportComponent_apply]

/-- Every old positive-time OS vector already lies in the range of the new
Section-4.3 transport map. This is the exact range inclusion needed by the
future final density closure. -/
theorem range_positiveTimeBorchersVector_subset_range_bvt_transport_to_osHilbert_onImage
    (OS : OsterwalderSchraderAxioms d) :
    Set.range (positiveTimeBorchersVector (d := d) OS) ⊆
      Set.range (bvt_transport_to_osHilbert_onImage (d := d) OS) := by
  rintro x ⟨F, rfl⟩
  exact ⟨PositiveTimeBorchersSequence.toBvtTransportImageSequence (d := d) F, by
    simpa using bvt_transport_to_osHilbert_onImage_of_positiveTime (d := d) OS F⟩

/-- The transformed-image transport range is already dense in the OS Hilbert
space because it contains the existing dense positive-time Borchers vectors. -/
theorem denseRange_bvt_transport_to_osHilbert_onImage
    (OS : OsterwalderSchraderAxioms d) :
    Dense (Set.range (bvt_transport_to_osHilbert_onImage (d := d) OS)) := by
  exact (positiveTimeBorchersVector_dense (d := d) OS).mono
    (range_positiveTimeBorchersVector_subset_range_bvt_transport_to_osHilbert_onImage
      (d := d) OS)

private theorem inner_bvt_transport_to_osHilbert_onImage_eq_double_sum
    (OS : OsterwalderSchraderAxioms d)
    (F G : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) (hGm : G.toBorchers.bound ≤ m) :
    @inner ℂ (OSHilbertSpace OS) _
        (bvt_transport_to_osHilbert_onImage OS F)
        (bvt_transport_to_osHilbert_onImage OS G) =
      (Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          @inner ℂ (OSHilbertSpace OS) _
            (if h : n ≤ F.toBorchers.bound then
              euclideanPositiveTimeSingleVector (d := d) OS
                (EuclideanPositiveTimeComponent.ofSubmodule
                  (bvtTransportImagePreimage (d := d) F n))
            else 0)
            (if h : k ≤ G.toBorchers.bound then
              euclideanPositiveTimeSingleVector (d := d) OS
                (EuclideanPositiveTimeComponent.ofSubmodule
                  (bvtTransportImagePreimage (d := d) G k))
            else 0) := by
  rw [bvt_transport_to_osHilbert_onImage_eq_padded_sum (d := d) (OS := OS)
      (F := F) (m := m) hFm]
  rw [bvt_transport_to_osHilbert_onImage_eq_padded_sum (d := d) (OS := OS)
      (F := G) (m := m) hGm]
  rw [sum_inner]
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [inner_sum]

private theorem norm_sq_bvt_transport_to_osHilbert_onImage_eq_double_sum
    (OS : OsterwalderSchraderAxioms d)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) :
    ‖bvt_transport_to_osHilbert_onImage OS F‖ ^ 2 =
      ((Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          @inner ℂ (OSHilbertSpace OS) _
            (if h : n ≤ F.toBorchers.bound then
              euclideanPositiveTimeSingleVector (d := d) OS
                (EuclideanPositiveTimeComponent.ofSubmodule
                  (bvtTransportImagePreimage (d := d) F n))
            else 0)
            (if h : k ≤ F.toBorchers.bound then
              euclideanPositiveTimeSingleVector (d := d) OS
                (EuclideanPositiveTimeComponent.ofSubmodule
                  (bvtTransportImagePreimage (d := d) F k))
            else 0)).re := by
  have hnorm :
      RCLike.re
        (@inner ℂ (OSHilbertSpace OS) _
          (bvt_transport_to_osHilbert_onImage OS F)
          (bvt_transport_to_osHilbert_onImage OS F)) =
        ‖bvt_transport_to_osHilbert_onImage OS F‖ ^ 2 := by
    simpa using
      (inner_self_eq_norm_sq (𝕜 := ℂ) (bvt_transport_to_osHilbert_onImage OS F))
  rw [← hnorm, inner_bvt_transport_to_osHilbert_onImage_eq_double_sum
    (d := d) (OS := OS) (F := F) (G := F) (m := m) hFm hFm]
  have houter :
      RCLike.re
          ((Finset.range (m + 1)).sum fun n =>
            (Finset.range (m + 1)).sum fun k =>
              @inner ℂ (OSHilbertSpace OS) _
                (if h : n ≤ F.toBorchers.bound then
                  euclideanPositiveTimeSingleVector (d := d) OS
                    (EuclideanPositiveTimeComponent.ofSubmodule
                      (bvtTransportImagePreimage (d := d) F n))
                else 0)
                (if h : k ≤ F.toBorchers.bound then
                  euclideanPositiveTimeSingleVector (d := d) OS
                    (EuclideanPositiveTimeComponent.ofSubmodule
                      (bvtTransportImagePreimage (d := d) F k))
                else 0)) =
        (Finset.range (m + 1)).sum fun n =>
          RCLike.re
            ((Finset.range (m + 1)).sum fun k =>
              @inner ℂ (OSHilbertSpace OS) _
                (if h : n ≤ F.toBorchers.bound then
                  euclideanPositiveTimeSingleVector (d := d) OS
                    (EuclideanPositiveTimeComponent.ofSubmodule
                      (bvtTransportImagePreimage (d := d) F n))
                else 0)
                (if h : k ≤ F.toBorchers.bound then
                  euclideanPositiveTimeSingleVector (d := d) OS
                    (EuclideanPositiveTimeComponent.ofSubmodule
                      (bvtTransportImagePreimage (d := d) F k))
                else 0)) := by
    simpa using
      (Complex.re_sum (s := Finset.range (m + 1))
        (f := fun n =>
          (Finset.range (m + 1)).sum fun k =>
            @inner ℂ (OSHilbertSpace OS) _
              (if h : n ≤ F.toBorchers.bound then
                euclideanPositiveTimeSingleVector (d := d) OS
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F n))
              else 0)
              (if h : k ≤ F.toBorchers.bound then
                euclideanPositiveTimeSingleVector (d := d) OS
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F k))
              else 0)))
  rw [houter]
  have hinner :
      ∀ n,
        RCLike.re
            ((Finset.range (m + 1)).sum fun k =>
              @inner ℂ (OSHilbertSpace OS) _
                (if h : n ≤ F.toBorchers.bound then
                  euclideanPositiveTimeSingleVector (d := d) OS
                    (EuclideanPositiveTimeComponent.ofSubmodule
                      (bvtTransportImagePreimage (d := d) F n))
                else 0)
                (if h : k ≤ F.toBorchers.bound then
                  euclideanPositiveTimeSingleVector (d := d) OS
                    (EuclideanPositiveTimeComponent.ofSubmodule
                      (bvtTransportImagePreimage (d := d) F k))
                else 0)) =
          (Finset.range (m + 1)).sum fun k =>
            (@inner ℂ (OSHilbertSpace OS) _
              (if h : n ≤ F.toBorchers.bound then
                euclideanPositiveTimeSingleVector (d := d) OS
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F n))
              else 0)
              (if h : k ≤ F.toBorchers.bound then
                euclideanPositiveTimeSingleVector (d := d) OS
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F k))
              else 0)).re := by
    intro n
    simpa using
      (Complex.re_sum (s := Finset.range (m + 1))
        (f := fun k =>
          @inner ℂ (OSHilbertSpace OS) _
            (if h : n ≤ F.toBorchers.bound then
              euclideanPositiveTimeSingleVector (d := d) OS
                (EuclideanPositiveTimeComponent.ofSubmodule
                  (bvtTransportImagePreimage (d := d) F n))
            else 0)
            (if h : k ≤ F.toBorchers.bound then
              euclideanPositiveTimeSingleVector (d := d) OS
                (EuclideanPositiveTimeComponent.ofSubmodule
                  (bvtTransportImagePreimage (d := d) F k))
            else 0)))
  simpa [hinner]

private theorem inner_euclideanPositiveTimeSingleVector_ofSubmodule_eq_osInner
    (OS : OsterwalderSchraderAxioms d)
    {n k : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) k) :
    @inner ℂ (OSHilbertSpace OS) _
        (euclideanPositiveTimeSingleVector (d := d) OS
          (EuclideanPositiveTimeComponent.ofSubmodule f))
        (euclideanPositiveTimeSingleVector (d := d) OS
          (EuclideanPositiveTimeComponent.ofSubmodule g)) =
      PositiveTimeBorchersSequence.osInner OS
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule f))
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule g)) := by
  simp [euclideanPositiveTimeSingleVector, positiveTimeBorchersVector_inner_eq]

private theorem norm_sq_bvt_transport_to_osHilbert_onImage_eq_osInner_padded_double_sum
    (OS : OsterwalderSchraderAxioms d)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) :
    ‖bvt_transport_to_osHilbert_onImage OS F‖ ^ 2 =
      ((Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          if h₁ : n ≤ F.toBorchers.bound then
            if h₂ : k ≤ F.toBorchers.bound then
              PositiveTimeBorchersSequence.osInner OS
                (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F n)))
                (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F k)))
            else 0
          else 0).re := by
  rw [norm_sq_bvt_transport_to_osHilbert_onImage_eq_double_sum
    (d := d) (OS := OS) (F := F) (m := m) hFm]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro n hn
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h₁ : n ≤ F.toBorchers.bound
  · by_cases h₂ : k ≤ F.toBorchers.bound
    · simp [h₁, h₂,
        inner_euclideanPositiveTimeSingleVector_ofSubmodule_eq_osInner]
    · simp [h₁, h₂]
  · simp [h₁]

private theorem bvt_wightmanInner_eq_padded_double_sum
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) (hGm : G.toBorchers.bound ≤ m) :
    WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers G.toBorchers =
      (Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          if h₁ : n ≤ F.toBorchers.bound then
            if h₂ : k ≤ G.toBorchers.bound then
              bvt_W OS lgc (n + k)
                ((F.toBorchers.funcs n).conjTensorProduct (G.toBorchers.funcs k))
            else 0
          else 0 := by
  have hw :
      WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers G.toBorchers =
        WightmanInnerProductN d (bvt_W OS lgc) F.toBorchers G.toBorchers
          (m + 1) (m + 1) := by
    apply WightmanInnerProduct_eq_extended (d := d) (W := bvt_W OS lgc)
      (hlin := bvt_W_linear (d := d) OS lgc)
    · exact Nat.succ_le_succ hFm
    · exact Nat.succ_le_succ hGm
  rw [hw]
  unfold WightmanInnerProductN
  refine Finset.sum_congr rfl ?_
  intro n hn
  by_cases hN : n ≤ F.toBorchers.bound
  · refine Finset.sum_congr rfl ?_
    intro k hk
    by_cases hK : k ≤ G.toBorchers.bound
    · simp [hN, hK]
    · have hkgt : G.toBorchers.bound < k := by omega
      simp [hN, hK, G.toBorchers.bound_spec k hkgt,
        (bvt_W_linear (d := d) OS lgc _).map_zero]
  · have hngt : F.toBorchers.bound < n := by omega
    simp [hN]
    apply Finset.sum_eq_zero
    intro k hk
    rw [F.toBorchers.bound_spec n hngt, SchwartzMap.conjTensorProduct_zero_left,
      (bvt_W_linear (d := d) OS lgc _).map_zero]

private theorem bvt_wightmanInner_eq_single_single_padded_double_sum
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) (hGm : G.toBorchers.bound ≤ m) :
    WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers G.toBorchers =
      (Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          if h₁ : n ≤ F.toBorchers.bound then
            if h₂ : k ≤ G.toBorchers.bound then
              WightmanInnerProduct d (bvt_W OS lgc)
                (BorchersSequence.single n (F.toBorchers.funcs n))
                (BorchersSequence.single k (G.toBorchers.funcs k))
            else 0
          else 0 := by
  rw [bvt_wightmanInner_eq_padded_double_sum
    (d := d) (OS := OS) (lgc := lgc) (F := F) (G := G) (m := m) hFm hGm]
  refine Finset.sum_congr rfl ?_
  intro n hn
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h₁ : n ≤ F.toBorchers.bound
  · by_cases h₂ : k ≤ G.toBorchers.bound
    · simp [h₁, h₂, WightmanInnerProduct_single_single, bvt_W_linear]
    · simp [h₁, h₂]
  · simp [h₁]

theorem bvt_wightmanInner_eq_transport_inner_onImage_of_single_single
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) (hGm : G.toBorchers.bound ≤ m)
    (hss : ∀ n k,
      n ≤ F.toBorchers.bound →
      k ≤ G.toBorchers.bound →
      WightmanInnerProduct d (bvt_W OS lgc)
          (BorchersSequence.single n (F.toBorchers.funcs n))
          (BorchersSequence.single k (G.toBorchers.funcs k)) =
        PositiveTimeBorchersSequence.osInner OS
          (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
            (EuclideanPositiveTimeComponent.ofSubmodule
              (bvtTransportImagePreimage (d := d) F n)))
          (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
            (EuclideanPositiveTimeComponent.ofSubmodule
              (bvtTransportImagePreimage (d := d) G k)))) :
    WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers G.toBorchers =
      @inner ℂ (OSHilbertSpace OS) _
        (bvt_transport_to_osHilbert_onImage OS F)
        (bvt_transport_to_osHilbert_onImage OS G) := by
  rw [bvt_wightmanInner_eq_single_single_padded_double_sum
    (d := d) (OS := OS) (lgc := lgc) (F := F) (G := G) (m := m) hFm hGm]
  rw [inner_bvt_transport_to_osHilbert_onImage_eq_double_sum
    (d := d) (OS := OS) (F := F) (G := G) (m := m) hFm hGm]
  refine Finset.sum_congr rfl ?_
  intro n hn
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h₁ : n ≤ F.toBorchers.bound
  · by_cases h₂ : k ≤ G.toBorchers.bound
    · simp [h₁, h₂, hss n k h₁ h₂,
        inner_euclideanPositiveTimeSingleVector_ofSubmodule_eq_osInner]
    · simp [h₁, h₂]
  · simp [h₁]

private theorem single_single_wightman_eq_osInner_iff_kernel_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n k : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d k)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) k) :
    WightmanInnerProduct d (bvt_W OS lgc)
        (BorchersSequence.single n φ)
        (BorchersSequence.single k ψ) =
      PositiveTimeBorchersSequence.osInner OS
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule f))
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule g))
      ↔
    bvt_W OS lgc (n + k) (φ.conjTensorProduct ψ) =
      OS.S (n + k)
        (ZeroDiagonalSchwartz.ofClassical
          ((f : SchwartzNPoint d n).osConjTensorProduct
            (g : SchwartzNPoint d k))) := by
  rw [WightmanInnerProduct_single_single (d := d) (W := bvt_W OS lgc)
      (hlin := bvt_W_linear (d := d) OS lgc) (n := n) (m := k)
      (f := φ) (g := ψ)]
  have hos :
      PositiveTimeBorchersSequence.osInner OS
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule f))
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule g)) =
      OS.S (n + k)
        (ZeroDiagonalSchwartz.ofClassical
          ((f : SchwartzNPoint d n).osConjTensorProduct
            (g : SchwartzNPoint d k))) := by
    unfold PositiveTimeBorchersSequence.osInner
    simp [EuclideanPositiveTimeComponent.toPositiveTimeSingle,
      EuclideanPositiveTimeComponent.ofSubmodule, OSInnerProduct_single_single,
      OS.E0_linear]
  rw [hos]

theorem bvt_wightmanInner_eq_transport_inner_onImage_of_kernel_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) (hGm : G.toBorchers.bound ≤ m)
    (hkernel : ∀ n k,
      n ≤ F.toBorchers.bound →
      k ≤ G.toBorchers.bound →
      bvt_W OS lgc (n + k)
        ((F.toBorchers.funcs n).conjTensorProduct (G.toBorchers.funcs k)) =
      OS.S (n + k)
        (ZeroDiagonalSchwartz.ofClassical
          (((bvtTransportImagePreimage (d := d) F n : euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n).osConjTensorProduct
            ((bvtTransportImagePreimage (d := d) G k : euclideanPositiveTimeSubmodule (d := d) k) :
              SchwartzNPoint d k)))) :
    WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers G.toBorchers =
      @inner ℂ (OSHilbertSpace OS) _
        (bvt_transport_to_osHilbert_onImage OS F)
        (bvt_transport_to_osHilbert_onImage OS G) := by
  apply bvt_wightmanInner_eq_transport_inner_onImage_of_single_single
    (d := d) (OS := OS) (lgc := lgc) (F := F) (G := G) (m := m) hFm hGm
  intro n k hn hk
  exact
    (single_single_wightman_eq_osInner_iff_kernel_eq
      (d := d) (OS := OS) (lgc := lgc)
      (φ := F.toBorchers.funcs n) (ψ := G.toBorchers.funcs k)
      (f := bvtTransportImagePreimage (d := d) F n)
      (g := bvtTransportImagePreimage (d := d) G k)).2
      (hkernel n k hn hk)

private theorem bvt_wightmanInner_self_eq_padded_double_sum
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) :
    WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers F.toBorchers =
      (Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          if h₁ : n ≤ F.toBorchers.bound then
            if h₂ : k ≤ F.toBorchers.bound then
              bvt_W OS lgc (n + k)
                ((F.toBorchers.funcs n).conjTensorProduct (F.toBorchers.funcs k))
            else 0
          else 0 := by
  have hw :
      WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers F.toBorchers =
        WightmanInnerProductN d (bvt_W OS lgc) F.toBorchers F.toBorchers
          (m + 1) (m + 1) := by
    apply WightmanInnerProduct_eq_extended (d := d) (W := bvt_W OS lgc)
      (hlin := bvt_W_linear (d := d) OS lgc)
    · exact Nat.succ_le_succ hFm
    · exact Nat.succ_le_succ hFm
  rw [hw]
  unfold WightmanInnerProductN
  refine Finset.sum_congr rfl ?_
  intro n hn
  by_cases hN : n ≤ F.toBorchers.bound
  · refine Finset.sum_congr rfl ?_
    intro k hk
    by_cases hK : k ≤ F.toBorchers.bound
    · simp [hN, hK]
    · have hkgt : F.toBorchers.bound < k := by omega
      simp [hN, hK, F.toBorchers.bound_spec k hkgt,
        (bvt_W_linear (d := d) OS lgc (n + k)).map_zero]
  · have hngt : F.toBorchers.bound < n := by omega
    simp [hN]
    apply Finset.sum_eq_zero
    intro k hk
    rw [F.toBorchers.bound_spec n hngt, SchwartzMap.conjTensorProduct_zero_left,
      (bvt_W_linear (d := d) OS lgc (n + k)).map_zero]

private theorem bvt_wightmanInner_self_eq_single_single_padded_double_sum
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) :
    WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers F.toBorchers =
      (Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          if h₁ : n ≤ F.toBorchers.bound then
            if h₂ : k ≤ F.toBorchers.bound then
              WightmanInnerProduct d (bvt_W OS lgc)
                (BorchersSequence.single n (F.toBorchers.funcs n))
                (BorchersSequence.single k (F.toBorchers.funcs k))
            else 0
          else 0 := by
  rw [bvt_wightmanInner_self_eq_padded_double_sum
    (d := d) (OS := OS) (lgc := lgc) (F := F) (m := m) hFm]
  refine Finset.sum_congr rfl ?_
  intro n hn
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h₁ : n ≤ F.toBorchers.bound
  · by_cases h₂ : k ≤ F.toBorchers.bound
    · simp [h₁, h₂, WightmanInnerProduct_single_single, bvt_W_linear]
    · simp [h₁, h₂]
  · simp [h₁]

private theorem bvt_wightmanInner_eq_transport_norm_sq_onImage_of_single_single
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m)
    (hss : ∀ n k,
      n ≤ F.toBorchers.bound →
      k ≤ F.toBorchers.bound →
      WightmanInnerProduct d (bvt_W OS lgc)
          (BorchersSequence.single n (F.toBorchers.funcs n))
          (BorchersSequence.single k (F.toBorchers.funcs k)) =
        PositiveTimeBorchersSequence.osInner OS
          (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
            (EuclideanPositiveTimeComponent.ofSubmodule
              (bvtTransportImagePreimage (d := d) F n)))
          (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
            (EuclideanPositiveTimeComponent.ofSubmodule
              (bvtTransportImagePreimage (d := d) F k)))) :
    (WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers F.toBorchers).re =
      ‖bvt_transport_to_osHilbert_onImage OS F‖ ^ 2 := by
  rw [bvt_wightmanInner_self_eq_single_single_padded_double_sum
    (d := d) (OS := OS) (lgc := lgc) (F := F) (m := m) hFm]
  rw [norm_sq_bvt_transport_to_osHilbert_onImage_eq_osInner_padded_double_sum
    (d := d) (OS := OS) (F := F) (m := m) hFm]
  have hsum :
      ((Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          if h₁ : n ≤ F.toBorchers.bound then
            if h₂ : k ≤ F.toBorchers.bound then
              WightmanInnerProduct d (bvt_W OS lgc)
                (BorchersSequence.single n (F.toBorchers.funcs n))
                (BorchersSequence.single k (F.toBorchers.funcs k))
            else 0
          else 0) =
      ((Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          if h₁ : n ≤ F.toBorchers.bound then
            if h₂ : k ≤ F.toBorchers.bound then
              PositiveTimeBorchersSequence.osInner OS
                (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F n)))
                (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F k)))
            else 0
          else 0) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    refine Finset.sum_congr rfl ?_
    intro k hk
    by_cases h₁ : n ≤ F.toBorchers.bound
    · by_cases h₂ : k ≤ F.toBorchers.bound
      · simp [h₁, h₂, hss n k h₁ h₂]
      · simp [h₁, h₂]
    · simp [h₁]
  exact congrArg Complex.re hsum

theorem bvt_wightmanInner_eq_transport_norm_sq_onImage_of_kernel_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m)
    (hkernel : ∀ n k,
      n ≤ F.toBorchers.bound →
      k ≤ F.toBorchers.bound →
      bvt_W OS lgc (n + k)
        ((F.toBorchers.funcs n).conjTensorProduct (F.toBorchers.funcs k)) =
      OS.S (n + k)
        (ZeroDiagonalSchwartz.ofClassical
          (((bvtTransportImagePreimage (d := d) F n : euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n).osConjTensorProduct
            ((bvtTransportImagePreimage (d := d) F k : euclideanPositiveTimeSubmodule (d := d) k) :
              SchwartzNPoint d k)))) :
    (WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers F.toBorchers).re =
      ‖bvt_transport_to_osHilbert_onImage OS F‖ ^ 2 := by
  apply bvt_wightmanInner_eq_transport_norm_sq_onImage_of_single_single
    (d := d) (OS := OS) (lgc := lgc) (F := F) (m := m) hFm
  intro n k hn hk
  exact
    (single_single_wightman_eq_osInner_iff_kernel_eq
      (d := d) (OS := OS) (lgc := lgc)
      (φ := F.toBorchers.funcs n) (ψ := F.toBorchers.funcs k)
      (f := bvtTransportImagePreimage (d := d) F n)
      (g := bvtTransportImagePreimage (d := d) F k)).2
      (hkernel n k hn hk)

/-- Once the Stage-5 matrix-element kernel equality is available on the
transformed-image carrier, positivity on that carrier is immediate: the
reconstructed Wightman quadratic form is already identified with the square
norm of the transported OS Hilbert-space vector. -/
theorem bvt_wightmanInner_self_nonneg_onImage_of_kernel_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m)
    (hkernel : ∀ n k,
      n ≤ F.toBorchers.bound →
      k ≤ F.toBorchers.bound →
      bvt_W OS lgc (n + k)
        ((F.toBorchers.funcs n).conjTensorProduct (F.toBorchers.funcs k)) =
      OS.S (n + k)
        (ZeroDiagonalSchwartz.ofClassical
          (((bvtTransportImagePreimage (d := d) F n : euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n).osConjTensorProduct
            ((bvtTransportImagePreimage (d := d) F k : euclideanPositiveTimeSubmodule (d := d) k) :
              SchwartzNPoint d k)))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers F.toBorchers).re := by
  rw [bvt_wightmanInner_eq_transport_norm_sq_onImage_of_kernel_eq
    (d := d) (OS := OS) (lgc := lgc) (F := F) (m := m) hFm hkernel]
  exact sq_nonneg ‖bvt_transport_to_osHilbert_onImage OS F‖

/-- Package-I seam reducer on the transformed-image core: once the `k = 0`
matrix elements are supplied separately and every positive-degree right factor
admits the honest Lemma-4.2 time-interchange witness, the on-image positivity
statement follows formally from the existing transport norm-square theorem.

This theorem does not claim the remaining analytic work is finished. Its role
is to move the live seam from a raw kernel family to the exact split dictated by
the current blueprint:
1. a dedicated zero-right kernel input,
2. positive-degree matrix-element time interchange on the transformed-image
   carrier,
3. then Package-I positivity on that carrier. -/
theorem bvt_W_matrixElement_onImage_of_repr_eq_transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d)
    (hambientCompact : ∀ n, n ≤ F.toBorchers.bound →
      HasCompactSupport
        ((((F.toBorchers.funcs n : SchwartzNPoint d n) :
            NPointDomain d n → ℂ))))
    (hzero : ∀ n, n ≤ F.toBorchers.bound →
      bvt_W OS lgc (n + 0)
        ((F.toBorchers.funcs n).conjTensorProduct (F.toBorchers.funcs 0)) =
      OS.S (n + 0)
        (ZeroDiagonalSchwartz.ofClassical
          ((((bvtTransportImagePreimage (d := d) F n :
                euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n).osConjTensorProduct
            ((bvtTransportImagePreimage (d := d) F 0 :
                euclideanPositiveTimeSubmodule (d := d) 0) :
              SchwartzNPoint d 0)))))
    (hpair :
      ∀ n k, n ≤ F.toBorchers.bound → k ≤ F.toBorchers.bound → (hk_pos : 0 < k) →
        ∃ f : euclideanPositiveTimeSubmodule (d := d) n,
          os1TransportComponent d n f =
            section43PositiveEnergyQuotientMap (d := d) n (F.toBorchers.funcs n) ∧
          HasCompactSupport (((f : SchwartzNPoint d n) : NPointDomain d n → ℂ)) ∧
          ∃ g : euclideanPositiveTimeSubmodule (d := d) k,
            os1TransportComponent d k g =
              section43PositiveEnergyQuotientMap (d := d) k (F.toBorchers.funcs k) ∧
            HasCompactSupport (((g : SchwartzNPoint d k) : NPointDomain d k → ℂ)) ∧
            ∃ H : ℂ → ℂ,
              (∀ t : ℝ, 0 < t →
                H ((t : ℂ) * Complex.I) =
                  OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                    (PositiveTimeBorchersSequence.single n
                      ((f : euclideanPositiveTimeSubmodule (d := d) n) :
                        SchwartzNPoint d n) f.2)
                    (PositiveTimeBorchersSequence.single k
                      ((g : euclideanPositiveTimeSubmodule (d := d) k) :
                        SchwartzNPoint d k) g.2) (t : ℂ)) ∧
              (∀ t : ℝ, 0 < t →
                Filter.Tendsto
                  (fun ε : ℝ =>
                    ∫ y : NPointDomain d (n + k),
                      bvt_F OS lgc (n + k)
                        (xiShift ⟨n, Nat.lt_add_of_pos_right hk_pos⟩ 0
                          (fun j μ =>
                            ↑(y j μ) +
                              ε * ↑(canonicalForwardConeDirection (d := d) (n + k) j μ) *
                                Complex.I)
                          (t : ℂ)) *
                        ((F.toBorchers.funcs n).conjTensorProduct
                          (F.toBorchers.funcs k)) y)
                  (nhdsWithin 0 (Set.Ioi 0))
                  (nhds (H ((t : ℂ) * Complex.I))))) :
    ∀ n k, n ≤ F.toBorchers.bound → k ≤ F.toBorchers.bound →
      bvt_W OS lgc (n + k)
        ((F.toBorchers.funcs n).conjTensorProduct (F.toBorchers.funcs k)) =
      OS.S (n + k)
        (ZeroDiagonalSchwartz.ofClassical
          ((((bvtTransportImagePreimage (d := d) F n :
                euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n).osConjTensorProduct
            ((bvtTransportImagePreimage (d := d) F k :
                euclideanPositiveTimeSubmodule (d := d) k) :
              SchwartzNPoint d k)))) := by
  intro n k hn hk
  by_cases hk0 : k = 0
  · subst hk0
    simpa using hzero n hn
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
    rcases hpair n k hn hk hk_pos with ⟨f, hf_repr, hf_compact, g, hg_repr, hg_compact, H,
      hH_imag_os, hlimit⟩
    exact lemma42_matrix_element_time_interchange_onImage_of_repr_eq_transport
      (d := d) (OS := OS) (lgc := lgc) (F := F) (n := n) (k := k) hk_pos
      f hf_repr hf_compact g hg_repr hg_compact (hambientCompact k hk) H hH_imag_os hlimit

/-- Public on-image positivity theorem on the exact explicit representation
surface required by the current theorem-3 boundary-vanishing reduction. Once a
transformed-image target comes equipped with:
1. ambient compact support on the active finite degree range,
2. the separate `k = 0` kernel identity,
3. positive-degree representative data together with the honest Lemma-4.2
   time-interchange witnesses,
then the reconstructed quadratic form is nonnegative on that on-image target. -/
theorem bvt_wightmanInner_self_nonneg_onImage_of_repr_eq_transport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m)
    (repr : ∀ n, euclideanPositiveTimeSubmodule (d := d) n)
    (hrepr : ∀ n,
      os1TransportComponent d n (repr n) =
        section43PositiveEnergyQuotientMap (d := d) n (F.toBorchers.funcs n))
    (hambientCompact : ∀ n, n ≤ F.toBorchers.bound →
      HasCompactSupport
        ((((F.toBorchers.funcs n : SchwartzNPoint d n) :
            NPointDomain d n → ℂ))))
    (hreprCompact : ∀ n, n ≤ F.toBorchers.bound →
      HasCompactSupport ((((repr n : euclideanPositiveTimeSubmodule (d := d) n) :
        SchwartzNPoint d n) : NPointDomain d n → ℂ)))
    (hzero : ∀ n, n ≤ F.toBorchers.bound →
      bvt_W OS lgc (n + 0)
        ((F.toBorchers.funcs n).conjTensorProduct (F.toBorchers.funcs 0)) =
      OS.S (n + 0)
        (ZeroDiagonalSchwartz.ofClassical
          ((((repr n : euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n).osConjTensorProduct
            ((repr 0 : euclideanPositiveTimeSubmodule (d := d) 0) :
              SchwartzNPoint d 0)))))
    (hpair :
      ∀ n k, n ≤ F.toBorchers.bound → k ≤ F.toBorchers.bound → (hk_pos : 0 < k) →
        ∃ H : ℂ → ℂ,
          (∀ t : ℝ, 0 < t →
            H ((t : ℂ) * Complex.I) =
              OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n
                  ((repr n : euclideanPositiveTimeSubmodule (d := d) n) :
                    SchwartzNPoint d n)
                  (repr n).2)
                (PositiveTimeBorchersSequence.single k
                  ((repr k : euclideanPositiveTimeSubmodule (d := d) k) :
                    SchwartzNPoint d k)
                  (repr k).2) (t : ℂ)) ∧
          (∀ t : ℝ, 0 < t →
            Filter.Tendsto
              (fun ε : ℝ =>
                ∫ y : NPointDomain d (n + k),
                  bvt_F OS lgc (n + k)
                    (xiShift ⟨n, Nat.lt_add_of_pos_right hk_pos⟩ 0
                      (fun j μ =>
                        ↑(y j μ) +
                          ε * ↑(canonicalForwardConeDirection (d := d) (n + k) j μ) *
                            Complex.I)
                      (t : ℂ)) *
                    ((F.toBorchers.funcs n).conjTensorProduct
                      (F.toBorchers.funcs k)) y)
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds (H ((t : ℂ) * Complex.I))))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers F.toBorchers).re := by
  have hrepr_eq :
      ∀ n, repr n = bvtTransportImagePreimage (d := d) F n := by
    intro n
    apply os1TransportComponent_injective (d := d) (n := n)
    rw [hrepr n, bvtTransportImagePreimage_spec]
  have hzero' : ∀ n, n ≤ F.toBorchers.bound →
      bvt_W OS lgc (n + 0)
        ((F.toBorchers.funcs n).conjTensorProduct (F.toBorchers.funcs 0)) =
      OS.S (n + 0)
        (ZeroDiagonalSchwartz.ofClassical
          ((((bvtTransportImagePreimage (d := d) F n :
                euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n).osConjTensorProduct
            ((bvtTransportImagePreimage (d := d) F 0 :
                euclideanPositiveTimeSubmodule (d := d) 0) :
              SchwartzNPoint d 0)))) := by
    intro n hn
    simpa [hrepr_eq n, hrepr_eq 0] using hzero n hn
  apply bvt_wightmanInner_self_nonneg_onImage_of_kernel_eq
    (d := d) (OS := OS) (lgc := lgc) (F := F) (m := m) hFm
  exact bvt_W_matrixElement_onImage_of_repr_eq_transport
    (d := d) (OS := OS) (lgc := lgc) (F := F) hambientCompact hzero' (by
      intro n k hn hk hk_pos
      rcases hpair n k hn hk hk_pos with ⟨H, hH_imag_os, hlimit⟩
      exact ⟨repr n, hrepr n, hreprCompact n hn, repr k, hrepr k, hreprCompact k hk,
        H, hH_imag_os, hlimit⟩)

/-- Package-I seam reducer on the transformed-image core: once the `k = 0`
matrix elements are supplied separately and every positive-degree right factor
admits the honest Lemma-4.2 time-interchange witness, the on-image positivity
statement follows formally from the existing transport norm-square theorem.

This theorem packages the special case where those witnesses are already stated
using the canonical chosen preimages `bvtTransportImagePreimage`. -/
theorem bvt_W_matrixElement_onImage
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d)
    (hprecompact : ∀ n, n ≤ F.toBorchers.bound →
      HasCompactSupport
        ((((bvtTransportImagePreimage (d := d) F n :
              euclideanPositiveTimeSubmodule (d := d) n) :
            SchwartzNPoint d n) : NPointDomain d n → ℂ)))
    (hambientCompact : ∀ n, n ≤ F.toBorchers.bound →
      HasCompactSupport
        ((((F.toBorchers.funcs n : SchwartzNPoint d n) :
            NPointDomain d n → ℂ))))
    (hzero : ∀ n, n ≤ F.toBorchers.bound →
      bvt_W OS lgc (n + 0)
        ((F.toBorchers.funcs n).conjTensorProduct (F.toBorchers.funcs 0)) =
      OS.S (n + 0)
        (ZeroDiagonalSchwartz.ofClassical
          ((((bvtTransportImagePreimage (d := d) F n :
                euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n).osConjTensorProduct
            ((bvtTransportImagePreimage (d := d) F 0 :
                euclideanPositiveTimeSubmodule (d := d) 0) :
              SchwartzNPoint d 0)))))
    (hpair :
      ∀ n k, n ≤ F.toBorchers.bound → k ≤ F.toBorchers.bound → (hk_pos : 0 < k) →
        ∃ H : ℂ → ℂ,
          (∀ t : ℝ, 0 < t →
            H ((t : ℂ) * Complex.I) =
              OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n
                  ((bvtTransportImagePreimage (d := d) F n :
                      euclideanPositiveTimeSubmodule (d := d) n) :
                    SchwartzNPoint d n)
                  (bvtTransportImagePreimage (d := d) F n).2)
                (PositiveTimeBorchersSequence.single k
                  ((bvtTransportImagePreimage (d := d) F k :
                      euclideanPositiveTimeSubmodule (d := d) k) :
                    SchwartzNPoint d k)
                  (bvtTransportImagePreimage (d := d) F k).2) (t : ℂ)) ∧
          (∀ t : ℝ, 0 < t →
            Filter.Tendsto
              (fun ε : ℝ =>
                ∫ y : NPointDomain d (n + k),
                  bvt_F OS lgc (n + k)
                    (xiShift ⟨n, Nat.lt_add_of_pos_right hk_pos⟩ 0
                      (fun j μ =>
                        ↑(y j μ) +
                          ε * ↑(canonicalForwardConeDirection (d := d) (n + k) j μ) *
                            Complex.I)
                      (t : ℂ)) *
                    ((F.toBorchers.funcs n).conjTensorProduct
                      (F.toBorchers.funcs k)) y)
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds (H ((t : ℂ) * Complex.I))))) :
    ∀ n k, n ≤ F.toBorchers.bound → k ≤ F.toBorchers.bound →
      bvt_W OS lgc (n + k)
        ((F.toBorchers.funcs n).conjTensorProduct (F.toBorchers.funcs k)) =
      OS.S (n + k)
        (ZeroDiagonalSchwartz.ofClassical
          ((((bvtTransportImagePreimage (d := d) F n :
                euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n).osConjTensorProduct
            ((bvtTransportImagePreimage (d := d) F k :
                euclideanPositiveTimeSubmodule (d := d) k) :
              SchwartzNPoint d k)))) := by
  refine bvt_W_matrixElement_onImage_of_repr_eq_transport
    (d := d) (OS := OS) (lgc := lgc) (F := F) hambientCompact hzero ?_
  intro n k hn hk hk_pos
  refine ⟨bvtTransportImagePreimage (d := d) F n, ?_, hprecompact n hn,
    bvtTransportImagePreimage (d := d) F k, ?_, hprecompact k hk, ?_⟩
  · exact bvtTransportImagePreimage_spec (d := d) (F := F) n
  · exact bvtTransportImagePreimage_spec (d := d) (F := F) k
  · rcases hpair n k hn hk hk_pos with ⟨H, hH_imag_os, hlimit⟩
    exact ⟨H, hH_imag_os, hlimit⟩

/-- The `k = 0` supplier required by the on-image Package-I closure is
automatic as soon as the ambient degree-`0` component itself vanishes. This
isolates the exact extra datum still missing from a positive-degree
boundary-vanishing surrogate: the positive-degree hypothesis does not control
`F.funcs 0`, but if that degree-`0` term is separately zero then the whole
zero-right comparison collapses formally on both the Wightman and OS sides. -/
theorem bvt_zero_right_onImage_of_component_zero
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d)
    (hF0 : (F.toBorchers.funcs 0 : SchwartzNPoint d 0) = 0) :
    ∀ n, n ≤ F.toBorchers.bound →
      bvt_W OS lgc (n + 0)
        ((F.toBorchers.funcs n).conjTensorProduct (F.toBorchers.funcs 0)) =
      OS.S (n + 0)
        (ZeroDiagonalSchwartz.ofClassical
          ((((bvtTransportImagePreimage (d := d) F n :
                euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n).osConjTensorProduct
            ((bvtTransportImagePreimage (d := d) F 0 :
                euclideanPositiveTimeSubmodule (d := d) 0) :
              SchwartzNPoint d 0)))) := by
  have hpre0_transport :
      os1TransportComponent d 0 (bvtTransportImagePreimage (d := d) F 0) = 0 := by
    simpa [hF0] using bvtTransportImagePreimage_spec (d := d) (F := F) 0
  have hpre0 :
      bvtTransportImagePreimage (d := d) F 0 = 0 :=
    (os1TransportComponent_eq_zero_iff d 0
      (bvtTransportImagePreimage (d := d) F 0)).mp hpre0_transport
  intro n hn
  have hzeroDiag :
      ZeroDiagonalSchwartz.ofClassical
        ((((bvtTransportImagePreimage (d := d) F n :
              euclideanPositiveTimeSubmodule (d := d) n) :
            SchwartzNPoint d n).osConjTensorProduct
          ((bvtTransportImagePreimage (d := d) F 0 :
              euclideanPositiveTimeSubmodule (d := d) 0) :
            SchwartzNPoint d 0))) = 0 := by
    have hclassical :
        ((((bvtTransportImagePreimage (d := d) F n :
              euclideanPositiveTimeSubmodule (d := d) n) :
            SchwartzNPoint d n).osConjTensorProduct
          ((bvtTransportImagePreimage (d := d) F 0 :
              euclideanPositiveTimeSubmodule (d := d) 0) :
            SchwartzNPoint d 0))) = 0 := by
      simp [hpre0, SchwartzNPoint.osConjTensorProduct_zero_right]
    rw [hclassical, ZeroDiagonalSchwartz.ofClassical_zero]
  calc
    bvt_W OS lgc (n + 0)
        ((F.toBorchers.funcs n).conjTensorProduct (F.toBorchers.funcs 0)) =
      bvt_W OS lgc (n + 0)
        ((F.toBorchers.funcs n).conjTensorProduct (0 : SchwartzNPoint d 0)) := by
          simp [hF0]
    _ = 0 := by
          rw [SchwartzMap.conjTensorProduct_zero_right,
            (bvt_W_linear (d := d) OS lgc (n + 0)).map_zero]
    _ = OS.S (n + 0) 0 := by
          symm
          exact (OS.E0_linear (n + 0)).map_zero
    _ = OS.S (n + 0)
        (ZeroDiagonalSchwartz.ofClassical
          ((((bvtTransportImagePreimage (d := d) F n :
                euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n).osConjTensorProduct
            ((bvtTransportImagePreimage (d := d) F 0 :
                euclideanPositiveTimeSubmodule (d := d) 0) :
              SchwartzNPoint d 0)))) := by
          rw [hzeroDiag]

theorem bvt_wightmanInner_self_nonneg_onImage_of_zero_right_and_matrix_element_time_interchange
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m)
    (hprecompact : ∀ n, n ≤ F.toBorchers.bound →
      HasCompactSupport
        ((((bvtTransportImagePreimage (d := d) F n :
              euclideanPositiveTimeSubmodule (d := d) n) :
            SchwartzNPoint d n) : NPointDomain d n → ℂ)))
    (hambientCompact : ∀ n, n ≤ F.toBorchers.bound →
      HasCompactSupport
        ((((F.toBorchers.funcs n : SchwartzNPoint d n) :
            NPointDomain d n → ℂ))))
    (hzero : ∀ n, n ≤ F.toBorchers.bound →
      bvt_W OS lgc (n + 0)
        ((F.toBorchers.funcs n).conjTensorProduct (F.toBorchers.funcs 0)) =
      OS.S (n + 0)
        (ZeroDiagonalSchwartz.ofClassical
          ((((bvtTransportImagePreimage (d := d) F n :
                euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n).osConjTensorProduct
            ((bvtTransportImagePreimage (d := d) F 0 :
                euclideanPositiveTimeSubmodule (d := d) 0) :
              SchwartzNPoint d 0)))))
    (hpair :
      ∀ n k, n ≤ F.toBorchers.bound → k ≤ F.toBorchers.bound → (hk_pos : 0 < k) →
        ∃ H : ℂ → ℂ,
          (∀ t : ℝ, 0 < t →
            H ((t : ℂ) * Complex.I) =
              OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n
                  ((bvtTransportImagePreimage (d := d) F n :
                      euclideanPositiveTimeSubmodule (d := d) n) :
                    SchwartzNPoint d n)
                  (bvtTransportImagePreimage (d := d) F n).2)
                (PositiveTimeBorchersSequence.single k
                  ((bvtTransportImagePreimage (d := d) F k :
                      euclideanPositiveTimeSubmodule (d := d) k) :
                    SchwartzNPoint d k)
                  (bvtTransportImagePreimage (d := d) F k).2) (t : ℂ)) ∧
          (∀ t : ℝ, 0 < t →
            Filter.Tendsto
              (fun ε : ℝ =>
                ∫ y : NPointDomain d (n + k),
                  bvt_F OS lgc (n + k)
                    (xiShift ⟨n, Nat.lt_add_of_pos_right hk_pos⟩ 0
                      (fun j μ =>
                        ↑(y j μ) +
                          ε * ↑(canonicalForwardConeDirection (d := d) (n + k) j μ) *
                            Complex.I)
                      (t : ℂ)) *
                    ((F.toBorchers.funcs n).conjTensorProduct
                      (F.toBorchers.funcs k)) y)
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds (H ((t : ℂ) * Complex.I))))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers F.toBorchers).re := by
  apply bvt_wightmanInner_self_nonneg_onImage_of_repr_eq_transport
    (d := d) (OS := OS) (lgc := lgc) (F := F) (m := m) hFm
    (repr := bvtTransportImagePreimage (d := d) F)
    (hrepr := bvtTransportImagePreimage_spec (d := d) (F := F))
    hambientCompact hprecompact hzero hpair

/-- Family-level bridge into the exact per-approximant nonnegativity input used
downstream by the current theorem-3 boundary-vanishing target. For a fixed
candidate transformed-image family `G`, the already available per-approximant
on-image positivity theorem
`bvt_wightmanInner_self_nonneg_onImage_of_zero_right_and_matrix_element_time_interchange`
can be applied pointwise, yielding precisely the required conclusion
`∀ N, 0 ≤ Re ⟪G N, G N⟫`.

This remains strictly a family-level zero-right / matrix-element consumer: it
does not reconstruct `OrderedPositiveTimeRegion` hypotheses or re-enter the
`PositiveTimeBorchersSequence.osInner` positivity lane. -/
theorem bvt_wightmanInner_self_nonneg_family_onImage_of_zero_right_and_matrix_element_time_interchange
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (G : ℕ → BvtTransportImageSequence d) {m : ℕ}
    (hG : ∀ N, (G N).toBorchers.bound ≤ m)
    (hprecompact : ∀ N n, n ≤ (G N).toBorchers.bound →
      HasCompactSupport
        ((((bvtTransportImagePreimage (d := d) (G N) n :
              euclideanPositiveTimeSubmodule (d := d) n) :
            SchwartzNPoint d n) : NPointDomain d n → ℂ)))
    (hambientCompact : ∀ N n, n ≤ (G N).toBorchers.bound →
      HasCompactSupport
        ((((G N).toBorchers.funcs n : SchwartzNPoint d n) :
            NPointDomain d n → ℂ)))
    (hzero : ∀ N n, n ≤ (G N).toBorchers.bound →
      bvt_W OS lgc (n + 0)
        (((G N).toBorchers.funcs n).conjTensorProduct ((G N).toBorchers.funcs 0)) =
      OS.S (n + 0)
        (ZeroDiagonalSchwartz.ofClassical
          ((((bvtTransportImagePreimage (d := d) (G N) n :
                euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n).osConjTensorProduct
            ((bvtTransportImagePreimage (d := d) (G N) 0 :
                euclideanPositiveTimeSubmodule (d := d) 0) :
              SchwartzNPoint d 0)))))
    (hpair :
      ∀ N n k, n ≤ (G N).toBorchers.bound → k ≤ (G N).toBorchers.bound → (hk_pos : 0 < k) →
        ∃ H : ℂ → ℂ,
          (∀ t : ℝ, 0 < t →
            H ((t : ℂ) * Complex.I) =
              OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n
                  ((bvtTransportImagePreimage (d := d) (G N) n :
                      euclideanPositiveTimeSubmodule (d := d) n) :
                    SchwartzNPoint d n)
                  (bvtTransportImagePreimage (d := d) (G N) n).2)
                (PositiveTimeBorchersSequence.single k
                  ((bvtTransportImagePreimage (d := d) (G N) k :
                      euclideanPositiveTimeSubmodule (d := d) k) :
                    SchwartzNPoint d k)
                  (bvtTransportImagePreimage (d := d) (G N) k).2) (t : ℂ)) ∧
          (∀ t : ℝ, 0 < t →
            Filter.Tendsto
              (fun ε : ℝ =>
                ∫ y : NPointDomain d (n + k),
                  bvt_F OS lgc (n + k)
                    (xiShift ⟨n, Nat.lt_add_of_pos_right hk_pos⟩ 0
                      (fun j μ =>
                        ↑(y j μ) +
                          ε * ↑(canonicalForwardConeDirection (d := d) (n + k) j μ) *
                            Complex.I)
                      (t : ℂ)) *
                    (((G N).toBorchers.funcs n).conjTensorProduct
                      ((G N).toBorchers.funcs k)) y)
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds (H ((t : ℂ) * Complex.I))))) :
    ∀ N,
      0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
        (G N).toBorchers (G N).toBorchers).re := by
  intro N
  exact bvt_wightmanInner_self_nonneg_onImage_of_zero_right_and_matrix_element_time_interchange
    (d := d) (OS := OS) (lgc := lgc) (F := G N) (m := m) (hFm := hG N)
    (hprecompact := hprecompact N) (hambientCompact := hambientCompact N)
    (hzero := hzero N) (hpair := hpair N)

/-- Family-level recovery of the `k = 0` on-image supplier from the strictly
smaller datum that every approximant has zero degree-`0` component. This is
the exact missing information not forced by positive-degree boundary vanishing
of the fixed surrogate `F₀`. -/
theorem bvt_zero_right_family_onImage_of_component_zero
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (G : ℕ → BvtTransportImageSequence d)
    (hG0 : ∀ N, ((G N).toBorchers.funcs 0 : SchwartzNPoint d 0) = 0) :
    ∀ N n, n ≤ (G N).toBorchers.bound →
      bvt_W OS lgc (n + 0)
        (((G N).toBorchers.funcs n).conjTensorProduct ((G N).toBorchers.funcs 0)) =
      OS.S (n + 0)
        (ZeroDiagonalSchwartz.ofClassical
          ((((bvtTransportImagePreimage (d := d) (G N) n :
                euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n).osConjTensorProduct
            ((bvtTransportImagePreimage (d := d) (G N) 0 :
                euclideanPositiveTimeSubmodule (d := d) 0) :
              SchwartzNPoint d 0)))) := by
  intro N n hn
  exact bvt_zero_right_onImage_of_component_zero
    (d := d) (OS := OS) (lgc := lgc) (F := G N) (hF0 := hG0 N) n hn

private theorem borchersConj_continuous_onImage {n : ℕ} :
    Continuous (fun f : SchwartzNPoint d n => f.borchersConj) := by
  let revCLE : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
    { toFun := fun y i => y (Fin.rev i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun y i => y (Fin.rev i)
      left_inv := fun y => funext fun i => by simp [Fin.rev_rev]
      right_inv := fun y => funext fun i => by simp [Fin.rev_rev]
      continuous_toFun := by
        apply continuous_pi
        intro i
        exact continuous_apply (Fin.rev i)
      continuous_invFun := by
        apply continuous_pi
        intro i
        exact continuous_apply (Fin.rev i) }
  let revCLM : SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ revCLE
  have hrev : ∀ f : SchwartzNPoint d n, revCLM f = f.reverse := by
    intro f
    ext x
    simp [revCLM, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      SchwartzMap.reverse_apply, revCLE]
  have hconj_cont : Continuous (fun f : SchwartzNPoint d n => f.conj) := by
    let conjL : SchwartzNPoint d n →ₗ[ℝ] SchwartzNPoint d n :=
      { toFun := SchwartzMap.conj
        map_add' := fun f g => by
          ext x
          simp [SchwartzMap.conj_apply]
        map_smul' := fun c f => by
          simpa using (SchwartzMap.conj_smul (c := (c : ℂ)) f) }
    exact Seminorm.continuous_from_bounded
      (schwartz_withSeminorms ℝ (NPointDomain d n) ℂ)
      (schwartz_withSeminorms ℝ (NPointDomain d n) ℂ)
      conjL (fun q => by
        rcases q with ⟨k, l⟩
        refine ⟨{(k, l)}, 1, ?_⟩
        intro f
        simpa [Finset.sup_singleton] using SchwartzMap.seminorm_conj_le k l f)
  show Continuous (fun f => (revCLM f).conj)
  exact hconj_cont.comp revCLM.continuous |>.congr (fun f => by
    show (revCLM f).conj = f.borchersConj
    rw [hrev]
    rfl)

private theorem conjTensorProduct_continuous_onImage {n m : ℕ} :
    Continuous
      (fun p : SchwartzNPoint d n × SchwartzNPoint d m => p.1.conjTensorProduct p.2) := by
  have hpair :
      Continuous
        (fun p : SchwartzNPoint d n × SchwartzNPoint d m =>
          (p.1.borchersConj, p.2)) :=
    ((borchersConj_continuous_onImage (d := d)).comp continuous_fst).prodMk continuous_snd
  let h :
      Continuous
        (fun p : SchwartzNPoint d n × SchwartzNPoint d m =>
          p.1.borchersConj.tensorProduct p.2) :=
    SchwartzMap.tensorProduct_continuous.comp hpair
  simpa [SchwartzMap.conjTensorProduct] using h

/-- Fixed-bound finite-support continuity for the reconstructed Wightman
quadratic form. This is the exact Step-4 continuity input needed by the final
Package-I closure: if a bounded family of Borchers sequences converges
componentwise on the active finite degree range, then the corresponding
quadratic forms converge as well. -/
theorem tendsto_bvt_wightmanInner_self_of_bounded_componentwise_tendsto
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d) (G : ℕ → BorchersSequence d) {m : ℕ}
    (hF : F.bound ≤ m)
    (hG : ∀ N, (G N).bound ≤ m)
    (hcomp : ∀ n, n ≤ m →
      Filter.Tendsto
        (fun N : ℕ => ((G N).funcs n : SchwartzNPoint d n))
        Filter.atTop
        (nhds (F.funcs n))) :
    Filter.Tendsto
      (fun N : ℕ => WightmanInnerProduct d (bvt_W OS lgc) (G N) (G N))
      Filter.atTop
      (nhds (WightmanInnerProduct d (bvt_W OS lgc) F F)) := by
  have houter :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ n ∈ Finset.range (m + 1),
            ∑ k ∈ Finset.range (m + 1),
              bvt_W OS lgc (n + k)
                ((((G N).funcs n : SchwartzNPoint d n).conjTensorProduct
                  ((G N).funcs k : SchwartzNPoint d k))))
        Filter.atTop
        (nhds
          (∑ n ∈ Finset.range (m + 1),
            ∑ k ∈ Finset.range (m + 1),
              bvt_W OS lgc (n + k)
                ((((F.funcs n : SchwartzNPoint d n).conjTensorProduct
                  (F.funcs k : SchwartzNPoint d k)))))) := by
    refine tendsto_finset_sum _ (fun n hn => ?_)
    refine tendsto_finset_sum _ (fun k hk => ?_)
    have hpair :
        Filter.Tendsto
          (fun N : ℕ =>
            (((G N).funcs n : SchwartzNPoint d n),
              ((G N).funcs k : SchwartzNPoint d k)))
          Filter.atTop
          (nhds
            (((F.funcs n : SchwartzNPoint d n),
              (F.funcs k : SchwartzNPoint d k)))) := by
      exact (hcomp n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))).prodMk_nhds
        (hcomp k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
    have hcont :
        Continuous
          (fun p : SchwartzNPoint d n × SchwartzNPoint d k =>
            bvt_W OS lgc (n + k) (p.1.conjTensorProduct p.2)) :=
      (bvt_W_continuous (d := d) OS lgc (n + k)).comp
        (conjTensorProduct_continuous_onImage (d := d) (n := n) (m := k))
    simpa using
      (hcont.tendsto
        (((F.funcs n : SchwartzNPoint d n), (F.funcs k : SchwartzNPoint d k)))).comp hpair
  have hF_eq :
      WightmanInnerProduct d (bvt_W OS lgc) F F =
        ∑ n ∈ Finset.range (m + 1),
          ∑ k ∈ Finset.range (m + 1),
            bvt_W OS lgc (n + k)
              ((((F.funcs n : SchwartzNPoint d n).conjTensorProduct
                (F.funcs k : SchwartzNPoint d k)))) := by
    rw [WightmanInnerProduct_eq_extended (d := d) (W := bvt_W OS lgc)
      (hlin := bvt_W_linear (d := d) OS lgc) (F := F) (G := F) (N₁ := m + 1) (N₂ := m + 1)]
    · rfl
    · exact Nat.succ_le_succ hF
    · exact Nat.succ_le_succ hF
  have hG_eq :
      ∀ N : ℕ,
        WightmanInnerProduct d (bvt_W OS lgc) (G N) (G N) =
          ∑ n ∈ Finset.range (m + 1),
            ∑ k ∈ Finset.range (m + 1),
              bvt_W OS lgc (n + k)
                ((((G N).funcs n : SchwartzNPoint d n).conjTensorProduct
                  ((G N).funcs k : SchwartzNPoint d k))) := by
    intro N
    rw [WightmanInnerProduct_eq_extended (d := d) (W := bvt_W OS lgc)
      (hlin := bvt_W_linear (d := d) OS lgc) (F := G N) (G := G N)
      (N₁ := m + 1) (N₂ := m + 1)]
    · rfl
    · exact Nat.succ_le_succ (hG N)
    · exact Nat.succ_le_succ (hG N)
  have hfun :
      (fun N : ℕ => WightmanInnerProduct d (bvt_W OS lgc) (G N) (G N)) =
        (fun N : ℕ =>
          ∑ n ∈ Finset.range (m + 1),
            ∑ k ∈ Finset.range (m + 1),
              bvt_W OS lgc (n + k)
                ((((G N).funcs n : SchwartzNPoint d n).conjTensorProduct
                  ((G N).funcs k : SchwartzNPoint d k)))) := by
    funext N
    exact hG_eq N
  rw [hfun]
  simpa [hF_eq] using houter

/-- Exact closure reduction from on-image positivity along a bounded
finite-support approximation family. This isolates the remaining public
`bvt_W_positive` seam to the existence of such on-image approximants and the
matrix-element inputs already packaged upstream in Stage 5. -/
theorem bvt_wightmanInner_self_nonneg_of_bounded_onImage_approx
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d) {m : ℕ}
    (hF : F.bound ≤ m)
    (G : ℕ → BvtTransportImageSequence d)
    (hG : ∀ N, (G N).toBorchers.bound ≤ m)
    (hcomp : ∀ n, n ≤ m →
      Filter.Tendsto
        (fun N : ℕ => (((G N).toBorchers.funcs n : SchwartzNPoint d n)))
        Filter.atTop
        (nhds (F.funcs n)))
    (hcore : ∀ N,
      0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
        (G N).toBorchers (G N).toBorchers).re) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
  have ht :
      Filter.Tendsto
        (fun N : ℕ =>
          WightmanInnerProduct d (bvt_W OS lgc) (G N).toBorchers (G N).toBorchers)
        Filter.atTop
        (nhds (WightmanInnerProduct d (bvt_W OS lgc) F F)) :=
    tendsto_bvt_wightmanInner_self_of_bounded_componentwise_tendsto
      (d := d) (OS := OS) (lgc := lgc) (F := F)
      (G := fun N => (G N).toBorchers) (m := m) hF hG hcomp
  have htre :
      Filter.Tendsto
        (fun N : ℕ =>
          (WightmanInnerProduct d (bvt_W OS lgc) (G N).toBorchers (G N).toBorchers).re)
        Filter.atTop
        (nhds ((WightmanInnerProduct d (bvt_W OS lgc) F F).re)) :=
    Complex.continuous_re.tendsto _ |>.comp ht
  have hmem :
      ∀ᶠ N : ℕ in Filter.atTop,
        (WightmanInnerProduct d (bvt_W OS lgc) (G N).toBorchers (G N).toBorchers).re ∈
          Set.Ici (0 : ℝ) :=
    Filter.Eventually.of_forall fun N => hcore N
  exact IsClosed.mem_of_tendsto isClosed_Ici htre hmem

/-- Public closure reducer for the remaining theorem-3 seam. If a public
Borchers target `F` can first be identified with a boundary-vanishing surrogate
`F₀` at the level of the reconstructed quadratic form, then the existing
bounded on-image closure theorem applies to `F₀` and transfers positivity back
to `F`.

This isolates exactly the remaining mathematical content of `bvt_W_positive`:
not a new density theorem, but a two-piece handoff:
1. the ambient side supplies exactly `F₀`, `m`, `hF₀`, and `hEq`,
2. the on-image side separately supplies exactly `G`, `hG`, `hcomp`, and
   `hcore` for that fixed `F₀`.

So the ambient surrogate interface is already the exact target for this theorem;
it should not be expanded to package the on-image family inputs as well.

Current route discipline:
- upstream still owes only the fixed-surrogate identification into this theorem;
- downstream recovery of `hcore` stays on the on-image side, via the family
  zero-degree datum and the Stage-5 matrix-element interchange package, rather
  than by reviving the legacy intrinsic surrogate chain in
  `OSToWightmanBoundaryValues.lean`.

Exact seam clarification:
- this theorem itself does **not** take the ambient degree-`0` datum
  `hF0 : (F₀.funcs 0 : SchwartzNPoint d 0) = 0`, because it only consumes the
  abstract closure output `hcore`;
- however, in the current source tree the first available recovery route for
  that `hcore` is the fixed-surrogate/on-image supplier block immediately
  below, and at that seam `hF0` reappears as the first extra ambient payload
  needed to obtain the family zero-degree data used downstream;
- therefore any honest upstream caller analysis for `bvt_W_positive` must
  distinguish the abstract reducer surface here from the stricter currently
  implemented `hcore`-supplier surface below. -/
theorem bvt_wightmanInner_self_nonneg_of_eq_boundaryVanishingTarget
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F F₀ : BorchersSequence d) {m : ℕ}
    (hF₀ : F₀.bound ≤ m)
    (hEq : (WightmanInnerProduct d (bvt_W OS lgc) F F).re =
      (WightmanInnerProduct d (bvt_W OS lgc) F₀ F₀).re)
    (G : ℕ → BvtTransportImageSequence d)
    (hG : ∀ N, (G N).toBorchers.bound ≤ m)
    (hcomp : ∀ n, n ≤ m →
      Filter.Tendsto
        (fun N : ℕ => (((G N).toBorchers.funcs n : SchwartzNPoint d n)))
        Filter.atTop
        (nhds (F₀.funcs n)))
    (hcore : ∀ N,
      0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
        (G N).toBorchers (G N).toBorchers).re) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F F).re := by
  rw [hEq]
  exact bvt_wightmanInner_self_nonneg_of_bounded_onImage_approx
    (d := d) (OS := OS) (lgc := lgc) (F := F₀) (m := m) hF₀ G hG hcomp hcore

/- Exact fixed-surrogate on-image recovery surface, once the ambient side has
already fixed a bounded boundary-vanishing surrogate `F₀`.

This is the narrowest honest interface downstream of
`bvt_wightmanInner_self_nonneg_of_eq_boundaryVanishingTarget`:
- `G`, `hG`, and `hcomp` are still the closure inputs consumed directly there;
- the old per-approximant zero-right equality is not primitive;
- the irreducible extra datum is only that every approximant has zero degree-`0`
  component, from which the zero-right equality is recovered by
  `bvt_zero_right_family_onImage_of_component_zero`;
- `hcore` should not be a new primitive output;
- instead, after recovering the zero-right equality in that way, `hcore` is
  obtained by applying
  `bvt_wightmanInner_self_nonneg_family_onImage_of_zero_right_and_matrix_element_time_interchange`
  to the remaining per-approximant Stage-5 data below.

So the current exact fixed-`F₀` supplier theorem is the next honest bounded
on-image recovery surface:
- it starts from the boundary-vanishing surrogate `F₀`,
- it supplies exactly the bounded on-image approximation data consumed by
  `bvt_wightmanInner_self_nonneg_of_eq_boundaryVanishingTarget`,
- it still carries the family-level degree-`0` zero datum explicitly as a
  separate recovery input,
- and then the zero-right equality and `hcore` are recovered downstream.
-/
/- Exact upstream fixed-surrogate supplier seam.

Immediately before the downstream consumers
- `component_zero_of_fixed_boundaryVanishingSurrogate_onImage_supplier`,
- `bvt_wightmanInner_self_nonneg_of_fixed_boundaryVanishingSurrogate_onImage_supplier_of_timeShift_eq_on_positiveReals`,
- `bvt_wightmanInner_self_nonneg_of_eq_boundaryVanishingTarget`,
the smallest honest missing theorem should have the existential conclusion

`∃ G, hG, hcomp, hprecompact, hambientCompact, hG0, hreal`

for a fixed bounded surrogate `F₀`.

Source-backed precision about that future theorem surface:
- it should live upstream of this block, not inside the legacy
  `OSToWightmanBoundaryValues.lean` retuning chain;
- its explicit inputs should be only the fixed-surrogate ambient data already
  external to this block, namely `F₀`, `m`, `hF₀`, together with whatever
  caller-side identification compares the public target to `F₀`;
- equivalently, the missing supplier theorem itself should stop at the fixed
  surrogate and conclude only
  `∃ G, hG, hcomp, hprecompact, hambientCompact, hG0, hreal`,
  while any separate quadratic-value transport datum such as `hEq` belongs to
  the outer caller of
  `bvt_wightmanInner_self_nonneg_of_eq_boundaryVanishingTarget`, not to this
  supplier surface;
- it should *not* assume the extra ambient degree-`0` datum
  `((F₀.funcs 0 : SchwartzNPoint d 0) = 0)`, because that fact is recovered
  internally here from `hcomp` and `hG0` by the first consumer below.

Current source status after re-reading the on-image and boundary-value layers:
no existing theorem has exactly that fixed-surrogate supplier shape. -/
/- In the variables of the local consumer cluster, that missing supplier should
conclude
`∃ G, hG, hcomp, hprecompact, hambientCompact, hG0, hreal`
with
`hreal :
  ∀ N n k, n ≤ (G N).toBorchers.bound → k ≤ (G N).toBorchers.bound →
      (hk_pos : 0 < k) → ∀ t : ℝ, 0 < t →
        bvt_W OS lgc (n + k)
          (((G N).toBorchers.funcs n).conjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t ((G N).toBorchers.funcs k))) =
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n
            ((bvtTransportImagePreimage (d := d) (G N) n :
                euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n)
            (bvtTransportImagePreimage (d := d) (G N) n).2)
          (PositiveTimeBorchersSequence.single k
            ((bvtTransportImagePreimage (d := d) (G N) k :
                euclideanPositiveTimeSubmodule (d := d) k) :
              SchwartzNPoint d k)
            (bvtTransportImagePreimage (d := d) (G N) k).2) (t : ℂ)`. -/
/-- Internal recovery lemma for the fixed-surrogate on-image supplier block.

If an explicit on-image approximating family `G` converges componentwise to the
fixed surrogate `F₀` and every approximant has zero degree-`0` component, then
the ambient degree-`0` component of `F₀` also vanishes. This is only an
internal consequence of the on-image recovery inputs `hcomp` and `hG0`; it is
not an endorsed public theorem-3 seam. -/
private theorem component_zero_of_fixed_boundaryVanishingSurrogate_onImage_supplier
    (F₀ : BorchersSequence d) {m : ℕ}
    (G : ℕ → BvtTransportImageSequence d)
    (hcomp : ∀ n, n ≤ m →
      Filter.Tendsto
        (fun N : ℕ => (((G N).toBorchers.funcs n : SchwartzNPoint d n)))
        Filter.atTop
        (nhds (F₀.funcs n)))
    (hG0 : ∀ N, ((G N).toBorchers.funcs 0 : SchwartzNPoint d 0) = 0) :
    (F₀.funcs 0 : SchwartzNPoint d 0) = 0 := by
  have hzero_tendsto :
      Filter.Tendsto
        (fun N : ℕ => (((G N).toBorchers.funcs 0 : SchwartzNPoint d 0)))
        Filter.atTop
        (nhds (F₀.funcs 0)) :=
    hcomp 0 (Nat.zero_le m)
  have hcont :
      Continuous (fun f : SchwartzNPoint d 0 => (f : NPointDomain d 0 → ℂ) 0) := by
    simpa [ContinuousLinearMap.comp_apply,
      SchwartzMap.toBoundedContinuousFunctionCLM_apply] using
      ((BoundedContinuousFunction.evalCLM ℂ (0 : NPointDomain d 0)).continuous.comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (NPointDomain d 0) ℂ).continuous)
  have hEval :
      Filter.Tendsto
        (fun N : ℕ =>
          (((G N).toBorchers.funcs 0 : SchwartzNPoint d 0) : NPointDomain d 0 → ℂ) 0)
        Filter.atTop
        (nhds (((F₀.funcs 0 : SchwartzNPoint d 0) : NPointDomain d 0 → ℂ) 0)) :=
    (hcont.continuousAt.tendsto : Filter.Tendsto
      (fun f : SchwartzNPoint d 0 => (f : NPointDomain d 0 → ℂ) 0)
      (nhds (F₀.funcs 0))
      (nhds (((F₀.funcs 0 : SchwartzNPoint d 0) : NPointDomain d 0 → ℂ) 0))).comp hzero_tendsto
  have hconst :
      (fun N : ℕ =>
        (((G N).toBorchers.funcs 0 : SchwartzNPoint d 0) : NPointDomain d 0 → ℂ) 0) =
      fun _ : ℕ => (0 : ℂ) := by
    funext N
    simpa [hG0 N]
  have hzero_limit :
      Filter.Tendsto
        (fun _ : ℕ => (0 : ℂ))
        Filter.atTop
        (nhds (((F₀.funcs 0 : SchwartzNPoint d 0) : NPointDomain d 0 → ℂ) 0)) := by
    convert hEval using 1
    ext N
    simp [hG0 N]
  have hF₀0_eval :
      (((F₀.funcs 0 : SchwartzNPoint d 0) : NPointDomain d 0 → ℂ) 0) = 0 :=
    tendsto_nhds_unique hzero_limit tendsto_const_nhds
  ext x
  have hx : x = 0 := Subsingleton.elim _ _
  simpa [hx] using hF₀0_eval

/-- Internal fixed-`F₀` consumer of the legacy `hpair` witness package.

This theorem no longer claims to construct the on-image approximation family
from the surrogate hypotheses on `F₀` alone. Instead, it records the precise
remaining upstream blocker: once an explicit supplier package
`G, hG, hcomp, hprecompact, hambientCompact, hG0, hpair` is available, the
family-level degree-`0` zero datum `hG0` recovers the zero-right equality via
`bvt_zero_right_family_onImage_of_component_zero`, the per-approximant
nonnegativity follows from
`bvt_wightmanInner_self_nonneg_family_onImage_of_zero_right_and_matrix_element_time_interchange`,
and the bounded closure theorem transfers positivity to `F₀`.

This theorem remains useful as the exact internal consumer reached after the
public `hreal`-facing seam upgrades to `hpair`. It is not the endorsed public
fixed-surrogate theorem surface any more. -/
private theorem bvt_wightmanInner_self_nonneg_of_fixed_boundaryVanishingSurrogate_onImage_supplier
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F₀ : BorchersSequence d) {m : ℕ}
    (hF₀ : F₀.bound ≤ m)
    (G : ℕ → BvtTransportImageSequence d)
    (hG : ∀ N, (G N).toBorchers.bound ≤ m)
    (hcomp : ∀ n, n ≤ m →
      Filter.Tendsto
        (fun N : ℕ => (((G N).toBorchers.funcs n : SchwartzNPoint d n)))
        Filter.atTop
        (nhds (F₀.funcs n)))
    (hprecompact : ∀ N n, n ≤ (G N).toBorchers.bound →
      HasCompactSupport
        ((((bvtTransportImagePreimage (d := d) (G N) n :
              euclideanPositiveTimeSubmodule (d := d) n) :
            SchwartzNPoint d n) : NPointDomain d n → ℂ)))
    (hambientCompact : ∀ N n, n ≤ (G N).toBorchers.bound →
      HasCompactSupport
        ((((G N).toBorchers.funcs n : SchwartzNPoint d n) :
            NPointDomain d n → ℂ)))
    (hG0 : ∀ N, ((G N).toBorchers.funcs 0 : SchwartzNPoint d 0) = 0)
    (hpair :
      ∀ N n k, n ≤ (G N).toBorchers.bound → k ≤ (G N).toBorchers.bound →
          (hk_pos : 0 < k) →
        ∃ H : ℂ → ℂ,
          (∀ t : ℝ, 0 < t →
            H ((t : ℂ) * Complex.I) =
              OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n
                  ((bvtTransportImagePreimage (d := d) (G N) n :
                      euclideanPositiveTimeSubmodule (d := d) n) :
                    SchwartzNPoint d n)
                  (bvtTransportImagePreimage (d := d) (G N) n).2)
                (PositiveTimeBorchersSequence.single k
                  ((bvtTransportImagePreimage (d := d) (G N) k :
                      euclideanPositiveTimeSubmodule (d := d) k) :
                    SchwartzNPoint d k)
                  (bvtTransportImagePreimage (d := d) (G N) k).2) (t : ℂ)) ∧
          (∀ t : ℝ, 0 < t →
            Filter.Tendsto
              (fun ε : ℝ =>
                ∫ y : NPointDomain d (n + k),
                  bvt_F OS lgc (n + k)
                    (xiShift ⟨n, Nat.lt_add_of_pos_right hk_pos⟩ 0
                      (fun j μ =>
                        ↑(y j μ) +
                          ε * ↑(canonicalForwardConeDirection (d := d) (n + k) j μ) *
                            Complex.I)
                      (t : ℂ)) *
                    (((G N).toBorchers.funcs n).conjTensorProduct
                      ((G N).toBorchers.funcs k)) y)
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds (H ((t : ℂ) * Complex.I))))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F₀ F₀).re := by
  have hzero :
      ∀ N n, n ≤ (G N).toBorchers.bound →
        bvt_W OS lgc (n + 0)
          (((G N).toBorchers.funcs n).conjTensorProduct ((G N).toBorchers.funcs 0)) =
        OS.S (n + 0)
          (ZeroDiagonalSchwartz.ofClassical
            ((((bvtTransportImagePreimage (d := d) (G N) n :
                  euclideanPositiveTimeSubmodule (d := d) n) :
                SchwartzNPoint d n).osConjTensorProduct
              ((bvtTransportImagePreimage (d := d) (G N) 0 :
                  euclideanPositiveTimeSubmodule (d := d) 0) :
                SchwartzNPoint d 0)))) :=
    bvt_zero_right_family_onImage_of_component_zero
      (d := d) (OS := OS) (lgc := lgc) (G := G) hG0
  have hcore :
      ∀ N,
        0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
          (G N).toBorchers (G N).toBorchers).re :=
    bvt_wightmanInner_self_nonneg_family_onImage_of_zero_right_and_matrix_element_time_interchange
      (d := d) (OS := OS) (lgc := lgc) (G := G) (m := m) hG
      hprecompact hambientCompact hzero hpair
  exact bvt_wightmanInner_self_nonneg_of_bounded_onImage_approx
    (d := d) (OS := OS) (lgc := lgc) (F := F₀) (m := m) hF₀ G hG hcomp hcore

/- Honest one-step sharpening of the fixed-surrogate on-image recovery seam.

At this level the intermediate Lemma-4.2 witness package `hpair` is no longer
irreducible: the general transformed-image reducer
`exists_hpair_bvtTransportImagePreimage_of_timeShift_eq_on_positiveReals`
already upgrades the positive-real-time identification data `hreal` to `hpair`
for each approximant and each positive-degree pair. So the truthful
fixed-surrogate on-image recovery surface now speaks directly in terms of
`hreal` on the positive-degree side, while the separate family-level degree-`0`
datum `hG0` still remains explicit on the present theorem surface and should be
read only as an internal/on-image recovery input, not as an endorsed ambient
theorem-3 seam. The older theorem above remains the exact internal consumer of
the resulting matrix-element witness package.

Exact upstream blocker surface:
- immediately before the consumers
  `component_zero_of_fixed_boundaryVanishingSurrogate_onImage_supplier`,
  `bvt_wightmanInner_self_nonneg_of_fixed_boundaryVanishingSurrogate_onImage_supplier_of_timeShift_eq_on_positiveReals`,
  and `bvt_wightmanInner_self_nonneg_of_eq_boundaryVanishingTarget`,
  the smallest honest missing theorem is an upstream fixed-`F₀` supplier with
  conclusion
  `∃ G, hG, hcomp, hprecompact, hambientCompact, hG0, hreal`;
- its hypotheses should be only the fixed-surrogate ambient data already
  external to this block, namely `F₀`, `m`, and `hF₀`, together with whatever
  additional ambient identification is needed by the caller to compare the
  public target to `F₀`;
- the same positive-degree `hreal` family is also the current upstream input
  for the comparison lane's newer `hWlimit` consumers, via the existing
  `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single` plus
  `tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_conjTensorProduct_timeShift`
  upgrade, so no extra wrapper theorem belongs at this on-image seam;
- source-first, the only genuinely absent ingredient at this seam is the
  constructor producing such a positive-time/on-image family `G` for the fixed
  surrogate `F₀`; once that family exists, the present compact-family/on-image
  cluster already supplies the remaining payload fields downstream;
- accordingly, the theorem immediately below is already the narrow theorem-sized
  fixed-surrogate/on-image handoff from `hreal` to downstream positivity; the
  only missing theorem surface is the upstream existential supplier producing
  `G, hG, hcomp, hprecompact, hambientCompact, hG0, hreal`;
- once that existential supplier is available, the present file already
  recovers the ambient degree-`0` vanishing internally via
  `component_zero_of_fixed_boundaryVanishingSurrogate_onImage_supplier`,
  proves positivity for `F₀` via the theorem below, and then lets
  `bvt_wightmanInner_self_nonneg_of_eq_boundaryVanishingTarget` transfer the
  result back to the original target.

Current source status after re-reading this file and the boundary-value layers:
no existing theorem has that fixed-`F₀` supplier shape. -/
/- Exact producer-cluster adjacency note:
the future existential supplier with payload
`∃ G, hG, hcomp, hprecompact, hambientCompact, hG0, hreal`
should adjoin immediately above the three-theorem local consumer cluster
`component_zero_of_fixed_boundaryVanishingSurrogate_onImage_supplier`,
`bvt_wightmanInner_self_nonneg_of_fixed_boundaryVanishingSurrogate_onImage_supplier_of_timeShift_eq_on_positiveReals`,
and `bvt_wightmanInner_self_nonneg_of_eq_boundaryVanishingTarget`, because
that is the first current source block that consumes the full package without
any additional wrapper theorem surface. A future theorem at exactly this seam
should therefore be named on the fixed-surrogate supplier surface itself, e.g.
`exists_fixed_boundaryVanishingSurrogate_onImage_supplier_of_timeShift_eq_on_positiveReals`.

Current source-backed refinement after the explicit preimage-family pass:
the theorem-sized ingress up to, but not including, `hreal` is now already
implemented above as
`exists_bounded_componentwise_onImage_supplier_data_of_preimageFamilies`.
So the first remaining missing producer here is no longer an earlier carrier
ingress to `PositiveTimeBorchersSequence d`. But a proof-body-first audit of
the actual downstream consumers sharpens the next theorem-sized step further:
the public payload still exposed here is `hreal`, yet the earliest new theorem
to prove is one level upstream in `OSToWightmanPositivity.lean`, not an
on-image wrapper theorem stated directly as `hreal`.

The reason is visible from the exact bodies of the quoted consumers:

- `lemma42_matrix_element_time_interchange` is only a call to
  `kernel_eq_of_tendsto_bvt_F_canonical_xiShift_to_upperHalfPlaneWitness_on_imagAxis`,
  so locally it consumes only
  `hH_imag_os : H ((t : ℂ) * Complex.I) = OSInnerProductTimeShiftHolomorphicValue ...`
  together with the matching shell limit `hlimit`;
- `one_variable_time_interchange_for_wightman_pairing` is strictly later: it
  takes an already-rotated right-half-plane witness `H` and uses it only to
  obtain the positive-real `bvt_singleSplit_xiShiftHolomorphicValue = bvt_W`
  comparison;
- `bvt_xiShift_eq_osInnerProduct_holomorphicValue_single` is later again: once
  that positive-real comparison has been routed through the existing
  `singleSplit` trace, it upgrades to the semigroup-side holomorphic value;
- the on-image reducers here, such as
  `bvt_wightmanInner_self_nonneg_of_fixed_boundaryVanishingSurrogate_onImage_supplier_of_timeShift_eq_on_positiveReals`
  and
  `compactApproxPositiveTime_onImage_hpair_of_timeShift_eq_on_positiveReals`,
  only consume the resulting positive-real family `hreal`.

So, on the explicit ambient/preimage inputs
`F, hF, hcomp, f, hf, hprecompact, hambientCompact, hF0`,
the minimal honest next theorem is the fixed-pair upper-half-plane scalarization
step:
`∃ Hs : ℂ → ℂ,
    DifferentiableOn ℂ Hs SCV.upperHalfPlane ∧
    (∀ t : ℝ, 0 < t →
      Hs ((t : ℂ) * Complex.I) =
        OSInnerProductTimeShiftHolomorphicValue ... (t : ℂ))`,
with the fixed pair determined by the current Section-4.3 quotient data.
Only after assembling this `Hs` should later code rotate it to the right-half-
plane witness used by `one_variable_time_interchange_for_wightman_pairing`,
derive the positive-real `singleSplit` comparison, and then expose the public
`hreal` family consumed in this file.

So there is still no honest missing theorem here that is merely a new compact-
family wrapper, and the next theorem is not the already-rotated witness `H`.
The next theorem-sized assembly step is the fixed-pair upper-half-plane
scalarization `Hs`, whose downstream consequence composes to the explicit
`hreal` producer. -/
/- Exact source-backed obstruction behind that ingress claim:
the current transformed-image entry theorems in this file stop at
`BvtTransportImageSequence.ofPreimageFamily` and
`section43PositiveEnergyQuotientMap_mem_bvtTransportImage_iff_exists_preimage`.
Those only ask for degreewise Section-4.3 quotient equalities
`os1TransportComponent d n f = section43PositiveEnergyQuotientMap ...`; they
do not produce the strict ordered-support facts needed to package the ambient
components into `PositiveTimeBorchersSequence`, and they do not prove the
family-level approximation/compactness/degree-`0` payload required by the
fixed-surrogate consumer cluster.

So the next honest theorem cannot merely rephrase the compact-family producer
already proved below. It has to be an earlier ingress theorem, for a fixed
surrogate `F₀`, supplying either:

- an honest `PositiveTimeBorchersSequence d` whose Borchers components are the
  chosen surrogate/preimage data strongly enough for
  `compactApproxPositiveTimeBorchers` to instantiate the canonical family, or
- directly the equivalent transformed-image family
  `∃ G, hG, hcomp, hprecompact, hambientCompact, hG0`
  before the positive-real comparison `hreal` is even discussed.

Until that ingress exists, the theorem
`compactApproxPositiveTime_timeShift_eq_osHolomorphicValue_of_singleSplit_eq_bvt_W_on_positiveReals`
below is already the smallest honest producer available on the canonical
compact family, but only conditional on starting from an existing positive-time
carrier. -/
/-- On the canonical compact positive-time family
`N ↦ PositiveTimeBorchersSequence.toBvtTransportImageSequence
      (compactApproxPositiveTimeBorchers F N)`,
the chosen transformed-image preimages `bvtTransportImagePreimage` are
definitionally the original compact positive-time cutoff components. Hence the
supplier's preimage-side compact-support field `hprecompact` is already
available from `compactApproxPositiveTimeBorchers_component_compact` on this
explicit family. -/
theorem compactApproxPositiveTime_toBvtTransportImageSequence_hprecompact
    (F : PositiveTimeBorchersSequence d) :
    ∀ N n,
      n ≤ (PositiveTimeBorchersSequence.toBvtTransportImageSequence (d := d)
        (compactApproxPositiveTimeBorchers (d := d) F N)).toBorchers.bound →
      HasCompactSupport
        ((((bvtTransportImagePreimage (d := d)
              (PositiveTimeBorchersSequence.toBvtTransportImageSequence (d := d)
                (compactApproxPositiveTimeBorchers (d := d) F N)) n :
              euclideanPositiveTimeSubmodule (d := d) n) :
            SchwartzNPoint d n) : NPointDomain d n → ℂ)) := by
  intro N n _hn
  simpa [bvtTransportImagePreimage_of_positiveTime] using
    (compactApproxPositiveTimeBorchers_component_compact (d := d) F N n)

private theorem bvt_wightmanInner_self_nonneg_of_fixed_boundaryVanishingSurrogate_onImage_supplier_of_timeShift_eq_on_positiveReals
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F₀ : BorchersSequence d) {m : ℕ}
    (hF₀ : F₀.bound ≤ m)
    (G : ℕ → BvtTransportImageSequence d)
    (hG : ∀ N, (G N).toBorchers.bound ≤ m)
    (hcomp : ∀ n, n ≤ m →
      Filter.Tendsto
        (fun N : ℕ => (((G N).toBorchers.funcs n : SchwartzNPoint d n)))
        Filter.atTop
        (nhds (F₀.funcs n)))
    (hprecompact : ∀ N n, n ≤ (G N).toBorchers.bound →
      HasCompactSupport
        ((((bvtTransportImagePreimage (d := d) (G N) n :
              euclideanPositiveTimeSubmodule (d := d) n) :
            SchwartzNPoint d n) : NPointDomain d n → ℂ)))
    (hambientCompact : ∀ N n, n ≤ (G N).toBorchers.bound →
      HasCompactSupport
        ((((G N).toBorchers.funcs n : SchwartzNPoint d n) :
            NPointDomain d n → ℂ)))
    (hG0 : ∀ N, ((G N).toBorchers.funcs 0 : SchwartzNPoint d 0) = 0)
    (hreal :
      ∀ N n k, n ≤ (G N).toBorchers.bound → k ≤ (G N).toBorchers.bound →
          (hk_pos : 0 < k) →
          ∀ t : ℝ, 0 < t →
            bvt_W OS lgc (n + k)
              (((G N).toBorchers.funcs n).conjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t ((G N).toBorchers.funcs k))) =
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n
                ((bvtTransportImagePreimage (d := d) (G N) n :
                    euclideanPositiveTimeSubmodule (d := d) n) :
                  SchwartzNPoint d n)
                (bvtTransportImagePreimage (d := d) (G N) n).2)
              (PositiveTimeBorchersSequence.single k
                ((bvtTransportImagePreimage (d := d) (G N) k :
                    euclideanPositiveTimeSubmodule (d := d) k) :
                  SchwartzNPoint d k)
                (bvtTransportImagePreimage (d := d) (G N) k).2) (t : ℂ)) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F₀ F₀).re := by
  apply bvt_wightmanInner_self_nonneg_of_fixed_boundaryVanishingSurrogate_onImage_supplier
    (d := d) (OS := OS) (lgc := lgc) (F₀ := F₀) (m := m) hF₀ G hG hcomp
    hprecompact hambientCompact hG0
  intro N n k hn hk hk_pos
  exact
    exists_hpair_bvtTransportImagePreimage_of_timeShift_eq_on_positiveReals
      (d := d) (OS := OS) (lgc := lgc) (F := G N) (n := n) (k := k) hk_pos
      (hprecompact N n hn) (hprecompact N k hk) (hreal N n k hn hk hk_pos)

/-- The legacy compact positive-time cutoff family already fits the exact
bounded on-image closure interface. This packages the old positive-time
approximation supplier into the new Stage-5 closure theorem; what remains is to
prove the per-approximant on-image positivity input on that family. -/
theorem bvt_wightmanInner_self_nonneg_of_compactApproxPositiveTime_onImage
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hcore : ∀ N,
      0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
        (compactApproxPositiveTimeBorchers (d := d) F N : BorchersSequence d)
        (compactApproxPositiveTimeBorchers (d := d) F N : BorchersSequence d)).re) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re := by
  let G : ℕ → BvtTransportImageSequence d := fun N =>
    PositiveTimeBorchersSequence.toBvtTransportImageSequence (d := d)
      (compactApproxPositiveTimeBorchers (d := d) F N)
  apply bvt_wightmanInner_self_nonneg_of_bounded_onImage_approx
    (d := d) (OS := OS) (lgc := lgc) (F := (F : BorchersSequence d))
    (m := (F : BorchersSequence d).bound) (G := G)
  · exact le_rfl
  · intro N
    change (compactApproxPositiveTimeBorchers (d := d) F N : BorchersSequence d).bound ≤
      (F : BorchersSequence d).bound
    simp [compactApproxPositiveTimeBorchers]
  · intro n hn
    change Filter.Tendsto
      (fun N : ℕ =>
        (((compactApproxPositiveTimeBorchers (d := d) F N : PositiveTimeBorchersSequence d) :
            BorchersSequence d).funcs n : SchwartzNPoint d n))
      Filter.atTop
      (nhds (((F : BorchersSequence d).funcs n : SchwartzNPoint d n)))
    simpa using
      (tendsto_compactApproxPositiveTimeBorchers_component (d := d) F n)
  · intro N
    simpa [G] using hcore N

/-- Legacy compact-family bridge into
`bvt_wightmanInner_self_nonneg_of_fixed_boundaryVanishingSurrogate_onImage_supplier`.

For the legacy compact positive-time cutoff family, the bounded convergence,
ambient compact-support, preimage compact-support, and family-level degree-`0`
zero data are all automatic once the ambient target already has zero degree-`0`
component. What still does not follow formally is the positive-degree
Lemma-4.2 witness package `hpair`; this theorem isolates that legacy internal
bridge explicitly on the compact-family surface. The endorsed public seam is
the fixed-surrogate `hreal` theorem, not this compact-family `hpair` consumer. -/
private theorem bvt_wightmanInner_self_nonneg_of_compactApproxPositiveTime_onImage_supplier_of_component_zero
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hF0 : (((F : BorchersSequence d).funcs 0 : SchwartzNPoint d 0)) = 0)
    (hpair :
      ∀ N n k,
          n ≤ (compactApproxPositiveTimeBorchers (d := d) F N : BorchersSequence d).bound →
          k ≤ (compactApproxPositiveTimeBorchers (d := d) F N : BorchersSequence d).bound →
          (hk_pos : 0 < k) →
        ∃ H : ℂ → ℂ,
          (∀ t : ℝ, 0 < t →
            H ((t : ℂ) * Complex.I) =
              OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n
                  ((((compactApproxPositiveTimeBorchers (d := d) F N :
                        PositiveTimeBorchersSequence d) :
                      BorchersSequence d).funcs n) :
                    SchwartzNPoint d n)
                  ((compactApproxPositiveTimeBorchers (d := d) F N :
                      PositiveTimeBorchersSequence d).ordered_tsupport n))
                (PositiveTimeBorchersSequence.single k
                  ((((compactApproxPositiveTimeBorchers (d := d) F N :
                        PositiveTimeBorchersSequence d) :
                      BorchersSequence d).funcs k) :
                    SchwartzNPoint d k)
                  ((compactApproxPositiveTimeBorchers (d := d) F N :
                      PositiveTimeBorchersSequence d).ordered_tsupport k)) (t : ℂ)) ∧
          (∀ t : ℝ, 0 < t →
            Filter.Tendsto
              (fun ε : ℝ =>
                ∫ y : NPointDomain d (n + k),
                  bvt_F OS lgc (n + k)
                    (xiShift ⟨n, Nat.lt_add_of_pos_right hk_pos⟩ 0
                      (fun j μ =>
                        ↑(y j μ) +
                          ε * ↑(canonicalForwardConeDirection (d := d) (n + k) j μ) *
                            Complex.I)
                      (t : ℂ)) *
                    (((((compactApproxPositiveTimeBorchers (d := d) F N :
                            PositiveTimeBorchersSequence d) :
                          BorchersSequence d).funcs n) : SchwartzNPoint d n).conjTensorProduct
                      ((((compactApproxPositiveTimeBorchers (d := d) F N :
                            PositiveTimeBorchersSequence d) :
                          BorchersSequence d).funcs k) : SchwartzNPoint d k)) y)
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds (H ((t : ℂ) * Complex.I))))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re := by
  let G : ℕ → BvtTransportImageSequence d := fun N =>
    PositiveTimeBorchersSequence.toBvtTransportImageSequence (d := d)
      (compactApproxPositiveTimeBorchers (d := d) F N)
  apply bvt_wightmanInner_self_nonneg_of_fixed_boundaryVanishingSurrogate_onImage_supplier
    (d := d) (OS := OS) (lgc := lgc) (F₀ := (F : BorchersSequence d))
    (m := (F : BorchersSequence d).bound) (G := G)
  · exact le_rfl
  · intro N
    change (compactApproxPositiveTimeBorchers (d := d) F N : BorchersSequence d).bound ≤
      (F : BorchersSequence d).bound
    simp [compactApproxPositiveTimeBorchers]
  · intro n hn
    change Filter.Tendsto
      (fun N : ℕ =>
        (((compactApproxPositiveTimeBorchers (d := d) F N : PositiveTimeBorchersSequence d) :
            BorchersSequence d).funcs n : SchwartzNPoint d n))
      Filter.atTop
      (nhds (((F : BorchersSequence d).funcs n : SchwartzNPoint d n)))
    simpa using
      (tendsto_compactApproxPositiveTimeBorchers_component (d := d) F n)
  · intro N n hn
    simpa [G, bvtTransportImagePreimage_of_positiveTime] using
      (compactApproxPositiveTimeBorchers_component_compact (d := d) F N n)
  · intro N n hn
    simpa [G] using
      PositiveTimeBorchersSequence.compactApproxPositiveTime_toBvtTransportImageSequence_hambientCompact
        (d := d) F N n hn
  · exact
      PositiveTimeBorchersSequence.compactApproxPositiveTime_onImage_component_zero_of_component_zero
        (d := d) (F := F) hF0
  · intro N n k hn hk hk_pos
    simpa [G, bvtTransportImagePreimage_of_positiveTime] using
      hpair N n k hn hk hk_pos

/-- Legacy compact-family reducer from `hreal` to the internal `hpair` package.

For the legacy compact positive-time cutoff family, the already-proved
general transformed-image reducer
`exists_hpair_bvtTransportImagePreimage_of_timeShift_eq_on_positiveReals`
upgrades any honest positive-real-time identification
between the right-time-shifted reconstructed Wightman pairing and the OS
matrix element into the precise per-approximant Lemma-4.2 witness package
required by
`bvt_wightmanInner_self_nonneg_of_compactApproxPositiveTime_onImage_supplier_of_component_zero`.

This theorem does not prove that positive-real-time identification. It isolates
the exact legacy bridge datum on the compact-family surface: once `hreal`
is supplied, the downstream internal `hpair` package is formal. This remains a
local bridge for the compact-family route, not the endorsed public theorem-3
seam. -/
private theorem compactApproxPositiveTime_onImage_hpair_of_timeShift_eq_on_positiveReals
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hreal :
      ∀ N n k,
          n ≤ (compactApproxPositiveTimeBorchers (d := d) F N : BorchersSequence d).bound →
          k ≤ (compactApproxPositiveTimeBorchers (d := d) F N : BorchersSequence d).bound →
          (hk_pos : 0 < k) →
          ∀ t : ℝ, 0 < t →
            bvt_W OS lgc (n + k)
              (((((compactApproxPositiveTimeBorchers (d := d) F N :
                      PositiveTimeBorchersSequence d) :
                    BorchersSequence d).funcs n) : SchwartzNPoint d n).conjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t
                  ((((compactApproxPositiveTimeBorchers (d := d) F N :
                        PositiveTimeBorchersSequence d) :
                      BorchersSequence d).funcs k) : SchwartzNPoint d k))) =
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n
                ((((compactApproxPositiveTimeBorchers (d := d) F N :
                      PositiveTimeBorchersSequence d) :
                    BorchersSequence d).funcs n) : SchwartzNPoint d n)
                ((compactApproxPositiveTimeBorchers (d := d) F N :
                    PositiveTimeBorchersSequence d).ordered_tsupport n))
              (PositiveTimeBorchersSequence.single k
                ((((compactApproxPositiveTimeBorchers (d := d) F N :
                      PositiveTimeBorchersSequence d) :
                    BorchersSequence d).funcs k) : SchwartzNPoint d k)
                ((compactApproxPositiveTimeBorchers (d := d) F N :
                    PositiveTimeBorchersSequence d).ordered_tsupport k)) (t : ℂ)) :
    ∀ N n k,
        n ≤ (compactApproxPositiveTimeBorchers (d := d) F N : BorchersSequence d).bound →
        k ≤ (compactApproxPositiveTimeBorchers (d := d) F N : BorchersSequence d).bound →
        (hk_pos : 0 < k) →
      ∃ H : ℂ → ℂ,
        (∀ t : ℝ, 0 < t →
          H ((t : ℂ) * Complex.I) =
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n
                ((((compactApproxPositiveTimeBorchers (d := d) F N :
                      PositiveTimeBorchersSequence d) :
                    BorchersSequence d).funcs n) :
                  SchwartzNPoint d n)
                ((compactApproxPositiveTimeBorchers (d := d) F N :
                    PositiveTimeBorchersSequence d).ordered_tsupport n))
              (PositiveTimeBorchersSequence.single k
                ((((compactApproxPositiveTimeBorchers (d := d) F N :
                      PositiveTimeBorchersSequence d) :
                    BorchersSequence d).funcs k) :
                  SchwartzNPoint d k)
                ((compactApproxPositiveTimeBorchers (d := d) F N :
                    PositiveTimeBorchersSequence d).ordered_tsupport k)) (t : ℂ)) ∧
        (∀ t : ℝ, 0 < t →
          Filter.Tendsto
            (fun ε : ℝ =>
              ∫ y : NPointDomain d (n + k),
                bvt_F OS lgc (n + k)
                  (xiShift ⟨n, Nat.lt_add_of_pos_right hk_pos⟩ 0
                    (fun j μ =>
                      ↑(y j μ) +
                        ε * ↑(canonicalForwardConeDirection (d := d) (n + k) j μ) *
                          Complex.I)
                    (t : ℂ)) *
                  (((((compactApproxPositiveTimeBorchers (d := d) F N :
                          PositiveTimeBorchersSequence d) :
                        BorchersSequence d).funcs n) : SchwartzNPoint d n).conjTensorProduct
                    ((((compactApproxPositiveTimeBorchers (d := d) F N :
                          PositiveTimeBorchersSequence d) :
                        BorchersSequence d).funcs k) : SchwartzNPoint d k)) y)
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds (H ((t : ℂ) * Complex.I)))) := by
  intro N n k hn hk hk_pos
  let G0 : BvtTransportImageSequence d :=
    PositiveTimeBorchersSequence.toBvtTransportImageSequence (d := d)
      (compactApproxPositiveTimeBorchers (d := d) F N)
  have hprecompact_n :
      HasCompactSupport
        ((((bvtTransportImagePreimage (d := d) G0 n :
              euclideanPositiveTimeSubmodule (d := d) n) :
            SchwartzNPoint d n) : NPointDomain d n → ℂ)) := by
    simpa [G0, bvtTransportImagePreimage_of_positiveTime] using
      (compactApproxPositiveTimeBorchers_component_compact (d := d) F N n)
  have hprecompact_k :
      HasCompactSupport
        ((((bvtTransportImagePreimage (d := d) G0 k :
              euclideanPositiveTimeSubmodule (d := d) k) :
            SchwartzNPoint d k) : NPointDomain d k → ℂ)) := by
    simpa [G0, bvtTransportImagePreimage_of_positiveTime] using
      (compactApproxPositiveTimeBorchers_component_compact (d := d) F N k)
  have hpair :=
    exists_hpair_bvtTransportImagePreimage_of_timeShift_eq_on_positiveReals
      (d := d) (OS := OS) (lgc := lgc) (F := G0) (n := n) (k := k) hk_pos
      hprecompact_n hprecompact_k (by
        intro t ht
        simpa [G0, bvtTransportImagePreimage_of_positiveTime] using
          hreal N n k hn hk hk_pos t ht)
  simpa [G0, bvtTransportImagePreimage_of_positiveTime] using hpair

/-- Exact compact-family bridge from the old compact-shell positive-real surface
to the corrected on-image positive-real semigroup surface.

For each compact positive-time cutoff approximant, the legacy compact-shell
hypothesis from `OSToWightmanBoundaryValuesCompactApprox.lean` and
`bvt_xiShift_eq_osInnerProduct_holomorphicValue_single` share the same
`bvt_singleSplit_xiShiftHolomorphicValue` left-hand side. So on this compact
family the upgrade to the Stage-5 on-image target is a direct transitivity
step, with no need to expose the intermediate `hpair` package. -/
private theorem
    compactApproxPositiveTime_timeShift_eq_osHolomorphicValue_of_singleSplit_eq_bvt_W_on_positiveReals
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hlegacy :
      ∀ N n k (hk_pos : 0 < k) (t : ℝ), 0 < t →
        let F_N : PositiveTimeBorchersSequence d := compactApproxPositiveTimeBorchers (d := d) F N;
          bvt_singleSplit_xiShiftHolomorphicValue
            (d := d) OS lgc hk_pos
            (((F_N : BorchersSequence d).funcs n))
            (F_N.ordered_tsupport n)
            (compactApproxPositiveTimeBorchers_component_compact (d := d) F N n)
            (((F_N : BorchersSequence d).funcs k))
            (F_N.ordered_tsupport k)
            (compactApproxPositiveTimeBorchers_component_compact (d := d) F N k) (t : ℂ)
          =
            bvt_W OS lgc (n + k)
              (((F_N : BorchersSequence d).funcs n).conjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t
                  ((F_N : BorchersSequence d).funcs k)))) :
    ∀ N n k,
        n ≤ (compactApproxPositiveTimeBorchers (d := d) F N : BorchersSequence d).bound →
        k ≤ (compactApproxPositiveTimeBorchers (d := d) F N : BorchersSequence d).bound →
        (hk_pos : 0 < k) →
        ∀ t : ℝ, 0 < t →
          bvt_W OS lgc (n + k)
            (((((compactApproxPositiveTimeBorchers (d := d) F N :
                    PositiveTimeBorchersSequence d) :
                  BorchersSequence d).funcs n) : SchwartzNPoint d n).conjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t
                ((((compactApproxPositiveTimeBorchers (d := d) F N :
                      PositiveTimeBorchersSequence d) :
                    BorchersSequence d).funcs k) : SchwartzNPoint d k))) =
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n
              ((((compactApproxPositiveTimeBorchers (d := d) F N :
                    PositiveTimeBorchersSequence d) :
                  BorchersSequence d).funcs n) : SchwartzNPoint d n)
              ((compactApproxPositiveTimeBorchers (d := d) F N :
                  PositiveTimeBorchersSequence d).ordered_tsupport n))
            (PositiveTimeBorchersSequence.single k
              ((((compactApproxPositiveTimeBorchers (d := d) F N :
                    PositiveTimeBorchersSequence d) :
                  BorchersSequence d).funcs k) : SchwartzNPoint d k)
              ((compactApproxPositiveTimeBorchers (d := d) F N :
                  PositiveTimeBorchersSequence d).ordered_tsupport k)) (t : ℂ) := by
  intro N n k _hn _hk hk_pos t ht
  let F_N : PositiveTimeBorchersSequence d := compactApproxPositiveTimeBorchers (d := d) F N
  have hlegacy_t :
      bvt_singleSplit_xiShiftHolomorphicValue
        (d := d) OS lgc hk_pos
        (((F_N : BorchersSequence d).funcs n))
        (F_N.ordered_tsupport n)
        (compactApproxPositiveTimeBorchers_component_compact (d := d) F N n)
        (((F_N : BorchersSequence d).funcs k))
        (F_N.ordered_tsupport k)
        (compactApproxPositiveTimeBorchers_component_compact (d := d) F N k) (t : ℂ)
      =
        bvt_W OS lgc (n + k)
          (((F_N : BorchersSequence d).funcs n).conjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t
              ((F_N : BorchersSequence d).funcs k))) := by
    simpa [F_N] using hlegacy N n k hk_pos t ht
  have hbridge :
      bvt_singleSplit_xiShiftHolomorphicValue
        (d := d) OS lgc hk_pos
        (((F_N : BorchersSequence d).funcs n))
        (F_N.ordered_tsupport n)
        (compactApproxPositiveTimeBorchers_component_compact (d := d) F N n)
        (((F_N : BorchersSequence d).funcs k))
        (F_N.ordered_tsupport k)
        (compactApproxPositiveTimeBorchers_component_compact (d := d) F N k) (t : ℂ)
      =
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n
            (((F_N : BorchersSequence d).funcs n))
            (F_N.ordered_tsupport n))
          (PositiveTimeBorchersSequence.single k
            (((F_N : BorchersSequence d).funcs k))
            (F_N.ordered_tsupport k)) (t : ℂ) := by
    simpa [F_N] using
      bvt_xiShift_eq_osInnerProduct_holomorphicValue_single
        (d := d) (OS := OS) (lgc := lgc) (n := n) (m := k) hk_pos
        (((F_N : BorchersSequence d).funcs n))
        (F_N.ordered_tsupport n)
        (compactApproxPositiveTimeBorchers_component_compact (d := d) F N n)
        (((F_N : BorchersSequence d).funcs k))
        (F_N.ordered_tsupport k)
        (compactApproxPositiveTimeBorchers_component_compact (d := d) F N k)
        (t : ℂ) (by simpa using ht)
  exact hlegacy_t.symm.trans hbridge

/-- Exact composed legacy compact-family consumer surface downstream of the
fixed-surrogate on-image reducer.

For the legacy compact positive-time cutoff family, nothing beyond the
irreducible ambient degree-`0` vanishing datum and the honest positive-real-time
identification is needed upstream: the first produces the family-level
degree-`0` zero data required by the fixed-surrogate supplier reducer, and the
second produces its `hpair` package via
`compactApproxPositiveTime_onImage_hpair_of_timeShift_eq_on_positiveReals`.

So this theorem is the narrowest truthful compact-family closure surface
currently available downstream of that fixed-surrogate reframe. It is a legacy
compact-family consumer interface, not an endorsed public theorem-3 seam; it
does not postulate an existential supplier family and it does not return to the
legacy intrinsic route. -/
private theorem bvt_wightmanInner_self_nonneg_of_compactApproxPositiveTime_onImage_of_component_zero_and_timeShift_eq_on_positiveReals
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hF0 : (((F : BorchersSequence d).funcs 0 : SchwartzNPoint d 0)) = 0)
    (hreal :
      ∀ N n k,
          n ≤ (compactApproxPositiveTimeBorchers (d := d) F N : BorchersSequence d).bound →
          k ≤ (compactApproxPositiveTimeBorchers (d := d) F N : BorchersSequence d).bound →
          (hk_pos : 0 < k) →
          ∀ t : ℝ, 0 < t →
            bvt_W OS lgc (n + k)
              (((((compactApproxPositiveTimeBorchers (d := d) F N :
                      PositiveTimeBorchersSequence d) :
                    BorchersSequence d).funcs n) : SchwartzNPoint d n).conjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t
                  ((((compactApproxPositiveTimeBorchers (d := d) F N :
                        PositiveTimeBorchersSequence d) :
                      BorchersSequence d).funcs k) : SchwartzNPoint d k))) =
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n
                ((((compactApproxPositiveTimeBorchers (d := d) F N :
                      PositiveTimeBorchersSequence d) :
                    BorchersSequence d).funcs n) : SchwartzNPoint d n)
                ((compactApproxPositiveTimeBorchers (d := d) F N :
                    PositiveTimeBorchersSequence d).ordered_tsupport n))
              (PositiveTimeBorchersSequence.single k
                ((((compactApproxPositiveTimeBorchers (d := d) F N :
                      PositiveTimeBorchersSequence d) :
                    BorchersSequence d).funcs k) : SchwartzNPoint d k)
                ((compactApproxPositiveTimeBorchers (d := d) F N :
                    PositiveTimeBorchersSequence d).ordered_tsupport k)) (t : ℂ)) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re := by
  let G : ℕ → BvtTransportImageSequence d := fun N =>
    PositiveTimeBorchersSequence.toBvtTransportImageSequence (d := d)
      (compactApproxPositiveTimeBorchers (d := d) F N)
  apply
    bvt_wightmanInner_self_nonneg_of_fixed_boundaryVanishingSurrogate_onImage_supplier_of_timeShift_eq_on_positiveReals
      (d := d) (OS := OS) (lgc := lgc) (F₀ := (F : BorchersSequence d))
      (m := (F : BorchersSequence d).bound) (G := G)
  · exact le_rfl
  · intro N
    change (compactApproxPositiveTimeBorchers (d := d) F N : BorchersSequence d).bound ≤
      (F : BorchersSequence d).bound
    simp [compactApproxPositiveTimeBorchers]
  · intro n hn
    change Filter.Tendsto
      (fun N : ℕ =>
        (((compactApproxPositiveTimeBorchers (d := d) F N : PositiveTimeBorchersSequence d) :
            BorchersSequence d).funcs n : SchwartzNPoint d n))
      Filter.atTop
      (nhds (((F : BorchersSequence d).funcs n : SchwartzNPoint d n)))
    simpa using
      (tendsto_compactApproxPositiveTimeBorchers_component (d := d) F n)
  · intro N n hn
    simpa [G, bvtTransportImagePreimage_of_positiveTime] using
      (compactApproxPositiveTimeBorchers_component_compact (d := d) F N n)
  · intro N n hn
    simpa [G] using
      (compactApproxPositiveTimeBorchers_component_compact (d := d) F N n)
  · exact
      PositiveTimeBorchersSequence.compactApproxPositiveTime_onImage_component_zero_of_component_zero
        (d := d) (F := F) hF0
  · intro N n k hn hk hk_pos t ht
    simpa [G, bvtTransportImagePreimage_of_positiveTime] using
      hreal N n k hn hk hk_pos t ht

/-- Exact compact-family on-image nonnegativity consumer that absorbs the old
compact-shell positive-real theorem surface internally.

This is the strongest truthful compact-family on-image closure theorem now
justified by source: the legacy compact-shell family hypothesis from
`OSToWightmanBoundaryValuesCompactApprox.lean` is composed immediately with
`compactApproxPositiveTime_timeShift_eq_osHolomorphicValue_of_singleSplit_eq_bvt_W_on_positiveReals`,
and the result is fed to the existing fixed-surrogate on-image reducer. -/
theorem
    bvt_wightmanInner_self_nonneg_of_compactApproxPositiveTime_onImage_of_component_zero_and_singleSplit_eq_bvt_W_on_positiveReals
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d)
    (hF0 : (((F : BorchersSequence d).funcs 0 : SchwartzNPoint d 0)) = 0)
    (hlegacy :
      ∀ N n k (hk_pos : 0 < k) (t : ℝ), 0 < t →
        let F_N : PositiveTimeBorchersSequence d := compactApproxPositiveTimeBorchers (d := d) F N;
          bvt_singleSplit_xiShiftHolomorphicValue
            (d := d) OS lgc hk_pos
            (((F_N : BorchersSequence d).funcs n))
            (F_N.ordered_tsupport n)
            (compactApproxPositiveTimeBorchers_component_compact (d := d) F N n)
            (((F_N : BorchersSequence d).funcs k))
            (F_N.ordered_tsupport k)
            (compactApproxPositiveTimeBorchers_component_compact (d := d) F N k) (t : ℂ)
          =
            bvt_W OS lgc (n + k)
              (((F_N : BorchersSequence d).funcs n).conjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t
                  ((F_N : BorchersSequence d).funcs k)))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d)).re := by
  have hreal :
      ∀ N n k,
          n ≤ (compactApproxPositiveTimeBorchers (d := d) F N : BorchersSequence d).bound →
          k ≤ (compactApproxPositiveTimeBorchers (d := d) F N : BorchersSequence d).bound →
          (hk_pos : 0 < k) →
          ∀ t : ℝ, 0 < t →
            bvt_W OS lgc (n + k)
              (((((compactApproxPositiveTimeBorchers (d := d) F N :
                      PositiveTimeBorchersSequence d) :
                    BorchersSequence d).funcs n) : SchwartzNPoint d n).conjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t
                  ((((compactApproxPositiveTimeBorchers (d := d) F N :
                        PositiveTimeBorchersSequence d) :
                      BorchersSequence d).funcs k) : SchwartzNPoint d k))) =
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n
                ((((compactApproxPositiveTimeBorchers (d := d) F N :
                      PositiveTimeBorchersSequence d) :
                    BorchersSequence d).funcs n) : SchwartzNPoint d n)
                ((compactApproxPositiveTimeBorchers (d := d) F N :
                    PositiveTimeBorchersSequence d).ordered_tsupport n))
              (PositiveTimeBorchersSequence.single k
                ((((compactApproxPositiveTimeBorchers (d := d) F N :
                      PositiveTimeBorchersSequence d) :
                    BorchersSequence d).funcs k) : SchwartzNPoint d k)
                ((compactApproxPositiveTimeBorchers (d := d) F N :
                    PositiveTimeBorchersSequence d).ordered_tsupport k)) (t : ℂ) :=
    compactApproxPositiveTime_timeShift_eq_osHolomorphicValue_of_singleSplit_eq_bvt_W_on_positiveReals
      (d := d) OS lgc F hlegacy
  exact
    bvt_wightmanInner_self_nonneg_of_compactApproxPositiveTime_onImage_of_component_zero_and_timeShift_eq_on_positiveReals
      (d := d) OS lgc F hF0 hreal

/-!
Package I transport note:

The old placeholder `def := by sorry` transport route has been removed. The
current live Package-I frontier is now:
1. establish the transformed-image quadratic identity,
2. then close positivity from the transformed-image core using the already-built
   Hilbert-space density of positive-time vectors.

For the current theorem-3 blocker, the missing input is now earlier than every
closure theorem in this file. Source extraction narrows the paper content to:

- OS I, p. 95, Lemma 4.1: dense transformed-image map into an ambient test
  subspace `L`;
- OS I, p. 96, (4.24)-(4.28): quadratic identity on that transformed-image
  shell;
- OS II, p. 289, Theorem 4.3 plus Chapter V / VI: continuation, bounds, and
  boundary values for the reconstructed Wightman distributions.

What the papers do not provide is an ambient theorem that, for an arbitrary
public target, constructs a replacement in that shell or proves equality of
quadratic forms after such a replacement. So the missing input here is an
ambient-side replacement/pairing-preservation surface that lands a general
public target in the boundary-vanishing class before the consumers
`bvt_wightmanInner_self_nonneg_family_onImage_of_zero_right_and_matrix_element_time_interchange`
and
`bvt_wightmanInner_self_nonneg_of_eq_boundaryVanishingTarget`
can be applied. The present on-image package does not construct that
replacement; it only consumes it.

More sharply: below the now-landed supplier-data theorem
`exists_bounded_componentwise_onImage_supplier_data_of_preimageFamilies`, the
exact earliest remaining producer is the positive-real comparison payload
`hreal` on those same explicit ambient/preimage inputs (or an immediately
equivalent antecedent theorem whose output composes directly to `hreal`). It
is not a further compact-family wrapper.
-/

end OSReconstruction
