import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45BHWJost
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedContinuationProducers

/-!
# OS45 BHW/Jost oriented continuation consumers

This file specializes the checked source-oriented BHW/Jost continuation
consumer to the OS45 source-patch hull.  The hard Hall-Wightman/Jost analytic
inputs remain explicit parameters: source-normal-form patches, uniform
oriented descent, one-step uniqueness, and retargeted terminal comparisons.
-/

noncomputable section

open Complex Topology LorentzLieGroup

namespace BHW

variable {d n : ℕ} [NeZero d]

/-- Wick rotation of an ordered Euclidean source point lands in the BHW
forward tube, in the namespace convention used by `extendF`. -/
theorem wickRotate_mem_BHW_forwardTube_of_ordered
    {x : NPointDomain d n}
    (hx_ordered :
      x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
        (1 : Equiv.Perm (Fin n))) :
    (fun k => wickRotatePoint (x k)) ∈ BHW.ForwardTube d n := by
  have hroot :
      (fun k => wickRotatePoint (x ((1 : Equiv.Perm (Fin n)) k))) ∈
        _root_.ForwardTube d n :=
    wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector
      (d := d) (n := n) (1 : Equiv.Perm (Fin n)) hx_ordered
  simpa [BHW_forwardTube_eq (d := d) (n := n)] using hroot

/-- On an ordered Euclidean source point, the selected BHW extension agrees
with the original boundary-value witness. -/
theorem extendF_bvt_F_wickRotate_eq_of_ordered
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) {x : NPointDomain d n}
    (hx_ordered :
      x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
        (1 : Equiv.Perm (Fin n))) :
    BHW.extendF (bvt_F OS lgc n) (fun k => wickRotatePoint (x k)) =
      bvt_F OS lgc n (fun k => wickRotatePoint (x k)) := by
  have hF_holo :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_lorentz :
      ∀ (Λ : RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n
          (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
        bvt_F OS lgc n z := by
    intro Λ z hz
    exact bvt_F_restrictedLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
  exact
    BHW.extendF_eq_on_forwardTube n (bvt_F OS lgc n)
      hF_holo hF_lorentz (fun k => wickRotatePoint (x k))
      (BHW.wickRotate_mem_BHW_forwardTube_of_ordered
        (d := d) (n := n) hx_ordered)

/-- If a stored OS45 source-patch hull is known to be an ordered Euclidean
source patch, then its Wick trace lands in the ordinary BHW forward tube. -/
theorem OS45SourcePatchBHWJostHullData.wick_id_forwardTube_of_ordered
    {hd : 2 ≤ d}
    {OS : OsterwalderSchraderAxioms d}
    {lgc : OSLinearGrowthCondition d OS}
    {i : Fin n} {hi : i.val + 1 < n}
    {V : Set (NPointDomain d n)}
    (_H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V)
    (hV_ordered :
      ∀ x, x ∈ V →
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          (1 : Equiv.Perm (Fin n))) :
    ∀ x, x ∈ V →
      (fun k => wickRotatePoint (x k)) ∈ BHW.ForwardTube d n := by
  intro x hx
  exact
    BHW.wickRotate_mem_BHW_forwardTube_of_ordered
      (d := d) (n := n) (hV_ordered x hx)

/-- Exact analytic inputs needed by the checked strict source-oriented
continuation consumer.  This is intentionally an input surface, not a theorem:
the Hall-Wightman/Jost work is in `patchAt`, `uniformDescent`,
`uniformDescent_unique`, and `retargetedComparison`. -/
structure OS45SourcePatchBHWJostOrientedContinuationInputs
    (hd : 2 ≤ d)
    (n : ℕ) (τ : Equiv.Perm (Fin n))
    (Ω0 U : Set (Fin n → Fin (d + 1) → ℂ))
    (B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ) where
  p0 : Fin n → Fin (d + 1) → ℂ
  base_mem : p0 ∈ Ω0 ∩ U
  patchAt :
    ∀ {center : Fin n → Fin (d + 1) → ℂ}, center ∈ U →
      BHWJostOrientedSourceNormalFormGeometryPatch hd n τ U center
  uniformDescent :
    ∀ {center : Fin n → Fin (d + 1) → ℂ}
      (hcenter : center ∈ U),
      ∀ p q,
        p ∈ (patchAt hcenter).carrier → p ∈ U →
        q ∈ (patchAt hcenter).carrier → q ∈ U →
        ∀ Cprev : BHWJostLocalOrientedContinuationChart hd n τ U,
          p ∈ Cprev.carrier →
            Σ Cnext : BHWJostLocalOrientedContinuationChart hd n τ U,
              BHWJostOrientedTransitionData hd n τ U Cprev Cnext p q
  uniformDescent_unique :
    ∀ z (hz : z ∈ U),
      BHWJostOrientedTransferControlHasUniqueNext
        (BHWJostOrientedBranchFreeTransferNeighborhood.toTransferControl
          (bhw_jost_orientedBranchFreeTransferNeighborhood_at_of_sourceNormalFormProducer
            (hd := hd) (τ := τ) (U := U)
            patchAt uniformDescent hz))
  retargetedComparison :
    ∀ {y : Fin n → Fin (d + 1) → ℂ}
      (T₁ T₂ :
        BHWJostOrientedCertifiedTransferTerminalPointTrace
          hd n τ Ω0 U B0 p0 y),
      BHWOrientedTerminalChainComparisonData
        (T₁.trace.trace.chain.retargetTerminal T₁.point_mem)
        (T₂.trace.trace.chain.retargetTerminal T₂.point_mem)
  C0 : BHWJostLocalOrientedContinuationChart hd n τ U
  hp0C : p0 ∈ C0.carrier
  start_patch : Set (Fin n → Fin (d + 1) → ℂ)
  start_open : IsOpen start_patch
  start_preconnected : IsPreconnected start_patch
  start_nonempty : start_patch.Nonempty
  start_mem : p0 ∈ start_patch
  start_sub : start_patch ⊆ Ω0 ∩ C0.carrier
  start_agree : ∀ y, y ∈ start_patch → C0.branch y = B0 y
  initial_chart_mem : ∀ z, z ∈ Ω0 ∩ U → z ∈ C0.carrier
  initial_branch_agree : ∀ z, z ∈ Ω0 ∩ U → C0.branch z = B0 z

namespace OS45SourcePatchBHWJostOrientedContinuationInputs

variable {hd : 2 ≤ d} {τ : Equiv.Perm (Fin n)}
variable {Ω0 U : Set (Fin n → Fin (d + 1) → ℂ)}
variable {B0 : (Fin n → Fin (d + 1) → ℂ) → ℂ}

/-- The checked strict source-oriented continuation consumer applied to the
OS45 input surface. -/
theorem exists_gluedBranch
    (I : BHW.OS45SourcePatchBHWJostOrientedContinuationInputs
      (d := d) hd n τ Ω0 U B0)
    (hU_path : IsPathConnected U) :
    ∃ B : (Fin n → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ B U ∧
      (∀ z, z ∈ Ω0 → z ∈ U → B z = B0 z) :=
  BHW.bhw_jost_orientedGluedBranch_of_pathConnected_sourceNormalFormProducer_retargetedComparisons
    (hd := hd) (τ := τ) (Ω0 := Ω0) (U := U) (B0 := B0)
    I.p0 I.base_mem hU_path I.patchAt I.uniformDescent
    I.uniformDescent_unique I.retargetedComparison I.C0 I.hp0C
    I.start_patch I.start_open I.start_preconnected I.start_nonempty
    I.start_mem I.start_sub I.start_agree I.initial_chart_mem
    I.initial_branch_agree

end OS45SourcePatchBHWJostOrientedContinuationInputs

namespace OS45SourcePatchBHWJostHullData

variable {hd : 2 ≤ d}
variable {OS : OsterwalderSchraderAxioms d}
variable {lgc : OSLinearGrowthCondition d OS}
variable {i : Fin n} {hi : i.val + 1 < n}
variable {V : Set (NPointDomain d n)}

/-- Ordinary source-patch branch produced from the strict oriented
continuation inputs on the ordinary extended tube. -/
theorem exists_ordinaryBranch_of_orientedContinuationInputs
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V)
    (hV_ordered :
      ∀ x, x ∈ V →
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)))
    (I : BHW.OS45SourcePatchBHWJostOrientedContinuationInputs
      (d := d) hd n H.τ (BHW.ExtendedTube d n) H.U
      (BHW.extendF (bvt_F OS lgc n))) :
    ∃ Bord : (Fin n → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ Bord H.U ∧
      (∀ x, x ∈ V →
        Bord (fun k => wickRotatePoint (x k)) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x k))) ∧
      (∀ x, x ∈ V →
        Bord (BHW.realEmbed x) =
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x)) := by
  rcases I.exists_gluedBranch H.U_isPathConnected with
    ⟨Bord, hBord_holo, hBord_agree⟩
  refine ⟨Bord, hBord_holo, ?_, ?_⟩
  · intro x hx
    have hcontinue :
        Bord (fun k => wickRotatePoint (x k)) =
          BHW.extendF (bvt_F OS lgc n)
            (fun k => wickRotatePoint (x k)) :=
      hBord_agree (fun k => wickRotatePoint (x k))
        (H.wick_id_ET x hx) (H.wick_id_mem x hx)
    exact hcontinue.trans
      (BHW.extendF_bvt_F_wickRotate_eq_of_ordered
        (d := d) OS lgc n (hV_ordered x hx))
  · intro x hx
    exact hBord_agree (BHW.realEmbed x)
      (H.real_id_ET x hx) (H.real_id_mem x hx)

/-- Adjacent source-patch branch produced from the strict oriented
continuation inputs on the permutation preimage of the ordinary extended tube.
The Wick trace is not asserted here; it remains the OS I/BHW continuation
datum for the adjacent Wick edge. -/
theorem exists_adjacentBranch_of_orientedContinuationInputs
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V)
    (I : BHW.OS45SourcePatchBHWJostOrientedContinuationInputs
      (d := d) hd n H.τ
      {z | BHW.permAct (d := d) H.τ z ∈ BHW.ExtendedTube d n}
      H.U
      (fun z =>
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) H.τ z))) :
    ∃ Btau : (Fin n → Fin (d + 1) → ℂ) → ℂ,
      DifferentiableOn ℂ Btau H.U ∧
      (∀ x, x ∈ V →
        Btau (BHW.realEmbed x) =
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => x (H.τ k)))) ∧
      (∀ z,
        z ∈ {z | BHW.permAct (d := d) H.τ z ∈ BHW.ExtendedTube d n} →
        z ∈ H.U →
          Btau z =
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) H.τ z)) := by
  rcases I.exists_gluedBranch H.U_isPathConnected with
    ⟨Btau, hBtau_holo, hBtau_agree⟩
  refine ⟨Btau, hBtau_holo, ?_, hBtau_agree⟩
  intro x hx
  have hcontinue :
      Btau (BHW.realEmbed x) =
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) H.τ (BHW.realEmbed x)) :=
    hBtau_agree (BHW.realEmbed x)
      (H.real_tau_ET x hx) (H.real_id_mem x hx)
  simpa [BHW.permAct_realEmbed] using hcontinue

/-- The ordinary branch selected from the checked strict-oriented continuation
input packet. -/
noncomputable def ordinaryBranchOfOrientedContinuationInputs
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V)
    (hV_ordered :
      ∀ x, x ∈ V →
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)))
    (I : BHW.OS45SourcePatchBHWJostOrientedContinuationInputs
      (d := d) hd n H.τ (BHW.ExtendedTube d n) H.U
      (BHW.extendF (bvt_F OS lgc n))) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  Classical.choose (H.exists_ordinaryBranch_of_orientedContinuationInputs
    hV_ordered I)

theorem ordinaryBranchOfOrientedContinuationInputs_spec
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V)
    (hV_ordered :
      ∀ x, x ∈ V →
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)))
    (I : BHW.OS45SourcePatchBHWJostOrientedContinuationInputs
      (d := d) hd n H.τ (BHW.ExtendedTube d n) H.U
      (BHW.extendF (bvt_F OS lgc n))) :
    DifferentiableOn ℂ
        (H.ordinaryBranchOfOrientedContinuationInputs hV_ordered I) H.U ∧
      (∀ x, x ∈ V →
        H.ordinaryBranchOfOrientedContinuationInputs hV_ordered I
          (fun k => wickRotatePoint (x k)) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x k))) ∧
      (∀ x, x ∈ V →
        H.ordinaryBranchOfOrientedContinuationInputs hV_ordered I
          (BHW.realEmbed x) =
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x)) :=
  Classical.choose_spec
    (H.exists_ordinaryBranch_of_orientedContinuationInputs hV_ordered I)

theorem ordinaryBranchOfOrientedContinuationInputs_holo
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V)
    (hV_ordered :
      ∀ x, x ∈ V →
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)))
    (I : BHW.OS45SourcePatchBHWJostOrientedContinuationInputs
      (d := d) hd n H.τ (BHW.ExtendedTube d n) H.U
      (BHW.extendF (bvt_F OS lgc n))) :
    DifferentiableOn ℂ
      (H.ordinaryBranchOfOrientedContinuationInputs hV_ordered I) H.U :=
  (H.ordinaryBranchOfOrientedContinuationInputs_spec hV_ordered I).1

theorem ordinaryBranchOfOrientedContinuationInputs_wick_trace
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V)
    (hV_ordered :
      ∀ x, x ∈ V →
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)))
    (I : BHW.OS45SourcePatchBHWJostOrientedContinuationInputs
      (d := d) hd n H.τ (BHW.ExtendedTube d n) H.U
      (BHW.extendF (bvt_F OS lgc n))) :
    ∀ x, x ∈ V →
      H.ordinaryBranchOfOrientedContinuationInputs hV_ordered I
        (fun k => wickRotatePoint (x k)) =
        bvt_F OS lgc n (fun k => wickRotatePoint (x k)) :=
  (H.ordinaryBranchOfOrientedContinuationInputs_spec hV_ordered I).2.1

theorem ordinaryBranchOfOrientedContinuationInputs_real_trace
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V)
    (hV_ordered :
      ∀ x, x ∈ V →
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)))
    (I : BHW.OS45SourcePatchBHWJostOrientedContinuationInputs
      (d := d) hd n H.τ (BHW.ExtendedTube d n) H.U
      (BHW.extendF (bvt_F OS lgc n))) :
    ∀ x, x ∈ V →
      H.ordinaryBranchOfOrientedContinuationInputs hV_ordered I
        (BHW.realEmbed x) =
        BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) :=
  (H.ordinaryBranchOfOrientedContinuationInputs_spec hV_ordered I).2.2

/-- The adjacent branch selected from the checked strict-oriented continuation
input packet. -/
noncomputable def adjacentBranchOfOrientedContinuationInputs
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V)
    (I : BHW.OS45SourcePatchBHWJostOrientedContinuationInputs
      (d := d) hd n H.τ
      {z | BHW.permAct (d := d) H.τ z ∈ BHW.ExtendedTube d n}
      H.U
      (fun z =>
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) H.τ z))) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  Classical.choose (H.exists_adjacentBranch_of_orientedContinuationInputs I)

theorem adjacentBranchOfOrientedContinuationInputs_spec
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V)
    (I : BHW.OS45SourcePatchBHWJostOrientedContinuationInputs
      (d := d) hd n H.τ
      {z | BHW.permAct (d := d) H.τ z ∈ BHW.ExtendedTube d n}
      H.U
      (fun z =>
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) H.τ z))) :
    DifferentiableOn ℂ
        (H.adjacentBranchOfOrientedContinuationInputs I) H.U ∧
      (∀ x, x ∈ V →
        H.adjacentBranchOfOrientedContinuationInputs I (BHW.realEmbed x) =
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => x (H.τ k)))) ∧
      (∀ z,
        z ∈ {z | BHW.permAct (d := d) H.τ z ∈ BHW.ExtendedTube d n} →
        z ∈ H.U →
          H.adjacentBranchOfOrientedContinuationInputs I z =
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) H.τ z)) :=
  Classical.choose_spec
    (H.exists_adjacentBranch_of_orientedContinuationInputs I)

theorem adjacentBranchOfOrientedContinuationInputs_holo
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V)
    (I : BHW.OS45SourcePatchBHWJostOrientedContinuationInputs
      (d := d) hd n H.τ
      {z | BHW.permAct (d := d) H.τ z ∈ BHW.ExtendedTube d n}
      H.U
      (fun z =>
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) H.τ z))) :
    DifferentiableOn ℂ
      (H.adjacentBranchOfOrientedContinuationInputs I) H.U :=
  (H.adjacentBranchOfOrientedContinuationInputs_spec I).1

theorem adjacentBranchOfOrientedContinuationInputs_real_trace
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V)
    (I : BHW.OS45SourcePatchBHWJostOrientedContinuationInputs
      (d := d) hd n H.τ
      {z | BHW.permAct (d := d) H.τ z ∈ BHW.ExtendedTube d n}
      H.U
      (fun z =>
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) H.τ z))) :
    ∀ x, x ∈ V →
      H.adjacentBranchOfOrientedContinuationInputs I (BHW.realEmbed x) =
        BHW.extendF (bvt_F OS lgc n)
          (BHW.realEmbed (fun k => x (H.τ k))) :=
  (H.adjacentBranchOfOrientedContinuationInputs_spec I).2.1

theorem adjacentBranchOfOrientedContinuationInputs_initial_agree
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V)
    (I : BHW.OS45SourcePatchBHWJostOrientedContinuationInputs
      (d := d) hd n H.τ
      {z | BHW.permAct (d := d) H.τ z ∈ BHW.ExtendedTube d n}
      H.U
      (fun z =>
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) H.τ z))) :
    ∀ z,
      z ∈ {z | BHW.permAct (d := d) H.τ z ∈ BHW.ExtendedTube d n} →
      z ∈ H.U →
        H.adjacentBranchOfOrientedContinuationInputs I z =
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) H.τ z) :=
  (H.adjacentBranchOfOrientedContinuationInputs_spec I).2.2

/-- Assemble the checked OS45 source-patch pair carrier from the two strict
oriented continuation input packets and the remaining adjacent Wick-trace
datum. -/
noncomputable def pairDataOfOrientedContinuationInputs
    (H : BHW.OS45SourcePatchBHWJostHullData
      (d := d) hd OS lgc n i hi V)
    (hV_ordered :
      ∀ x, x ∈ V →
        x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)))
    (Iord : BHW.OS45SourcePatchBHWJostOrientedContinuationInputs
      (d := d) hd n H.τ (BHW.ExtendedTube d n) H.U
      (BHW.extendF (bvt_F OS lgc n)))
    (Iadj : BHW.OS45SourcePatchBHWJostOrientedContinuationInputs
      (d := d) hd n H.τ
      {z | BHW.permAct (d := d) H.τ z ∈ BHW.ExtendedTube d n}
      H.U
      (fun z =>
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) H.τ z)))
    (adjacent_wick_trace :
      ∀ x, x ∈ V →
        H.adjacentBranchOfOrientedContinuationInputs Iadj
          (fun k => wickRotatePoint (x k)) =
          bvt_F OS lgc n (fun k => wickRotatePoint (x (H.τ k)))) :
    BHW.OS45SourcePatchBHWJostPairData
      (d := d) hd OS lgc n i hi V :=
  BHW.OS45SourcePatchBHWJostPairData.ofHullDataAndBranches
    (d := d) H
    (H.ordinaryBranchOfOrientedContinuationInputs hV_ordered Iord)
    (H.adjacentBranchOfOrientedContinuationInputs Iadj)
    (H.ordinaryBranchOfOrientedContinuationInputs_holo hV_ordered Iord)
    (H.adjacentBranchOfOrientedContinuationInputs_holo Iadj)
    (H.ordinaryBranchOfOrientedContinuationInputs_wick_trace hV_ordered Iord)
    adjacent_wick_trace
    (H.ordinaryBranchOfOrientedContinuationInputs_real_trace hV_ordered Iord)
    (H.adjacentBranchOfOrientedContinuationInputs_real_trace Iadj)

end OS45SourcePatchBHWJostHullData

end BHW
