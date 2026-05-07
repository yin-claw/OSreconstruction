import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientCanonicalImage
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedSlicedNormalParameterFinCoord
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedMaxRankIdentity

/-!
# Rank-deficient tube residual-polydisc assembly

This file begins the final downstream assembly of the rank-deficient
tube-valued residual polydisc.  The first checked step is the compact/open
Schur-window sandwich: the finite-coordinate image of the sliced Schur window
is forced into the compact tube-control ball, while the same sliced window is
fed to the canonical Schur image theorem.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW
namespace SourceOrientedRankDeficientNormalFormData

/-- Choose a sliced Schur window whose finite-coordinate image lies inside the
compact extended-tube control ball, and whose canonical sliced image is an
open source-variety neighborhood represented by the same window. -/
theorem exists_slicedSchurWindow_finCoordControl
    {d n : ℕ}
    [NeZero d]
    (hd : 2 ≤ d)
    (hn : d + 1 ≤ n)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0) :
    ∃ (ε headRadius mixedRadius : ℝ)
      (Tail : SourceOrientedRankDeficientTailWindowChoice d n N.r N.hrD N.hrn)
      (Ωv : Set (SourceOrientedVariety d n)),
      let W :=
        sourceOrientedRankDeficientSlicedSchurParameterWindow
          d n N.r N.hrD N.hrn headRadius mixedRadius Tail
      let e :=
        sourceOrientedSlicedNormalParameterFinCoordHomeomorph
          (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn)
      0 < ε ∧
        0 < headRadius ∧
        0 < mixedRadius ∧
        IsCompact
          (sourceOrientedSlicedNormalParameterFinCoordClosedBall
            d n N.r N.hrD N.hrn ε) ∧
        IsOpen W ∧
        sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn ∈ W ∧
        e '' W ⊆
          sourceOrientedSlicedNormalParameterFinCoordClosedBall
            d n N.r N.hrD N.hrn ε ∧
        (∀ c,
          c ∈ sourceOrientedSlicedNormalParameterFinCoordClosedBall
              d n N.r N.hrD N.hrn ε →
            N.toOriginal
                (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn
                  ((e.symm c).toNormalParameter)) ∈
              ExtendedTube d n) ∧
        IsOpen Ωv ∧
        Ωv ⊆
          sourceOrientedSlicedNormalParameterVarietyPoint
            d n N.r N.hrD N.hrn '' W ∧
        (∀ p, p ∈ W →
          sourceOrientedSlicedNormalParameterVarietyPoint
            d n N.r N.hrD N.hrn p ∈ Ωv) ∧
        (∀ p, p ∈ W → IsUnit p.toNormalParameter.head.det) := by
  rcases N.exists_slicedFinCoordCompactOpen_toOriginal_mem_ET with
    ⟨ε, hε, hK_compact, hB_open, hB_subset_K, hcenter_B, hK_tube⟩
  let e :=
    sourceOrientedSlicedNormalParameterFinCoordHomeomorph
      (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn)
  let B :=
    sourceOrientedSlicedNormalParameterFinCoordOpenBall
      d n N.r N.hrD N.hrn ε
  let U : Set (SourceOrientedRankDeficientSlicedNormalParameter d n N.r N.hrD N.hrn) :=
    e ⁻¹' B
  have hU :
      U ∈ 𝓝 (sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn) := by
    have hpre : e ⁻¹' B ∈
        𝓝 (sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn) :=
      e.continuous.continuousAt (hB_open.mem_nhds hcenter_B)
    simpa [U] using hpre
  let A := N.toAlgebraicNormalFormData
  let Head := sourceRankDeficientHeadSliceGaugeData d N.r N.hrD
  let headDomainRadius := Classical.choose Head.factorDomain_coordinate
  have hheadDomainSpec := Classical.choose_spec Head.factorDomain_coordinate
  rcases
      A.exists_slicedSchurParameterWindow_subset_nhds_image_subset_open_headDomain_tailRank_connected
        (d := d) (n := n) hn
        (U := U) hU
        (headDomain := Head.factorDomain)
        (headDomainRadius := headDomainRadius)
        hheadDomainSpec.1 hheadDomainSpec.2
        isOpen_univ (Set.mem_univ _) with
    ⟨headRadius, mixedRadius, Tail, hheadRadius, hmixedRadius, hdomain, hW_open,
      _hW_conn, hcenter_W, hW_sub_U, hhead_unit, _himage, _htailRank_conn⟩
  let W :=
    sourceOrientedRankDeficientSlicedSchurParameterWindow
      d n N.r N.hrD N.hrn headRadius mixedRadius Tail
  rcases
      sourceOrientedHeadSliceGaugeSchurWindowCanonicalImage
        (d := d) (n := n) hd hn (hrD := N.hrD) (hrn := N.hrn)
        Head Tail hdomain with
    ⟨Ωv, hΩv_open, hΩv_surj, hΩv_mem⟩
  have hW_closed :
      W ⊆ e ⁻¹'
        sourceOrientedSlicedNormalParameterFinCoordClosedBall
          d n N.r N.hrD N.hrn ε := by
    intro p hp
    exact hB_subset_K (hW_sub_U hp)
  have hP_subset_K :
      e '' W ⊆
        sourceOrientedSlicedNormalParameterFinCoordClosedBall
          d n N.r N.hrD N.hrn ε := by
    simpa [e] using
      sourceOrientedSlicedNormalParameterFinCoord_image_subset_closedBall
        (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn)
        (ε := ε) (W := W) hW_closed
  refine
    ⟨ε, headRadius, mixedRadius, Tail, Ωv, hε, hheadRadius, hmixedRadius,
      hK_compact, hW_open, hcenter_W, hP_subset_K, ?_, hΩv_open, hΩv_surj,
      hΩv_mem, hhead_unit⟩
  intro c hc
  simpa [e] using hK_tube c hc

end SourceOrientedRankDeficientNormalFormData

/-- Hard-range rank-deficient tube residual-polydisc constructor.  The compact
tube-control set is the checked finite-coordinate closed ball, while the open
parameter set is the finite-coordinate image of the sliced Schur window. -/
noncomputable def sourceOriented_rankDeficient_tubeResidualPolydisc_hardRange
    {d n : ℕ}
    [NeZero d]
    (hd : 2 ≤ d)
    (hn : d + 1 ≤ n)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0) :
    SourceOrientedResidualPolydiscData d n N := by
  let hcontrol_exists := N.exists_slicedSchurWindow_finCoordControl hd hn
  let ε := Classical.choose hcontrol_exists
  let hcontrol_exists₁ := Classical.choose_spec hcontrol_exists
  let headRadius := Classical.choose hcontrol_exists₁
  let hcontrol_exists₂ := Classical.choose_spec hcontrol_exists₁
  let mixedRadius := Classical.choose hcontrol_exists₂
  let hcontrol_exists₃ := Classical.choose_spec hcontrol_exists₂
  let Tail := Classical.choose hcontrol_exists₃
  let hcontrol_exists₄ := Classical.choose_spec hcontrol_exists₃
  let Ωv := Classical.choose hcontrol_exists₄
  let hcontrol := Classical.choose_spec hcontrol_exists₄
  let W :=
    sourceOrientedRankDeficientSlicedSchurParameterWindow
      d n N.r N.hrD N.hrn headRadius mixedRadius Tail
  let e :=
    sourceOrientedSlicedNormalParameterFinCoordHomeomorph
      (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn)
  let K :=
    sourceOrientedSlicedNormalParameterFinCoordClosedBall
      d n N.r N.hrD N.hrn ε
  let P : Set (Fin (sourceOrientedSlicedNormalParameterFinCoordDim d n N.r) → ℂ) :=
    e '' W
  let residualVector :
      (Fin (sourceOrientedSlicedNormalParameterFinCoordDim d n N.r) → ℂ) →
        Fin n → Fin (d + 1) → ℂ :=
    fun c =>
      sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn
        ((e.symm c).toNormalParameter)
  let image :
      (Fin (sourceOrientedSlicedNormalParameterFinCoordDim d n N.r) → ℂ) →
        SourceOrientedGramData d n :=
    fun c => sourceOrientedMinkowskiInvariant d n (N.toOriginal (residualVector c))
  rcases hcontrol with
    ⟨_hε, _hheadRadius, _hmixedRadius, hK_compact, hW_open, hcenter_W,
      hP_subset_K, hK_tube, hΩv_open, hΩv_surj, hΩv_mem, _hhead_unit⟩
  have hc0P :
      sourceOrientedSlicedNormalParameterFinCenterCoord d n N.r N.hrD N.hrn ∈ P := by
    simpa [P, e] using
      sourceOrientedSlicedNormalParameterFinCenterCoord_mem_image
        (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn)
        (W := W) hcenter_W
  have hcenter_symm :
      e.symm (sourceOrientedSlicedNormalParameterFinCenterCoord
          d n N.r N.hrD N.hrn) =
        sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn := by
    rw [← sourceOrientedSlicedNormalParameterFinCoordHomeomorph_center
      d n N.r N.hrD N.hrn]
    simp [e]
  have hresidual_center :
      residualVector
          (sourceOrientedSlicedNormalParameterFinCenterCoord
            d n N.r N.hrD N.hrn) =
        N.normalBase := by
    dsimp [residualVector]
    rw [hcenter_symm]
    rw [sourceOrientedSlicedNormalCenterParameter_toNormalParameter]
    rw [sourceOrientedNormalParameterVector_center]
    exact N.normalBase_eq.symm
  let Uvar : Set (SourceOrientedGramData d n) :=
    sourceOrientedVarietyUnderlyingSet d n (N.varietyTransport.invFun '' Ωv)
  let hUvar_rel :
      IsRelOpenInSourceOrientedGramVariety d n Uvar := by
    change
      IsRelOpenInSourceOrientedGramVariety d n
        (sourceOrientedVarietyUnderlyingSet d n
          (N.varietyTransport.invFun '' Classical.choose hcontrol_exists₄))
    exact
      sourceOrientedVarietyTransport_invFun_image_underlying_relOpen
        (d := d) (n := n) N.varietyTransport hΩv_open
  let Ω := Classical.choose hUvar_rel
  have hΩ_spec := Classical.choose_spec hUvar_rel
  have hΩ_open : IsOpen Ω := hΩ_spec.1
  have hΩ_eq : Uvar = Ω ∩ sourceOrientedGramVariety d n := hΩ_spec.2
  have hmem_bridge :
      ∀ c, c ∈ P → image c ∈ Uvar := by
    intro c hc
    simpa [P, e, residualVector, image, Uvar] using
      N.slicedFinCoord_originalImage_mem_varietyTransport
        (W := W) (Ω := Ωv) hΩv_mem c hc
  have hsurj_bridge :
      Uvar ⊆ image '' P := by
    intro G hG
    simpa [P, e, residualVector, image, Uvar] using
      N.slicedFinCoord_originalImage_surj_varietyTransport
        (W := W) (Ω := Ωv) hΩv_surj hG
  have hΩ_center_pair :
      sourceOrientedMinkowskiInvariant d n z0 ∈ Ω ∩ sourceOrientedGramVariety d n := by
    have hcenter_mem : image
        (sourceOrientedSlicedNormalParameterFinCenterCoord
          d n N.r N.hrD N.hrn) ∈ Uvar :=
      hmem_bridge _ hc0P
    have hcenter_mem' :
        sourceOrientedMinkowskiInvariant d n z0 ∈ Uvar := by
      simpa [image, residualVector, hresidual_center,
        N.toOriginal_normalBase_invariant] using hcenter_mem
    simpa [hΩ_eq] using hcenter_mem'
  refine
    { m := sourceOrientedSlicedNormalParameterFinCoordDim d n N.r
      c0 := sourceOrientedSlicedNormalParameterFinCenterCoord d n N.r N.hrD N.hrn
      K := K
      P := P
      K_compact := hK_compact
      P_open := by
        simpa [P, e] using
          isOpen_sourceOrientedSlicedNormalParameterFinCoord_image
            (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn)
            (W := W) hW_open
      P_subset_K := hP_subset_K
      c0_mem := hc0P
      residualVector := residualVector
      residualVector_continuousOn := by
        simpa [K, e, residualVector] using
          N.continuousOn_slicedFinCoord_normalParameterVector_closedBall ε
      residualVector_c0 := hresidual_center
      toOriginal_residualVector_mem_ET := by
        intro c hc
        simpa [K, e, residualVector] using hK_tube c hc
      Ω := Ω
      Ω_open := hΩ_open
      Ω_center := hΩ_center_pair.1
      originalInvariant_mem := by
        intro c hc
        have hcU : image c ∈ Uvar := hmem_bridge c hc
        simpa [image, hΩ_eq] using hcU
      image_surj := by
        intro G hG
        have hGU : G ∈ Uvar := by
          simpa [hΩ_eq] using hG
        simpa [image] using hsurj_bridge hGU
      maxRank_dense_original := by
        intro c hcP
        have hcU : image c ∈ Uvar := hmem_bridge c hcP
        have hdenseU :
            image c ∈
              closure (Uvar ∩ {G | SourceOrientedMaxRankAt d n G}) :=
          sourceOrientedMaxRank_dense_in_relOpen_inter
            (d := d) (n := n) hn hUvar_rel hcU
        have hsubset :
            Uvar ∩ {G | SourceOrientedMaxRankAt d n G} ⊆
              image ''
                {c' | c' ∈ P ∧ SourceOrientedMaxRankAt d n (image c')} := by
          intro G hG
          rcases hsurj_bridge hG.1 with ⟨c', hc'P, hc'eq⟩
          refine ⟨c', ⟨hc'P, ?_⟩, hc'eq⟩
          simpa [hc'eq] using hG.2
        exact closure_mono hsubset hdenseU }
end BHW
