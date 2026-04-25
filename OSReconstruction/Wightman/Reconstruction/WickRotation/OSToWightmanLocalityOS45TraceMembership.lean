import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45CommonChart
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45BranchPullback

noncomputable section

namespace BHW

variable {d n : ℕ} [NeZero d]

/-- The two adjacent ordered Wick traces used in the OS45 common chart both lie
in the OS-II ACR-one domain. -/
theorem adjacent_wick_traces_mem_acrOne
    (i : Fin n) (hi : i.val + 1 < n)
    (ρ : Equiv.Perm (Fin n))
    {x : NPointDomain d n}
    (hx_ordered :
      x ∈ EuclideanOrderedPositiveTimeSector (d := d) (n := n) ρ)
    (hx_swap_ordered :
      (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        EuclideanOrderedPositiveTimeSector (d := d) (n := n)
          ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)) :
    BHW.permAct (d := d) ρ (fun k => wickRotatePoint (x k)) ∈
        AnalyticContinuationRegion d n 1 ∧
    BHW.permAct (d := d) ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
        (BHW.permAct (d := d) (Equiv.swap i ⟨i.val + 1, hi⟩)
          (fun k => wickRotatePoint (x k))) ∈
        AnalyticContinuationRegion d n 1 := by
  constructor
  · exact BHW.wickRotate_ordered_mem_acrOne (d := d) (n := n) ρ hx_ordered
  · simpa [BHW.permAct_wickRotatePoint] using
      BHW.wickRotate_ordered_mem_acrOne
        (d := d) (n := n)
        ((Equiv.swap i ⟨i.val + 1, hi⟩).symm * ρ)
        hx_swap_ordered

/-- The common OS45 real chart point lies in both pulled real-branch domains
for the original branch and the adjacent relabelled branch. -/
theorem os45CommonChart_real_mem_pulledRealBranchDomain_pair
    (τ ρ : Equiv.Perm (Fin n))
    {x : NPointDomain d n}
    (hx_ET : BHW.realEmbed x ∈ BHW.ExtendedTube d n)
    (hxτ_ET : BHW.realEmbed (fun k => x (τ k)) ∈ BHW.ExtendedTube d n) :
    BHW.os45CommonChartCLE (d := d) (n := n) ρ (BHW.realEmbed x) ∈
      BHW.os45PulledRealBranchDomain (d := d) (n := n) ρ ∩
        BHW.os45PulledRealBranchDomain (d := d) (n := n) (τ.symm * ρ) := by
  constructor
  · have hmem :=
      BHW.os45QuarterTurn_perm_realEmbed_mem_os45PulledRealBranchDomain
        (d := d) (n := n) ρ x hx_ET
    simpa using hmem
  · have hmem :=
      BHW.os45QuarterTurn_perm_realEmbed_mem_os45PulledRealBranchDomain
        (d := d) (n := n) (τ.symm * ρ) (fun k => x (τ k)) hxτ_ET
    have hmem' :
        BHW.os45QuarterTurnConfig (d := d) (n := n)
            (fun k => BHW.realEmbed (fun j => x (τ j)) ((τ.symm * ρ) k)) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) (τ.symm * ρ) := by
      simpa [Equiv.Perm.mul_apply] using hmem
    have hcommon :
        BHW.os45QuarterTurnConfig
            (d := d) (n := n) (fun k => BHW.realEmbed x (ρ k)) ∈
          BHW.os45PulledRealBranchDomain (d := d) (n := n) (τ.symm * ρ) := by
      have hchart :=
        BHW.os45QuarterTurnConfig_reindexed_realBranch_eq
          (d := d) (n := n) τ ρ x
      exact hchart ▸ hmem'
    simpa using hcommon

end BHW
