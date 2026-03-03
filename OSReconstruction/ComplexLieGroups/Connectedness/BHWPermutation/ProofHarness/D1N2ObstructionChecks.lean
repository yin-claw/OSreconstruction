import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.PermutationFlowBlockers.Core

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter

namespace BHW

example : ¬ d1N2InvariantRealizable (-9 : ℂ) (-1 : ℂ) (-3 : ℂ) 0 :=
  d1N2InvariantRealizable_swappedProbe_not

example :
    ∃ f : ℂ → ℂ → ℂ → ℂ → ℂ,
      d1N2InvariantKernelSource f ∧
      ¬ d1N2InvariantKernelDiffZeroOnQuadric f :=
  d1N2InvariantKernelSource_not_sufficient_for_quadricDiffZero

end BHW

