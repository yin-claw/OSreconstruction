import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedSchurPropagation

/-!
# Reconstruction from source-oriented Schur residual data

This small companion exposes the endpoint reconstruction theorem in the exact
shape consumed by the rank-deficient local-image route: once Schur residual
data have been produced and the shifted residual tail has been realized by
tail coordinates, the normal-parameter source tuple realizes the original
oriented source datum.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Reconstruction from Schur residual data and a realizing shifted residual
tail tuple. -/
theorem sourceOriented_reconstruct_from_schurResidual
    (d n r : ℕ)
    (hn : d + 1 ≤ n)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (R : SourceOrientedSchurResidualData d n r hrD hrn G)
    {q : Fin (n - r) → Fin (d + 1 - r) → ℂ}
    (hq :
      sourceShiftedTailOrientedInvariant d r hrD (n - r) q = R.tail) :
    sourceOrientedMinkowskiInvariant d n
      (sourceOrientedNormalParameterVector d n r hrD hrn
        { head := R.headFactor
          mixed := R.L
          tail := q }) = G := by
  exact
    sourceOrientedNormalParameterVector_realizes_schur
      d n r hn hrD hrn hGvar R rfl rfl hq

/-- Existential source-tuple form of
`sourceOriented_reconstruct_from_schurResidual`. -/
theorem exists_sourceOriented_reconstruct_from_schurResidual
    (d n r : ℕ)
    (hn : d + 1 ≤ n)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (R : SourceOrientedSchurResidualData d n r hrD hrn G)
    {q : Fin (n - r) → Fin (d + 1 - r) → ℂ}
    (hq :
      sourceShiftedTailOrientedInvariant d r hrD (n - r) q = R.tail) :
    ∃ z : Fin n → Fin (d + 1) → ℂ,
      sourceOrientedMinkowskiInvariant d n z = G := by
  exact
    ⟨sourceOrientedNormalParameterVector d n r hrD hrn
        { head := R.headFactor
          mixed := R.L
          tail := q },
      sourceOriented_reconstruct_from_schurResidual
        d n r hn hrD hrn hGvar R hq⟩

end BHW
