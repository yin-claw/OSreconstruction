import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedContinuation

/-!
# Transport equivalences for oriented source invariants

The rank-deficient normal-form route transports a normal Schur chart back to
the original oriented source coordinates.  This file records the purely
topological/algebraic interface for such transports.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- A homeomorphic change of oriented source-invariant coordinates preserving
the oriented source variety and the maximal-rank predicate. -/
structure SourceOrientedInvariantTransportEquiv (d n : ℕ) where
  toHomeomorph :
    SourceOrientedGramData d n ≃ₜ SourceOrientedGramData d n
  mem_variety_iff :
    ∀ G,
      toHomeomorph G ∈ sourceOrientedGramVariety d n ↔
        G ∈ sourceOrientedGramVariety d n
  maxRank_iff :
    ∀ G,
      SourceOrientedMaxRankAt d n (toHomeomorph G) ↔
        SourceOrientedMaxRankAt d n G

namespace SourceOrientedInvariantTransportEquiv

variable {d n : ℕ}

/-- Forward coordinate transport. -/
def toFun (T : SourceOrientedInvariantTransportEquiv d n) :
    SourceOrientedGramData d n → SourceOrientedGramData d n :=
  T.toHomeomorph

/-- Inverse coordinate transport. -/
def invFun (T : SourceOrientedInvariantTransportEquiv d n) :
    SourceOrientedGramData d n → SourceOrientedGramData d n :=
  T.toHomeomorph.symm

/-- The inverse transport is a left inverse to the forward transport. -/
theorem left_inv (T : SourceOrientedInvariantTransportEquiv d n) :
    Function.LeftInverse T.invFun T.toFun := by
  intro G
  exact T.toHomeomorph.left_inv G

/-- The inverse transport is a right inverse to the forward transport. -/
theorem right_inv (T : SourceOrientedInvariantTransportEquiv d n) :
    Function.RightInverse T.invFun T.toFun := by
  intro G
  exact T.toHomeomorph.right_inv G

/-- Forward transport is continuous. -/
theorem continuous_toFun (T : SourceOrientedInvariantTransportEquiv d n) :
    Continuous T.toFun :=
  T.toHomeomorph.continuous

/-- Inverse transport is continuous. -/
theorem continuous_invFun (T : SourceOrientedInvariantTransportEquiv d n) :
    Continuous T.invFun :=
  T.toHomeomorph.symm.continuous

/-- Images under the inverse transport of open sets are open. -/
theorem isOpen_invFun_image
    (T : SourceOrientedInvariantTransportEquiv d n)
    {Ω : Set (SourceOrientedGramData d n)}
    (hΩ : IsOpen Ω) :
    IsOpen (T.invFun '' Ω) := by
  simpa [invFun] using T.toHomeomorph.symm.isOpenMap Ω hΩ

/-- The inverse transport also preserves membership in the oriented source
variety. -/
theorem invFun_mem_variety_iff
    (T : SourceOrientedInvariantTransportEquiv d n)
    (G : SourceOrientedGramData d n) :
    T.invFun G ∈ sourceOrientedGramVariety d n ↔
      G ∈ sourceOrientedGramVariety d n := by
  have h := T.mem_variety_iff (T.invFun G)
  have h' :
      G ∈ sourceOrientedGramVariety d n ↔
        T.invFun G ∈ sourceOrientedGramVariety d n := by
    simpa [toFun, invFun] using h
  exact h'.symm

/-- The inverse transport also preserves the maximal-rank predicate. -/
theorem invFun_maxRank_iff
    (T : SourceOrientedInvariantTransportEquiv d n)
    (G : SourceOrientedGramData d n) :
    SourceOrientedMaxRankAt d n (T.invFun G) ↔
      SourceOrientedMaxRankAt d n G := by
  have h := T.maxRank_iff (T.invFun G)
  have h' :
      SourceOrientedMaxRankAt d n G ↔
        SourceOrientedMaxRankAt d n (T.invFun G) := by
    simpa [toFun, invFun] using h
  exact h'.symm

/-- Identity transport for oriented source invariants. -/
def refl (d n : ℕ) :
    SourceOrientedInvariantTransportEquiv d n where
  toHomeomorph := Homeomorph.refl (SourceOrientedGramData d n)
  mem_variety_iff := by
    intro G
    rfl
  maxRank_iff := by
    intro G
    rfl

end SourceOrientedInvariantTransportEquiv

end BHW
