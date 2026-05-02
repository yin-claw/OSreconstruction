import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceCoefficient

/-!
# Source Gram rank predicates

This file contains the scalar-rank predicates used to split the
Hall-Wightman same-source-Gram analysis.  These predicates live on scalar Gram
matrices; they are not local regularity predicates for the Gram map.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial
open scoped Matrix.Norms.Operator

namespace BHW

/-- Rank of a source Gram matrix in Hall-Wightman's scalar-product
coordinates. -/
def sourceGramMatrixRank
    (n : ℕ)
    (Z : Fin n → Fin n → ℂ) : ℕ :=
  Matrix.rank Z

/-- Rank of the scalar Gram matrix attached to a source configuration. -/
def sourceConfigGramMatrixRank
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) : ℕ :=
  sourceGramMatrixRank n (sourceMinkowskiGram d n z)

/-- Hall-Wightman's orbit-rank branch for Lemma 2. -/
def HWSourceGramOrbitRank
    (d n : ℕ)
    (Z : Fin n → Fin n → ℂ) : Prop :=
  min d n ≤ sourceGramMatrixRank n Z

/-- Hall-Wightman's low-rank branch for Lemma 2. -/
def HWSourceGramLowRank
    (d n : ℕ)
    (Z : Fin n → Fin n → ℂ) : Prop :=
  sourceGramMatrixRank n Z < min d n

/-- Orbit-rank branch at a source configuration. -/
def HWSourceGramOrbitRankAt
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) : Prop :=
  HWSourceGramOrbitRank d n (sourceMinkowskiGram d n z)

/-- Low-rank branch at a source configuration. -/
def HWSourceGramLowRankAt
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) : Prop :=
  HWSourceGramLowRank d n (sourceMinkowskiGram d n z)

/-- Maximal scalar rank for the local source-variety chart branch.  This is
the maximal possible rank in spacetime dimension `d + 1`, not the Lemma-2
orbit threshold. -/
def HWSourceGramMaxRank
    (d n : ℕ)
    (Z : Fin n → Fin n → ℂ) : Prop :=
  min (d + 1) n ≤ sourceGramMatrixRank n Z

/-- Exceptional scalar rank for the local source-variety chart branch. -/
def HWSourceGramExceptionalRank
    (d n : ℕ)
    (Z : Fin n → Fin n → ℂ) : Prop :=
  sourceGramMatrixRank n Z < min (d + 1) n

/-- Maximal scalar rank at a source configuration. -/
def HWSourceGramMaxRankAt
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) : Prop :=
  HWSourceGramMaxRank d n (sourceMinkowskiGram d n z)

/-- Exceptional scalar rank at a source configuration. -/
def HWSourceGramExceptionalRankAt
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) : Prop :=
  HWSourceGramExceptionalRank d n (sourceMinkowskiGram d n z)

/-- The left-adjoint map of the complex Minkowski form restricted to a source
subspace. -/
def restrictedMinkowskiLeftMap
    (d : ℕ)
    (M : Submodule ℂ (Fin (d + 1) → ℂ)) :
    M →ₗ[ℂ] (M →ₗ[ℂ] ℂ) where
  toFun x :=
    { toFun := fun y =>
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (y : Fin (d + 1) → ℂ)
      map_add' := by
        intro y z
        exact sourceComplexMinkowskiInner_add_right
          d (x : Fin (d + 1) → ℂ)
          (y : Fin (d + 1) → ℂ)
          (z : Fin (d + 1) → ℂ)
      map_smul' := by
        intro c y
        exact sourceComplexMinkowskiInner_smul_right
          d c (x : Fin (d + 1) → ℂ)
          (y : Fin (d + 1) → ℂ) }
  map_add' := by
    intro x y
    ext z
    exact sourceComplexMinkowskiInner_add_left
      d (x : Fin (d + 1) → ℂ)
      (y : Fin (d + 1) → ℂ)
      (z : Fin (d + 1) → ℂ)
  map_smul' := by
    intro c x
    ext y
    exact sourceComplexMinkowskiInner_smul_left
      d c (x : Fin (d + 1) → ℂ)
      (y : Fin (d + 1) → ℂ)

/-- Radical of the complex Minkowski form restricted to a source subspace. -/
def restrictedMinkowskiRadical
    (d : ℕ)
    (M : Submodule ℂ (Fin (d + 1) → ℂ)) :
    Submodule ℂ M :=
  LinearMap.ker (restrictedMinkowskiLeftMap d M)

/-- Rank of the complex Minkowski form restricted to a source subspace. -/
def restrictedMinkowskiRank
    (d : ℕ)
    (M : Submodule ℂ (Fin (d + 1) → ℂ)) : ℕ :=
  Module.finrank ℂ M - Module.finrank ℂ (restrictedMinkowskiRadical d M)

/-- A coefficient-evaluated source vector lies in the restricted radical
exactly when it pairs to zero with every coefficient-evaluated source vector. -/
theorem sourceCoefficientEval_mem_restrictedMinkowskiRadical_iff
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (a : Fin n → ℂ) :
    let evalZ := sourceCoefficientEval d n z
    let M := LinearMap.range evalZ
    (⟨evalZ a, ⟨a, rfl⟩⟩ : M) ∈
        restrictedMinkowskiRadical d M ↔
      ∀ b : Fin n → ℂ,
        sourceComplexMinkowskiInner d (evalZ a) (evalZ b) = 0 := by
  intro evalZ M
  rw [restrictedMinkowskiRadical, LinearMap.mem_ker]
  constructor
  · intro h b
    have hlin :
        restrictedMinkowskiLeftMap d M
          (⟨evalZ a, ⟨a, rfl⟩⟩ : M) = 0 := h
    have happ :=
      congrArg
        (fun L : M →ₗ[ℂ] ℂ => L (⟨evalZ b, ⟨b, rfl⟩⟩ : M))
        hlin
    simpa [restrictedMinkowskiLeftMap] using happ
  · intro h
    ext y
    rcases y with ⟨yv, b, rfl⟩
    simpa [restrictedMinkowskiLeftMap] using h b

/-- The scalar Gram kernel is the preimage of the restricted Minkowski
radical under coefficient evaluation. -/
theorem sourceCoefficientGramKernel_eq_eval_preimage_radical
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceCoefficientGramKernel n (sourceMinkowskiGram d n z) =
      ((restrictedMinkowskiRadical d
          (LinearMap.range (sourceCoefficientEval d n z))).map
        (Submodule.subtype
          (LinearMap.range (sourceCoefficientEval d n z)))).comap
        (sourceCoefficientEval d n z) := by
  let evalZ := sourceCoefficientEval d n z
  let M := LinearMap.range evalZ
  let rad := restrictedMinkowskiRadical d M
  ext a
  have hmap :
      evalZ a ∈ rad.map (Submodule.subtype M) ↔
        (⟨evalZ a, ⟨a, rfl⟩⟩ : M) ∈ rad := by
    constructor
    · rintro ⟨x, hx, hxval⟩
      have hx_eq : x = (⟨evalZ a, ⟨a, rfl⟩⟩ : M) :=
        Subtype.ext hxval
      simpa [hx_eq] using hx
    · intro hx
      exact ⟨(⟨evalZ a, ⟨a, rfl⟩⟩ : M), hx, rfl⟩
  change
    a ∈ LinearMap.ker
        (sourceCoefficientGramMap n (sourceMinkowskiGram d n z)) ↔
      evalZ a ∈ rad.map (Submodule.subtype M)
  rw [LinearMap.mem_ker, hmap,
    sourceCoefficientGramMap_eq_zero_iff_eval_pair_eval_eq_zero]
  simpa [evalZ, M, rad] using
    (sourceCoefficientEval_mem_restrictedMinkowskiRadical_iff d n z a).symm

/-- The scalar Gram matrix rank is the finrank of the range of the associated
coefficient Gram map. -/
theorem sourceGramMatrixRank_eq_finrank_range_sourceCoefficientGramMap
    (n : ℕ)
    (G : Fin n → Fin n → ℂ) :
    sourceGramMatrixRank n G =
      Module.finrank ℂ (LinearMap.range (sourceCoefficientGramMap n G)) := by
  rw [sourceGramMatrixRank]
  rw [← Matrix.rank_transpose G]
  rw [Matrix.rank_eq_finrank_range_toLin (Gᵀ)
    (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n))]
  rw [Matrix.toLin_eq_toLin']
  rw [← sourceCoefficientGramMap_eq_toLin_transpose]

/-- The low-rank branch is exactly the complement of the orbit-rank branch. -/
theorem hwSourceGram_lowRank_iff_not_orbitRank
    (d n : ℕ)
    {Z : Fin n → Fin n → ℂ} :
    HWSourceGramLowRank d n Z ↔
      ¬ HWSourceGramOrbitRank d n Z := by
  constructor
  · intro hlow horbit
    exact (not_lt_of_ge horbit) hlow
  · intro hnot
    exact Nat.lt_of_not_ge hnot

/-- The exceptional-rank branch is exactly the complement of the maximal-rank
branch. -/
theorem hwSourceGram_exceptionalRank_iff_not_maxRank
    (d n : ℕ)
    {Z : Fin n → Fin n → ℂ} :
    HWSourceGramExceptionalRank d n Z ↔
      ¬ HWSourceGramMaxRank d n Z := by
  constructor
  · intro hex hmax
    exact (not_lt_of_ge hmax) hex
  · intro hnot
    exact Nat.lt_of_not_ge hnot

/-- The orbit-rank predicate is transported by equality of source Gram
matrices. -/
theorem hwSourceGramOrbitRankAt_of_sourceGram_eq
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w) :
    HWSourceGramOrbitRankAt d n z ↔
      HWSourceGramOrbitRankAt d n w := by
  simp [HWSourceGramOrbitRankAt, HWSourceGramOrbitRank, hgram]

/-- The low-rank predicate is transported by equality of source Gram
matrices. -/
theorem hwSourceGramLowRankAt_of_sourceGram_eq
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w) :
    HWSourceGramLowRankAt d n z ↔
      HWSourceGramLowRankAt d n w := by
  simp [HWSourceGramLowRankAt, HWSourceGramLowRank, hgram]

/-- The maximal-rank predicate is transported by equality of source Gram
matrices. -/
theorem hwSourceGramMaxRankAt_of_sourceGram_eq
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w) :
    HWSourceGramMaxRankAt d n z ↔
      HWSourceGramMaxRankAt d n w := by
  simp [HWSourceGramMaxRankAt, HWSourceGramMaxRank, hgram]

/-- The exceptional-rank predicate is transported by equality of source Gram
matrices. -/
theorem hwSourceGramExceptionalRankAt_of_sourceGram_eq
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w) :
    HWSourceGramExceptionalRankAt d n z ↔
      HWSourceGramExceptionalRankAt d n w := by
  simp [HWSourceGramExceptionalRankAt, HWSourceGramExceptionalRank, hgram]

end BHW
