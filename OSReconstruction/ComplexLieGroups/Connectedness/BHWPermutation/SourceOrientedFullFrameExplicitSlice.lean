import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameOrbit

/-!
# Explicit full-frame gauge slice

This file packages the constructive right inverse used in the full-frame
oriented differential surjectivity proof as a named linear map.  Its range is a
concrete complement to the infinitesimal special-Lorentz orbit tangent, giving
an explicit gauge-slice packet for the real-compatible chart route.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- The explicit right inverse to the full-frame oriented differential on the
oriented hypersurface tangent space. -/
noncomputable def sourceFullFrameOrientedDifferentialRightInverseLinear
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (_hM0 : IsUnit M0.det) :
    sourceFullFrameOrientedTangentSpace d (sourceFullFrameOrientedGram d M0) →ₗ[ℂ]
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ where
  toFun := fun Y =>
    let G : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      Matrix.of (Y : SourceFullFrameOrientedCoord d).1
    let B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      (2 : ℂ)⁻¹ • (M0⁻¹ * G * (M0.transpose)⁻¹ *
        ComplexLorentzGroup.ηℂ (d := d))
    M0 * B
  map_add' := by
    intro Y Z
    let A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      Matrix.of (Y : SourceFullFrameOrientedCoord d).1
    let B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      Matrix.of (Z : SourceFullFrameOrientedCoord d).1
    let C : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      (M0.transpose)⁻¹
    let E : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      ComplexLorentzGroup.ηℂ (d := d)
    have hOf :
        Matrix.of
            ((Y : SourceFullFrameOrientedCoord d).1 +
              (Z : SourceFullFrameOrientedCoord d).1) = A + B := by
      exact
        (Matrix.of_add_of
          (Y : SourceFullFrameOrientedCoord d).1
          (Z : SourceFullFrameOrientedCoord d).1).symm
    have hlin :
        M0⁻¹ * (A + B) * C * E =
          M0⁻¹ * A * C * E + M0⁻¹ * B * C * E := by
      noncomm_ring
    change
      M0 * ((2 : ℂ)⁻¹ •
        (M0⁻¹ *
          Matrix.of
            ((Y + Z :
              sourceFullFrameOrientedTangentSpace d
                (sourceFullFrameOrientedGram d M0)) :
                SourceFullFrameOrientedCoord d).1 *
          (M0.transpose)⁻¹ * ComplexLorentzGroup.ηℂ (d := d))) =
        M0 * ((2 : ℂ)⁻¹ •
          (M0⁻¹ * Matrix.of (Y : SourceFullFrameOrientedCoord d).1 *
            (M0.transpose)⁻¹ * ComplexLorentzGroup.ηℂ (d := d))) +
        M0 * ((2 : ℂ)⁻¹ •
          (M0⁻¹ * Matrix.of (Z : SourceFullFrameOrientedCoord d).1 *
            (M0.transpose)⁻¹ * ComplexLorentzGroup.ηℂ (d := d)))
    simp only [Submodule.coe_add, Prod.fst_add]
    dsimp [A, B, C, E] at hOf hlin
    rw [hOf, hlin, smul_add, Matrix.mul_add]
  map_smul' := by
    intro c Y
    let A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      Matrix.of (Y : SourceFullFrameOrientedCoord d).1
    let C : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      (M0.transpose)⁻¹
    let E : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      ComplexLorentzGroup.ηℂ (d := d)
    have hOf :
        Matrix.of (c • (Y : SourceFullFrameOrientedCoord d).1) =
          c • A := by
      exact (Matrix.smul_of c (Y : SourceFullFrameOrientedCoord d).1).symm
    have hlin :
        M0⁻¹ * (c • A) * C * E =
          c • (M0⁻¹ * A * C * E) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul]
    change
      M0 * ((2 : ℂ)⁻¹ •
        (M0⁻¹ *
          Matrix.of
            ((c • Y :
              sourceFullFrameOrientedTangentSpace d
                (sourceFullFrameOrientedGram d M0)) :
                SourceFullFrameOrientedCoord d).1 *
          (M0.transpose)⁻¹ * ComplexLorentzGroup.ηℂ (d := d))) =
        c •
          (M0 * ((2 : ℂ)⁻¹ •
            (M0⁻¹ * Matrix.of (Y : SourceFullFrameOrientedCoord d).1 *
              (M0.transpose)⁻¹ * ComplexLorentzGroup.ηℂ (d := d))))
    simp only [Submodule.coe_smul, Prod.smul_fst]
    dsimp [A, C, E] at hOf hlin
    rw [hOf, hlin]
    rw [smul_smul, Matrix.mul_smul, Matrix.mul_smul, smul_smul]
    rw [mul_comm c]

@[simp]
theorem sourceFullFrameOrientedDifferentialRightInverseLinear_apply
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (Y : sourceFullFrameOrientedTangentSpace d
      (sourceFullFrameOrientedGram d M0)) :
    sourceFullFrameOrientedDifferentialRightInverseLinear d hM0 Y =
      let G : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
        Matrix.of (Y : SourceFullFrameOrientedCoord d).1
      let B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
        (2 : ℂ)⁻¹ • (M0⁻¹ * G * (M0.transpose)⁻¹ *
          ComplexLorentzGroup.ηℂ (d := d))
      M0 * B :=
  rfl

/-- The constructed linear map is a right inverse to the full-frame oriented
differential. -/
theorem sourceFullFrameOrientedDifferential_rightInverse
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (Y : sourceFullFrameOrientedTangentSpace d
      (sourceFullFrameOrientedGram d M0)) :
    sourceFullFrameOrientedDifferential d M0
        (sourceFullFrameOrientedDifferentialRightInverseLinear d hM0 Y) =
      (Y : SourceFullFrameOrientedCoord d) := by
  let G : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    Matrix.of (Y : SourceFullFrameOrientedCoord d).1
  let B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    (2 : ℂ)⁻¹ • (M0⁻¹ * G * (M0.transpose)⁻¹ *
      ComplexLorentzGroup.ηℂ (d := d))
  change sourceFullFrameOrientedDifferential d M0 (M0 * B) =
    (Y : SourceFullFrameOrientedCoord d)
  have hgram :
      Matrix.of
          (sourceFullFrameOrientedDifferential d M0 (M0 * B)).1 = G :=
    sourceFullFrameOrientedDifferential_constructedGram
      (d := d) hM0 (Y := (Y : SourceFullFrameOrientedCoord d)) Y.property.1
  have hdet :
      (sourceFullFrameOrientedDifferential d M0 (M0 * B)).2 =
        (Y : SourceFullFrameOrientedCoord d).2 :=
    sourceFullFrameOrientedDifferential_constructedDet
      (d := d) hM0 (Y := (Y : SourceFullFrameOrientedCoord d)) Y.property hgram
  apply Prod.ext
  · ext a b
    exact
      congrArg
        (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ => M a b) hgram
  · exact hdet

/-- The explicit gauge slice is the range of the constructive differential
right inverse. -/
noncomputable def sourceFullFrameOrientedDifferentialRightInverseRange
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det) :
    Submodule ℂ (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
  LinearMap.range (sourceFullFrameOrientedDifferentialRightInverseLinear d hM0)

/-- The explicit right-inverse range is complementary to the full-frame
special-Lorentz orbit tangent. -/
theorem sourceFullFrameOrientedDifferentialRightInverseRange_isCompl
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det) :
    IsCompl
      (sourceFullFrameOrientedDifferentialRightInverseRange d hM0)
      (sourceFullFrameOrbitTangent d M0) := by
  let T := sourceFullFrameOrientedTangentSpace d (sourceFullFrameOrientedGram d M0)
  let R : T →ₗ[ℂ] Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    sourceFullFrameOrientedDifferentialRightInverseLinear d hM0
  let S : Submodule ℂ (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
    LinearMap.range R
  let K : Submodule ℂ (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
    sourceFullFrameOrbitTangent d M0
  have hker :
      LinearMap.ker (sourceFullFrameOrientedDifferentialCLM d M0).toLinearMap =
        K := by
    dsimp [K]
    exact sourceFullFrameOrientedDifferential_kernel_eq_orbitTangent
      (d := d) hM0
  have hdisjoint : Disjoint S K := by
    rw [Submodule.disjoint_def]
    intro X hXS hXK
    rcases hXS with ⟨Y, rfl⟩
    have hkerX :
        R Y ∈
          LinearMap.ker
            (sourceFullFrameOrientedDifferentialCLM d M0).toLinearMap := by
      rw [hker]
      exact hXK
    have hzeroDiff : sourceFullFrameOrientedDifferential d M0 (R Y) = 0 := by
      simpa [sourceFullFrameOrientedDifferentialCLM,
        sourceFullFrameOrientedDifferentialLinear] using
        (LinearMap.mem_ker.mp hkerX)
    have hYzero : (Y : SourceFullFrameOrientedCoord d) = 0 := by
      have hright :=
        sourceFullFrameOrientedDifferential_rightInverse d hM0 Y
      rw [hright] at hzeroDiff
      exact hzeroDiff
    have hY0 : Y = 0 := Subtype.ext hYzero
    simp [hY0, R]
  have hcodisjoint : Codisjoint S K := by
    rw [codisjoint_iff_le_sup]
    intro X _hX
    let L :=
      (sourceFullFrameOrientedDifferentialCLM d M0).toLinearMap
    let Y : T :=
      ⟨L X, by
        change sourceFullFrameOrientedDifferential d M0 X ∈
          sourceFullFrameOrientedTangentSpace d
            (sourceFullFrameOrientedGram d M0)
        exact
          (sourceFullFrameOrientedDifferential_range_subset_tangent
            (d := d) hM0) ⟨X, rfl⟩⟩
    have hSY : R Y ∈ S := ⟨Y, rfl⟩
    have hKY : X - R Y ∈ K := by
      rw [← hker, LinearMap.mem_ker]
      have hRY : L (R Y) = L X := by
        have hright :=
          sourceFullFrameOrientedDifferential_rightInverse d hM0 Y
        change sourceFullFrameOrientedDifferential d M0 (R Y) =
          sourceFullFrameOrientedDifferential d M0 X
        rw [hright]
        rfl
      calc
        L (X - R Y) = L X - L (R Y) := by simp
        _ = 0 := by rw [hRY, sub_self]
    exact Submodule.mem_sup.mpr ⟨R Y, hSY, X - R Y, hKY, by abel⟩
  change IsCompl S K
  exact IsCompl.mk hdisjoint hcodisjoint

/-- A full-frame gauge-slice packet using the explicit right-inverse range,
instead of an arbitrary complement. -/
noncomputable def sourceFullFrameExplicitGaugeSliceData
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det) :
    SourceFullFrameGaugeSliceData d M0 := by
  let T := sourceFullFrameOrientedTangentSpace d (sourceFullFrameOrientedGram d M0)
  let R : T →ₗ[ℂ] Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    sourceFullFrameOrientedDifferentialRightInverseLinear d hM0
  let S : Submodule ℂ (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
    LinearMap.range R
  let K : Submodule ℂ (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
    sourceFullFrameOrbitTangent d M0
  let L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ →ₗ[ℂ]
      SourceFullFrameOrientedCoord d :=
    (sourceFullFrameOrientedDifferentialCLM d M0).toLinearMap
  have hCompl : IsCompl S K := by
    exact sourceFullFrameOrientedDifferentialRightInverseRange_isCompl
      (d := d) hM0
  have hker : LinearMap.ker L = K := by
    dsimp [L, K]
    exact sourceFullFrameOrientedDifferential_kernel_eq_orbitTangent
      (d := d) hM0
  let LS : S →ₗ[ℂ] T :=
    { toFun := fun X =>
        ⟨L (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ), by
          change sourceFullFrameOrientedDifferential d M0
              (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) ∈
            sourceFullFrameOrientedTangentSpace d
              (sourceFullFrameOrientedGram d M0)
          exact
            (sourceFullFrameOrientedDifferential_range_subset_tangent
              (d := d) hM0)
              ⟨(X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ), rfl⟩⟩
      map_add' := by
        intro X Y
        apply Subtype.ext
        simp [L]
      map_smul' := by
        intro c X
        apply Subtype.ext
        simp [L] }
  have hLS_inj : Function.Injective LS := by
    intro X Y hXY
    apply Subtype.ext
    have hval :
        L (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) =
          L (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
      exact congrArg Subtype.val hXY
    have hdiffK :
        (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) -
            (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) ∈ K := by
      rw [← hker, LinearMap.mem_ker]
      rw [map_sub, hval, sub_self]
    have hdiffS :
        (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) -
            (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) ∈ S :=
      S.sub_mem X.property Y.property
    have hzero :
        (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) -
            (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) = 0 :=
      submodule_mem_isCompl_inter_eq_zero hCompl hdiffS hdiffK
    exact sub_eq_zero.mp hzero
  have hLS_surj : Function.Surjective LS := by
    intro Y
    refine ⟨⟨R Y, ⟨Y, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change L (R Y) = (Y : SourceFullFrameOrientedCoord d)
    have hright := sourceFullFrameOrientedDifferential_rightInverse d hM0 Y
    change sourceFullFrameOrientedDifferential d M0 (R Y) =
      (Y : SourceFullFrameOrientedCoord d) at hright
    exact hright
  let e : S ≃ₗ[ℂ] T := LinearEquiv.ofBijective LS ⟨hLS_inj, hLS_surj⟩
  refine
    { slice := S
      isCompl := hCompl
      differential_iso := e
      differential_iso_eq := ?_ }
  intro X
  rfl

end BHW
