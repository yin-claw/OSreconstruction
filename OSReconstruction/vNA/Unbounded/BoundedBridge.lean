/- 
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.vNA.Unbounded.Basic

/-!
# Bounded Operators as Unbounded Operators

This file provides the basic bridge from everywhere-defined bounded operators to
the `UnboundedOperator` framework used by the spectral library.

The point is not a wrapper layer: it isolates the exact theorem needed to feed a
bounded self-adjoint contraction into the existing unbounded spectral theorem.
-/

noncomputable section

open scoped InnerProduct ComplexConjugate

universe u

namespace UnboundedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Regard a bounded operator as an unbounded operator with full domain. -/
def ofContinuousLinearMap (A : H →L[ℂ] H) : UnboundedOperator H where
  domain := ⊤
  toFun := fun x => A x
  map_add' := by
    intro x y
    simp
  map_smul' := by
    intro c x
    simp

omit [CompleteSpace H] in
@[simp] theorem ofContinuousLinearMap_apply (A : H →L[ℂ] H)
    (x : (ofContinuousLinearMap A).domain) :
    ofContinuousLinearMap A x = A x := rfl

omit [CompleteSpace H] in
@[simp] theorem ofContinuousLinearMap_domain (A : H →L[ℂ] H) :
    (ofContinuousLinearMap A).domain = ⊤ := rfl

/-- A bounded operator is densely defined when viewed as an unbounded operator. -/
theorem ofContinuousLinearMap_isDenselyDefined (A : H →L[ℂ] H) :
    (ofContinuousLinearMap A).IsDenselyDefined := by
  rw [UnboundedOperator.IsDenselyDefined, Submodule.topologicalClosure_eq_top_iff,
    ofContinuousLinearMap_domain, Submodule.top_orthogonal_eq_bot]

/-- Every vector lies in the adjoint domain of an everywhere-defined bounded
operator. -/
theorem mem_adjointDomain_ofContinuousLinearMap (A : H →L[ℂ] H) (y : H) :
    y ∈ (ofContinuousLinearMap A).adjointDomain := by
  use ‖A.adjoint y‖
  intro x
  have hxy : @inner ℂ H _ ((ofContinuousLinearMap A) x) y =
      @inner ℂ H _ (x : H) (A.adjoint y) := by
    simpa [ofContinuousLinearMap] using
      (ContinuousLinearMap.adjoint_inner_right A (x : H) y).symm
  rw [hxy]
  calc
    ‖@inner ℂ H _ (x : H) (A.adjoint y)‖ ≤ ‖(x : H)‖ * ‖A.adjoint y‖ :=
      norm_inner_le_norm _ _
    _ = ‖A.adjoint y‖ * ‖(x : H)‖ := by ring

@[simp] theorem adjointDomainSubmodule_ofContinuousLinearMap (A : H →L[ℂ] H) :
    (ofContinuousLinearMap A).adjointDomainSubmodule = ⊤ := by
  ext y
  simp [UnboundedOperator.adjointDomainSubmodule, mem_adjointDomain_ofContinuousLinearMap]

/-- The adjoint of `ofContinuousLinearMap A` acts by the bounded adjoint `A†`. -/
@[simp] theorem adjointApply_ofContinuousLinearMap (A : H →L[ℂ] H)
    (y : (ofContinuousLinearMap A).adjointDomainSubmodule) :
    (ofContinuousLinearMap A).adjointApply
        (ofContinuousLinearMap_isDenselyDefined A) y =
      A.adjoint y := by
  apply (ofContinuousLinearMap A).adjoint_unique
      (ofContinuousLinearMap_isDenselyDefined A) (y : H)
      ((ofContinuousLinearMap A).adjointApply
        (ofContinuousLinearMap_isDenselyDefined A) y)
      (A.adjoint y)
  · exact (ofContinuousLinearMap A).adjointApply_spec
      (ofContinuousLinearMap_isDenselyDefined A) y
  · intro x
    simpa [ofContinuousLinearMap] using
      (ContinuousLinearMap.adjoint_inner_right A (x : H) (y : H)).symm

/-- The unbounded adjoint of an everywhere-defined bounded operator is the same
bounded adjoint, viewed again with full domain. -/
@[simp] theorem adjoint_ofContinuousLinearMap (A : H →L[ℂ] H) :
    (ofContinuousLinearMap A).adjoint (ofContinuousLinearMap_isDenselyDefined A) =
      ofContinuousLinearMap A.adjoint := by
  apply UnboundedOperator.eq_of_graph_eq
  ext p
  constructor
  · intro hp
    rcases hp with ⟨y, hy1, hy2⟩
    refine ⟨⟨(y : H), by simp⟩, hy1, ?_⟩
    calc
      ofContinuousLinearMap A.adjoint ⟨(y : H), by simp⟩ = A.adjoint (y : H) := rfl
      _ = (ofContinuousLinearMap A).adjoint
            (ofContinuousLinearMap_isDenselyDefined A) y := by
            symm
            exact adjointApply_ofContinuousLinearMap (A := A) y
      _ = p.2 := hy2
  · intro hp
    rcases hp with ⟨y, hy1, hy2⟩
    let y' : (ofContinuousLinearMap A).adjointDomainSubmodule :=
      ⟨(y : H), mem_adjointDomain_ofContinuousLinearMap A y⟩
    refine ⟨y', hy1, ?_⟩
    calc
      (ofContinuousLinearMap A).adjoint
          (ofContinuousLinearMap_isDenselyDefined A) y' =
        A.adjoint (y : H) := adjointApply_ofContinuousLinearMap (A := A) y'
      _ = ofContinuousLinearMap A.adjoint y := by
        rfl
      _ = p.2 := hy2

/-- A bounded self-adjoint operator is self-adjoint in the unbounded sense after
passing to full domain. -/
theorem isSelfAdjoint_ofContinuousLinearMap (A : H →L[ℂ] H)
    (hA : _root_.IsSelfAdjoint A) :
    (ofContinuousLinearMap A).IsSelfAdjoint (ofContinuousLinearMap_isDenselyDefined A) := by
  rw [UnboundedOperator.IsSelfAdjoint, adjoint_ofContinuousLinearMap]
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hA
  exact congrArg ofContinuousLinearMap hA.symm

/-- Positivity of a bounded operator transfers verbatim to the corresponding
full-domain unbounded operator. -/
theorem isPositive_ofContinuousLinearMap (A : H →L[ℂ] H)
    (hA : ∀ x : H, 0 ≤ (@inner ℂ H _ (A x) x).re) :
    (ofContinuousLinearMap A).IsPositive := by
  intro x
  simpa [ofContinuousLinearMap] using hA (x : H)

end UnboundedOperator
