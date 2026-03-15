import Mathlib

/-!
# Dense Set Criteria For Continuous Linear Maps

Small helper lemmas for extending identities of continuous linear maps from a
dense subset to the whole domain.
-/

noncomputable section

open Topology

theorem ContinuousLinearMap.eq_zero_of_eq_zero_on_dense
    {𝕜 : Type*} [Semiring 𝕜]
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module 𝕜 E]
    {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [T2Space F]
    (T : E →L[𝕜] F) {S : Set E} (hS : Dense S)
    (hT : ∀ x ∈ S, T x = 0) :
    T = 0 := by
  ext x
  simp only [ContinuousLinearMap.zero_apply]
  have hclosed : IsClosed {x : E | T x = 0} :=
    isClosed_eq T.continuous continuous_const
  exact hclosed.closure_subset_iff.mpr (fun y hy => hT y hy) (hS.closure_eq ▸ trivial)

theorem ContinuousLinearMap.eq_of_eq_on_dense
    {𝕜 : Type*} [Semiring 𝕜]
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module 𝕜 E]
    {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [T2Space F]
    (T₁ T₂ : E →L[𝕜] F) {S : Set E} (hS : Dense S)
    (hT : ∀ x ∈ S, T₁ x = T₂ x) :
    T₁ = T₂ := by
  ext x
  have hclosed : IsClosed {x : E | T₁ x = T₂ x} :=
    isClosed_eq T₁.continuous T₂.continuous
  exact hclosed.closure_subset_iff.mpr (fun y hy => hT y hy) (hS.closure_eq ▸ trivial)
