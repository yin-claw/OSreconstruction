/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwingerAxioms
import OSReconstruction.ComplexLieGroups.DifferenceCoordinatesSCV

/-!
# OS to Wightman (E'→R')

Analytic continuation from Euclidean to Minkowski: given Schwinger functions
satisfying E0'-E4 (with the linear growth condition), reconstruct Wightman
functions satisfying R0-R5.

The critical point is that the Euclidean input is honest Schwinger data on the
zero-diagonal test space `°S`, while the Wightman output is a full tempered
distribution family on Schwartz space. That jump is the heart of OS
reconstruction; it must not be smuggled into the Euclidean hypothesis by
quietly assuming a full-Schwartz Schwinger theory from the start.

The proof proceeds through phases:
- Phase 2: Euclidean time translation semigroup
- Phase 3: Inductive analytic continuation (OS II, Theorem 4.1-4.2)
- Phase 4: Boundary values → tempered distributions
- Phase 5: Property transfer (OS axioms → Wightman axioms)
-/

open scoped Classical
open BigOperators Finset

noncomputable section

variable {d : ℕ} [NeZero d]
/-! ### OS to Wightman (Theorem E'→R') -/

/-- Phase 2: The Euclidean time translation semigroup.

    For t > 0, define the operator T(t) on the Hilbert space by:
      T(t) [f](τ₁,...,τₙ) = [f(τ₁ + t,..., τₙ + t)]

    This gives a contraction semigroup with:
    - T(s)T(t) = T(s+t)
    - ‖T(t)‖ ≤ 1 (contraction, from E2)
    - T(t) → I as t → 0⁺ (strong continuity, from E0)

    By the Hille-Yosida theorem, T(t) = e^{-tH} where H ≥ 0 is self-adjoint.
    This H is the Hamiltonian of the reconstructed QFT. -/
structure EuclideanSemigroup (OS : OsterwalderSchraderAxioms d) where
  /-- The semigroup parameter (Euclidean time) -/
  T : ℝ → (BorchersSequence d → BorchersSequence d)
  /-- Semigroup property: T(s) ∘ T(t) = T(s+t) -/
  semigroup : ∀ s t : ℝ, s > 0 → t > 0 → T s ∘ T t = T (s + t)
  /-- Contraction: ‖T(t)F‖ ≤ ‖F‖ -/
  contraction : ∀ t : ℝ, t > 0 → ∀ F : BorchersSequence d,
    (OSInnerProduct d OS.S (T t F) (T t F)).re ≤
    (OSInnerProduct d OS.S F F).re
  /-- Positivity: T(t) ≥ 0 as an operator -/
  positive : ∀ t : ℝ, t > 0 → ∀ F : BorchersSequence d,
    (OSInnerProduct d OS.S F (T t F)).re ≥ 0

abbrev timeShiftVec (d : ℕ) (t : ℝ) : SpacetimeDim d :=
  fun μ => if μ = 0 then t else 0

abbrev translateNPointDomain (a : SpacetimeDim d) {n : ℕ} :
    NPointDomain d n → NPointDomain d n :=
  fun x i => x i - a

omit [NeZero d] in
private theorem continuous_translateNPointDomain (a : SpacetimeDim d) {n : ℕ} :
    Continuous (translateNPointDomain (d := d) (n := n) a) := by
  apply continuous_pi
  intro i
  exact (continuous_apply i).sub continuous_const

omit [NeZero d] in
private theorem tsupport_precomp_subset {X Y α : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Zero α]
    {f : Y → α} {h : X → Y} (hh : Continuous h) :
    tsupport (fun x => f (h x)) ⊆ h ⁻¹' tsupport f := by
  refine closure_minimal ?_ ((isClosed_tsupport _).preimage hh)
  intro x hx
  exact subset_closure (by simpa [Function.mem_support] using hx)

omit [NeZero d] in
private theorem translateNPointDomain_antilipschitz (a : SpacetimeDim d) {n : ℕ} :
    AntilipschitzWith 1 (translateNPointDomain (d := d) (n := n) a) := by
  refine AntilipschitzWith.of_le_mul_dist ?_
  intro x y
  have hsub :
      x - y = translateNPointDomain (d := d) (n := n) a x -
        translateNPointDomain (d := d) (n := n) a y := by
    ext i μ
    simp [translateNPointDomain, sub_eq_add_neg]
    abel_nf
  simpa [one_mul, dist_eq_norm] using le_of_eq (congrArg norm hsub)

omit [NeZero d] in
private theorem translateNPointDomain_hasTemperateGrowth (a : SpacetimeDim d) {n : ℕ} :
    Function.HasTemperateGrowth (translateNPointDomain (d := d) (n := n) a) := by
  let c : NPointDomain d n := fun _ => -a
  have hconst : Function.HasTemperateGrowth (fun _ : NPointDomain d n => c) :=
    Function.HasTemperateGrowth.const c
  have hid : Function.HasTemperateGrowth (fun x : NPointDomain d n => x) := by
    simpa using (ContinuousLinearMap.id ℝ (NPointDomain d n)).hasTemperateGrowth
  simpa [translateNPointDomain, c, sub_eq_add_neg, Pi.add_apply] using hid.add hconst

abbrev translateSchwartzNPoint (a : SpacetimeDim d) {n : ℕ} :
    SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (translateNPointDomain_hasTemperateGrowth (d := d) (n := n) a)
    (translateNPointDomain_antilipschitz (d := d) (n := n) a)

omit [NeZero d] in
@[simp] theorem translateSchwartzNPoint_apply (a : SpacetimeDim d) {n : ℕ}
    (f : SchwartzNPoint d n) (x : NPointDomain d n) :
    translateSchwartzNPoint (d := d) a f x = f (fun i => x i - a) := by
  simp [translateSchwartzNPoint]

abbrev timeShiftSchwartzNPoint (t : ℝ) {n : ℕ} :
    SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
  translateSchwartzNPoint (d := d) (timeShiftVec d t)

omit [NeZero d] in
@[simp] theorem timeShiftSchwartzNPoint_apply (t : ℝ) {n : ℕ}
    (f : SchwartzNPoint d n) (x : NPointDomain d n) :
    timeShiftSchwartzNPoint (d := d) t f x =
      f (fun i => x i - timeShiftVec d t) := by
  simp [timeShiftSchwartzNPoint, translateSchwartzNPoint_apply]

abbrev timeShiftBorchers (t : ℝ) : BorchersSequence d → BorchersSequence d :=
  fun F =>
    { funcs := fun n => timeShiftSchwartzNPoint (d := d) t (F.funcs n)
      bound := F.bound
      bound_spec := by
        intro n hn
        simp [F.bound_spec n hn] }

omit [NeZero d] in
@[simp] theorem timeShiftBorchers_funcs (t : ℝ) (F : BorchersSequence d) (n : ℕ) :
    (timeShiftBorchers (d := d) t F).funcs n = timeShiftSchwartzNPoint (d := d) t (F.funcs n) :=
  rfl

omit [NeZero d] in
private theorem timeShift_preserves_ordered_positive_tsupport (t : ℝ) (ht : 0 < t)
    (F : BorchersSequence d)
    (hF : ∀ n, tsupport ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    ∀ n,
      tsupport ((((timeShiftBorchers (d := d) t F).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ)) ⊆ OrderedPositiveTimeRegion d n := by
  intro n x hx
  have hxpre :
      (fun i => x i - timeShiftVec d t) ∈
        tsupport ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
    exact tsupport_precomp_subset
      (f := ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ))
      (h := translateNPointDomain (d := d) (n := n) (timeShiftVec d t))
      (continuous_translateNPointDomain (d := d) (n := n) (timeShiftVec d t)) hx
  have hord := hF n hxpre
  intro i
  constructor
  · have hi := (hord i).1
    have htime : timeShiftVec d t 0 = t := by simp [timeShiftVec]
    have : x i 0 - t > 0 := by
      simpa [OrderedPositiveTimeRegion, htime] using hi
    linarith
  · intro j hij
    have hij' := (hord i).2 j hij
    have htime : timeShiftVec d t 0 = t := by simp [timeShiftVec]
    have : x i 0 - t < x j 0 - t := by
      simpa [OrderedPositiveTimeRegion, htime] using hij'
    linarith

omit [NeZero d] in
private theorem timeReflection_add_timeShiftVec (x : SpacetimeDim d) (t : ℝ) :
    timeReflection d (x + timeShiftVec d t) = timeReflection d x - timeShiftVec d t := by
  funext μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [timeReflection, timeShiftVec]
    ring
  · simp [timeReflection, timeShiftVec, hμ]

private theorem shift_osConjTensorProduct_eq {n m : ℕ}
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (s t : ℝ)
    (x : NPointDomain d (n + m)) :
    ((timeShiftSchwartzNPoint (d := d) t f).osConjTensorProduct
      (timeShiftSchwartzNPoint (d := d) s g)) x =
    (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) (t + s) g))
      (fun i => x i + timeShiftVec d t) := by
  simp only [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply,
    SchwartzNPoint.osConj_apply, timeShiftSchwartzNPoint_apply]
  congr
  · ext i μ
    symm
    simpa [timeReflectionN, splitFirst, sub_eq_add_neg] using
      congrArg (fun y : SpacetimeDim d => y μ)
        (timeReflection_add_timeShiftVec (d := d) (x := splitFirst n m x i) t)
  · ext i μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [splitLast, timeShiftVec, sub_eq_add_neg]
      ring
    · simp [splitLast, timeShiftVec, hμ, sub_eq_add_neg]

private theorem schwinger_shift_tensor_eq (OS : OsterwalderSchraderAxioms d)
    {n m : ℕ} (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) (s t : ℝ)
    (hleft : VanishesToInfiniteOrderOnCoincidence
      ((timeShiftSchwartzNPoint (d := d) t f).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) s g)))
    (hright : VanishesToInfiniteOrderOnCoincidence
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) (t + s) g))) :
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
      ((timeShiftSchwartzNPoint (d := d) t f).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) s g))) =
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) (t + s) g))) := by
  symm
  refine OS.E1_translation_invariant (n + m) (timeShiftVec d t)
    (ZeroDiagonalSchwartz.ofClassical
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) (t + s) g)))
    (ZeroDiagonalSchwartz.ofClassical
      ((timeShiftSchwartzNPoint (d := d) t f).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) s g))) ?_
  intro x
  rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (f := (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) (t + s) g))) hright,
    ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (f := ((timeShiftSchwartzNPoint (d := d) t f).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) s g))) hleft]
  exact shift_osConjTensorProduct_eq (d := d) f g s t x

private theorem OSInnerProduct_timeShift_eq (OS : OsterwalderSchraderAxioms d)
    (F G : BorchersSequence d) (s t : ℝ)
    (hleft : OSTensorAdmissible d (timeShiftBorchers (d := d) t F)
      (timeShiftBorchers (d := d) s G))
    (hright : OSTensorAdmissible d F
      (timeShiftBorchers (d := d) (t + s) G)) :
    OSInnerProduct d OS.S (timeShiftBorchers (d := d) t F) (timeShiftBorchers (d := d) s G) =
    OSInnerProduct d OS.S F (timeShiftBorchers (d := d) (t + s) G) := by
  unfold OSInnerProduct
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  simpa [timeShiftBorchers_funcs] using
    schwinger_shift_tensor_eq (d := d) OS (F.funcs n) (G.funcs m) s t
      (hleft n m) (hright n m)

private theorem OSTensorAdmissible_linearCombo_right {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℂ)
    (F : BorchersSequence d) (G : ι → BorchersSequence d)
    (hFG : ∀ i ∈ s, OSTensorAdmissible d F (G i)) :
    OSTensorAdmissible d F (BorchersSequence.linearCombo s c G) := by
  classical
  revert hFG
  refine Finset.induction_on s ?_ ?_
  · intro hFG
    simpa [BorchersSequence.linearCombo] using (OSTensorAdmissible.zero_right (d := d) F)
  · intro a s ha ih hFG
    intro n m
    rw [BorchersSequence.linearCombo_insert (d := d) ha c G m,
      BorchersSequence.add_funcs, BorchersSequence.smul_funcs,
      SchwartzNPoint.osConjTensorProduct_add_right,
      SchwartzNPoint.osConjTensorProduct_smul_right]
    exact ((hFG a (Finset.mem_insert_self a s) n m).smul (c a)).add
      (ih (fun i hi => hFG i (Finset.mem_insert_of_mem hi)) n m)

/-- The OS inner product distributes over `linearCombo` in the right argument. -/
private theorem OSInnerProduct_linearCombo_right (OS : OsterwalderSchraderAxioms d)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (F : BorchersSequence d) (G : ι → BorchersSequence d)
    (hFG : ∀ i ∈ s, OSTensorAdmissible d F (G i)) :
    OSInnerProduct d OS.S F (BorchersSequence.linearCombo s c G) =
      ∑ i ∈ s, c i • OSInnerProduct d OS.S F (G i) := by
  classical
  revert hFG
  refine Finset.induction_on s ?_ ?_
  · intro hFG
    rw [OSInnerProduct_congr_right (d := d) OS.S OS.E0_linear F
      (BorchersSequence.linearCombo ∅ c G) 0 (fun n => BorchersSequence.linearCombo_empty (d := d) c G n)]
    exact OSInnerProduct_zero_right (d := d) OS.S OS.E0_linear F
  · intro a s ha ih hFG
    rw [OSInnerProduct_congr_right (d := d) OS.S OS.E0_linear F
      (BorchersSequence.linearCombo (insert a s) c G)
      (c a • G a + BorchersSequence.linearCombo s c G)
      (fun n => BorchersSequence.linearCombo_insert (d := d) ha c G n)]
    rw [OSInnerProduct_add_right (d := d) OS.S OS.E0_linear F
      (c a • G a) (BorchersSequence.linearCombo s c G)]
    · rw [OSInnerProduct_smul_right (d := d) OS.S OS.E0_linear (c a) F (G a)]
      rw [ih (fun i hi => hFG i (Finset.mem_insert_of_mem hi))]
      simp [Finset.sum_insert, ha, smul_eq_mul, mul_assoc]
    · exact OSTensorAdmissible.smul_right (d := d)
        (hFG a (Finset.mem_insert_self a s)) (c a)
    · exact OSTensorAdmissible_linearCombo_right (d := d) s c F G
        (fun i hi => hFG i (Finset.mem_insert_of_mem hi))

private theorem OSTensorAdmissible_linearCombo_left {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℂ)
    (F : ι → BorchersSequence d) (G : BorchersSequence d)
    (hFG : ∀ i ∈ s, OSTensorAdmissible d (F i) G) :
    OSTensorAdmissible d (BorchersSequence.linearCombo s c F) G := by
  classical
  revert hFG
  refine Finset.induction_on s ?_ ?_
  · intro hFG
    simpa [BorchersSequence.linearCombo] using (OSTensorAdmissible.zero_left (d := d) G)
  · intro a s ha ih hFG
    intro n m
    rw [BorchersSequence.linearCombo_insert (d := d) ha c F n,
      BorchersSequence.add_funcs, BorchersSequence.smul_funcs,
      SchwartzNPoint.osConjTensorProduct_add_left,
      SchwartzNPoint.osConjTensorProduct_smul_left]
    exact ((hFG a (Finset.mem_insert_self a s) n m).smul (starRingEnd ℂ (c a))).add
      (ih (fun i hi => hFG i (Finset.mem_insert_of_mem hi)) n m)

/-- The OS inner product distributes over `linearCombo` in the left argument. -/
private theorem OSInnerProduct_linearCombo_left (OS : OsterwalderSchraderAxioms d)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (F : ι → BorchersSequence d) (G : BorchersSequence d)
    (hFG : ∀ i ∈ s, OSTensorAdmissible d (F i) G) :
    OSInnerProduct d OS.S (BorchersSequence.linearCombo s c F) G =
      ∑ i ∈ s, starRingEnd ℂ (c i) • OSInnerProduct d OS.S (F i) G := by
  classical
  revert hFG
  refine Finset.induction_on s ?_ ?_
  · intro hFG
    rw [OSInnerProduct_congr_left (d := d) OS.S OS.E0_linear
      (BorchersSequence.linearCombo ∅ c F) 0 G (fun n => BorchersSequence.linearCombo_empty (d := d) c F n)]
    exact OSInnerProduct_zero_left (d := d) OS.S OS.E0_linear G
  · intro a s ha ih hFG
    rw [OSInnerProduct_congr_left (d := d) OS.S OS.E0_linear
      (BorchersSequence.linearCombo (insert a s) c F)
      (c a • F a + BorchersSequence.linearCombo s c F) G
      (fun n => BorchersSequence.linearCombo_insert (d := d) ha c F n)]
    rw [OSInnerProduct_add_left (d := d) OS.S OS.E0_linear
      (c a • F a) (BorchersSequence.linearCombo s c F) G]
    · rw [OSInnerProduct_smul_left (d := d) OS.S OS.E0_linear (c a) (F a) G]
      rw [ih (fun i hi => hFG i (Finset.mem_insert_of_mem hi))]
      simp [Finset.sum_insert, ha, smul_eq_mul, mul_assoc]
    · exact OSTensorAdmissible.smul_left (d := d)
        (hFG a (Finset.mem_insert_self a s)) (c a)
    · exact OSTensorAdmissible_linearCombo_left (d := d) s c F G
        (fun i hi => hFG i (Finset.mem_insert_of_mem hi))

omit [NeZero d] in
private theorem timeShift_linearCombo_preserves_ordered_positive_tsupport {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℂ) (t : ι → ℝ)
    (ht : ∀ i ∈ s, 0 < t i)
    (F : BorchersSequence d)
    (hF : ∀ n, tsupport ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    ∀ n,
      tsupport (((BorchersSequence.linearCombo s c
          (fun i => timeShiftBorchers (d := d) (t i) F)).funcs n : SchwartzNPoint d n) :
            NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n := by
  classical
  revert ht
  refine Finset.induction_on s ?_ ?_
  · intro ht n
    simpa [BorchersSequence.linearCombo] using
      (empty_subset (OrderedPositiveTimeRegion d n) : (∅ : Set (NPointDomain d n)) ⊆ _)
  · intro a s ha ih ht n
    rw [BorchersSequence.linearCombo_insert (d := d) ha c
      (fun i => timeShiftBorchers (d := d) (t i) F) n]
    intro x hx
    have hx' :
        x ∈ tsupport ((((c a • timeShiftBorchers (d := d) (t a) F).funcs n :
          SchwartzNPoint d n) : NPointDomain d n → ℂ)) ∪
          tsupport ((((BorchersSequence.linearCombo s c
            (fun i => timeShiftBorchers (d := d) (t i) F)).funcs n :
              SchwartzNPoint d n) : NPointDomain d n → ℂ)) := by
      have hx'' := (tsupport_add
        ((((c a • timeShiftBorchers (d := d) (t a) F).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ))
        ((((BorchersSequence.linearCombo s c
          (fun i => timeShiftBorchers (d := d) (t i) F)).funcs n : SchwartzNPoint d n) :
            NPointDomain d n → ℂ))) hx
      simpa [BorchersSequence.add_funcs] using hx''
    rcases hx' with hxleft | hxright
    · have hxshift :
          x ∈ tsupport ((((timeShiftBorchers (d := d) (t a) F).funcs n :
            SchwartzNPoint d n) : NPointDomain d n → ℂ)) := by
        exact (tsupport_smul_subset_right
          (fun _ : NPointDomain d n => c a)
          ((((timeShiftBorchers (d := d) (t a) F).funcs n : SchwartzNPoint d n) :
            NPointDomain d n → ℂ)))
          (by simpa [BorchersSequence.smul_funcs] using hxleft)
      exact timeShift_preserves_ordered_positive_tsupport (d := d) (t a)
        (ht a (Finset.mem_insert_self a s)) F hF n hxshift
    · exact ih (fun i hi => ht i (Finset.mem_insert_of_mem hi)) n hxright

/-- Positivity of the Euclidean time-shift kernel on the OS side.

    For any Borchers sequence `F` supported in positive Euclidean times, the
    Hankel kernel `K(s,t) = ⟪F, T_{s+t} F⟫_OS` is positive semidefinite on every
    finite collection of positive times. This is the core positivity input for
    the Laplace/spectral base-step route. -/
theorem OSInnerProduct_timeShift_kernel_nonneg (OS : OsterwalderSchraderAxioms d)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ) (t : ι → ℝ)
    (ht : ∀ i ∈ s, 0 < t i)
    (F : BorchersSequence d)
    (hF : ∀ n, tsupport ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    0 ≤ (∑ i ∈ s, ∑ j ∈ s,
      starRingEnd ℂ (c i) * c j *
        OSInnerProduct d OS.S F (timeShiftBorchers (d := d) (t i + t j) F)).re := by
  let G : ι → BorchersSequence d := fun i => timeShiftBorchers (d := d) (t i) F
  let H : BorchersSequence d := BorchersSequence.linearCombo s c G
  have hGsupport : ∀ i ∈ s, ∀ n,
      tsupport (((G i).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n := by
    intro i hi
    simpa [G] using
      timeShift_preserves_ordered_positive_tsupport (d := d) (t i) (ht i hi) F hF
  have hHsupport : ∀ n,
      tsupport ((H.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n := by
    simpa [H, G] using
      timeShift_linearCombo_preserves_ordered_positive_tsupport
        (d := d) s c t ht F hF
  have hOuterAdm : ∀ i ∈ s, OSTensorAdmissible d (G i) H := by
    intro i hi
    exact OSTensorAdmissible_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (G i) H (hGsupport i hi) hHsupport
  have hPairAdm : ∀ i ∈ s, ∀ j ∈ s, OSTensorAdmissible d (G i) (G j) := by
    intro i hi j hj
    exact OSTensorAdmissible_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (G i) (G j) (hGsupport i hi) (hGsupport j hj)
  have hShiftAdm : ∀ i ∈ s, ∀ j ∈ s,
      OSTensorAdmissible d F (timeShiftBorchers (d := d) (t i + t j) F) := by
    intro i hi j hj
    exact OSTensorAdmissible_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) F (timeShiftBorchers (d := d) (t i + t j) F) hF
      (timeShift_preserves_ordered_positive_tsupport (d := d) (t i + t j)
        (by linarith [ht i hi, ht j hj]) F hF)
  have hpos : 0 ≤ (OSInnerProduct d OS.S H H).re :=
    OS.E2_reflection_positive H hHsupport
  have hExpandLeft :
      OSInnerProduct d OS.S H H =
        ∑ i ∈ s, starRingEnd ℂ (c i) * OSInnerProduct d OS.S (G i) H := by
    simpa [H, G, smul_eq_mul] using
      (OSInnerProduct_linearCombo_left (d := d) (OS := OS) (s := s) (c := c)
        (F := G) (G := H) hOuterAdm)
  have hExpandRight :
      ∀ i ∈ s, OSInnerProduct d OS.S (G i) H =
        ∑ j ∈ s, c j * OSInnerProduct d OS.S (G i) (G j) := by
    intro i hi
    simpa [H, G, smul_eq_mul] using
      (OSInnerProduct_linearCombo_right (d := d) (OS := OS) (s := s) (c := c)
        (F := G i) (G := G) (fun j hj => hPairAdm i hi j hj))
  have hEq :
      OSInnerProduct d OS.S H H =
        ∑ i ∈ s, ∑ j ∈ s,
          starRingEnd ℂ (c i) * c j *
            OSInnerProduct d OS.S F (timeShiftBorchers (d := d) (t i + t j) F) := by
    rw [hExpandLeft]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hExpandRight i hi, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hshiftEq :
        OSInnerProduct d OS.S (G i) (G j) =
          OSInnerProduct d OS.S F (timeShiftBorchers (d := d) (t i + t j) F) := by
      simpa [G] using
        (OSInnerProduct_timeShift_eq (d := d) (OS := OS) (F := F) (G := F)
          (s := t j) (t := t i) (hleft := hPairAdm i hi j hj)
          (hright := hShiftAdm i hi j hj))
    rw [mul_assoc]
    rw [hshiftEq]
  rwa [hEq] at hpos

/- Phase 3: Analytic continuation from Euclidean to Minkowski.

    The analytic continuation proceeds inductively. Starting from Schwinger functions
    S_n defined on Euclidean configurations, we extend to complex times.

    **Inductive structure** (OS II, Theorem 4.1):
    - A₀: S_k(ξ) is analytic on {ξ ∈ ℝ^k : ξⱼ > 0 for all j}
    - Aᵣ: S_k has analytic continuation to the region C_k^(r) ⊂ ℂ^k
      where r of the ξ-variables are complexified
    - After n = d + 1 steps, reach the full forward tube

    **Key estimate** (OS II, Theorem 4.2): At each step, the linear growth
    condition E0' provides the bounds needed for the continuation. -/

/-- The region C_k^(r) from OS II: the domain after r steps of analytic continuation.
    C_k^(0) = {ξ ∈ ℝ^k : Im = 0, ξᵢ₀ > 0} (positive real Euclidean domain)
    C_k^(r+1) = {z ∈ ℂ^{k(d+1)} : Im(z_i,μ - z_{i-1,μ}) > 0 for all i, μ ≤ r}
      (open forward tube in the first r+1 spacetime directions; no constraint on μ > r).

    **Key property**: For r ≥ 1, C_k^(r) is an OPEN subset of ℂ^{k(d+1)}
    (strict positivity of imaginary parts ⟹ open). This ensures `DifferentiableOn ℂ`
    on C_k^(r) is genuine holomorphicity, not a vacuous condition.

    **Note**: C_k^(d+1) is the tube over a positive orthant in difference
    coordinates, not yet the Wightman forward tube. The active reconstruction
    chain in this file no longer uses the old Bochner/orbit route, so we do not
    build further geometry on that path here.

    The regions are monotone in the reverse direction for `r ≥ 1`:
      C_k^(r+1) ⊆ C_k^(r),
    since each step adds one more imaginary-positivity constraint. Also
    `C_k^(0)` is disjoint from `C_k^(r)` for r ≥ 1 (`C_k^(0)` has Im = 0,
    while `C_k^(r)` requires Im > 0 in at least one direction). -/
def AnalyticContinuationRegion (d k r : ℕ) [NeZero d] :
    Set (Fin k → Fin (d + 1) → ℂ) :=
  match r with
  | 0 => -- Base: positive Euclidean domain (all Im = 0, Euclidean times positive)
    { z | (∀ i : Fin k, ∀ μ : Fin (d + 1), (z i μ).im = 0) ∧
          (∀ i : Fin k, (z i 0).re > 0) }
  | r + 1 => -- Open forward tube in first r+1 spacetime directions;
    -- no constraint on remaining directions (μ > r), giving an open set.
    { z | ∀ i : Fin k,
        ∀ μ : Fin (d + 1), μ.val ≤ r →
          let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
          (z i μ - prev μ).im > 0 }

/-- Each individual coordinate positivity condition in the r+1 analytic continuation region
    defines an open set. This is the building block for `isOpen_analyticContinuationRegion_succ`. -/
private theorem isOpen_acr_coord {d k r : ℕ} (i : Fin k) (μ : Fin (d + 1)) :
    IsOpen { z : Fin k → Fin (d + 1) → ℂ |
      μ.val ≤ r →
        let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
        (z i μ - prev μ).im > 0 } := by
  by_cases hμ : μ.val ≤ r
  · by_cases hi : i.val = 0
    · have hcont : Continuous fun z : Fin k → Fin (d + 1) → ℂ => (z i μ).im := by
        simpa using (Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply i)))
      simpa [hμ, hi] using isOpen_lt continuous_const hcont
    · let j : Fin k := ⟨i.val - 1, by omega⟩
      have hi' : Continuous fun z : Fin k → Fin (d + 1) → ℂ => (z i μ).im := by
        simpa using (Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply i)))
      have hj' : Continuous fun z : Fin k → Fin (d + 1) → ℂ => (z j μ).im := by
        simpa [j] using (Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply j)))
      simpa [hμ, hi, j, Complex.sub_im, sub_pos] using isOpen_lt hj' hi'
  · simp [hμ]

/-- For r ≥ 1, the analytic continuation region C_k^(r+1) is open. The strict imaginary-part
    positivity conditions are open conditions, and the region is a finite intersection of them. -/
theorem isOpen_analyticContinuationRegion_succ {d k r : ℕ} [NeZero d] :
    IsOpen (AnalyticContinuationRegion d k (r + 1)) := by
  suffices h :
      AnalyticContinuationRegion d k (r + 1) =
        ⋂ i : Fin k, ⋂ μ : Fin (d + 1),
          { z : Fin k → Fin (d + 1) → ℂ |
            μ.val ≤ r →
              let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
              (z i μ - prev μ).im > 0 } by
    rw [h]
    exact isOpen_iInter_of_finite (fun i : Fin k =>
      isOpen_iInter_of_finite (fun μ : Fin (d + 1) =>
        isOpen_acr_coord (d := d) (k := k) (r := r) i μ))
  ext z
  simp [AnalyticContinuationRegion]

private theorem differentiable_unflattenCfg_local (k d : ℕ) :
    Differentiable ℂ (BHW.unflattenCfg k d :
      (Fin (k * (d + 1)) → ℂ) → (Fin k → Fin (d + 1) → ℂ)) := by
  rw [differentiable_pi]
  intro i
  rw [differentiable_pi]
  intro μ
  simpa [BHW.unflattenCfg] using (differentiable_apply (finProdFinEquiv (i, μ)))

private theorem differentiable_fromDiffFlat_local (k d : ℕ) :
    Differentiable ℂ (BHW.fromDiffFlat k d) := by
  unfold BHW.fromDiffFlat
  exact (BHW.diffCoordEquiv k d).symm.differentiable.comp
    (differentiable_unflattenCfg_local k d)

private theorem differentiable_flattenCfg_local (k d : ℕ) :
    Differentiable ℂ (BHW.flattenCfg k d :
      (Fin k → Fin (d + 1) → ℂ) → (Fin (k * (d + 1)) → ℂ)) := by
  rw [differentiable_pi]
  intro i
  let p : Fin k × Fin (d + 1) := finProdFinEquiv.symm i
  let projInner :
      (Fin k → Fin (d + 1) → ℂ) → (Fin (d + 1) → ℂ) := fun z => z p.1
  let evalInner :
      (Fin k → Fin (d + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ) :=
    ContinuousLinearMap.proj (R := ℂ) p.1
  have hconst :
      Differentiable ℂ
        (fun _ : (Fin k → Fin (d + 1) → ℂ) =>
          (ContinuousLinearMap.proj (R := ℂ) p.2 :
            (Fin (d + 1) → ℂ) →L[ℂ] ℂ)) :=
    differentiable_const _
  simpa [BHW.flattenCfg, p] using
    (hconst.clm_apply
      (by simpa [projInner, evalInner] using
        (differentiable_apply p.1 : Differentiable ℂ projInner)))

private theorem differentiable_toDiffFlat_local (k d : ℕ) :
    Differentiable ℂ (BHW.toDiffFlat k d) := by
  unfold BHW.toDiffFlat
  exact (differentiable_flattenCfg_local k d).comp
    (BHW.diffCoordEquiv k d).differentiable

/-! ### First-step region as a tube over positive time-differences -/

/-- The flattened cone for `C_k^(1)`: only the time-difference coordinates are
    constrained to have positive imaginary part. -/
private def FlatPositiveTimeDiffReal (k d : ℕ) : Set (Fin (k * (d + 1)) → ℝ) :=
  {u | ∀ i : Fin k, 0 < u (finProdFinEquiv (i, 0))}

private theorem isOpen_flatPositiveTimeDiffReal (k d : ℕ) :
    IsOpen (FlatPositiveTimeDiffReal k d) := by
  simp only [FlatPositiveTimeDiffReal, Set.setOf_forall]
  exact isOpen_iInter_of_finite (fun i : Fin k =>
    isOpen_lt continuous_const (continuous_apply (finProdFinEquiv (i, 0))))

/-- `C_k^(1)` is exactly the tube over the positive time-difference cone in
    flattened difference coordinates. -/
private theorem acr_one_iff_toDiffFlat_mem_tubeDomain_positiveTimeDiff {d k : ℕ} [NeZero d]
    (z : Fin k → Fin (d + 1) → ℂ) :
    z ∈ AnalyticContinuationRegion d k 1 ↔
      BHW.toDiffFlat k d z ∈ SCV.TubeDomain (FlatPositiveTimeDiffReal k d) := by
  constructor
  · intro hz
    change (fun i => ((BHW.toDiffFlat k d z) i).im) ∈ FlatPositiveTimeDiffReal k d
    intro i
    have htime : 0 < (BHW.diffCoordEquiv k d z i 0).im := by
      by_cases hi : i.val = 0
      · have h0 := hz i 0 (Nat.le_refl 0)
        have h0' : 0 < (z i 0).im := by
          simpa [hi] using h0
        simpa [BHW.diffCoordEquiv_apply, hi] using h0'
      · have h1 := hz i 0 (Nat.le_refl 0)
        have h1' : 0 < (z i 0 - z ⟨i.val - 1, by omega⟩ 0).im := by
          simpa [hi, Complex.sub_im, sub_pos] using h1
        simpa [BHW.diffCoordEquiv_apply, hi] using h1'
    simpa [FlatPositiveTimeDiffReal, BHW.toDiffFlat, BHW.flattenCfg] using htime
  · intro hz
    change (fun i => ((BHW.toDiffFlat k d z) i).im) ∈ FlatPositiveTimeDiffReal k d at hz
    simp only [AnalyticContinuationRegion, Set.mem_setOf_eq]
    intro i μ hμ
    have hμ0 : μ = 0 := Fin.ext (Nat.eq_zero_of_le_zero hμ)
    subst hμ0
    have hflat : 0 < ((BHW.toDiffFlat k d z) (finProdFinEquiv (i, 0))).im :=
      hz i
    have hdiff : 0 < (BHW.diffCoordEquiv k d z i 0).im := by
      simpa [BHW.toDiffFlat, BHW.flattenCfg] using hflat
    by_cases hi : i.val = 0
    · simpa [BHW.diffCoordEquiv_apply, hi] using hdiff
    · have h1 : 0 < (z i 0 - z ⟨i.val - 1, by omega⟩ 0).im := by
        simpa [BHW.diffCoordEquiv_apply, hi] using hdiff
      simpa [hi, Complex.sub_im, sub_pos] using h1

/-- Transport holomorphicity on `C_k^(1)` to the positive-time-difference tube in
    flattened difference coordinates. -/
private theorem differentiableOn_toDiffFlat_of_acrone_holo {d k : ℕ} [NeZero d]
    (F : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (AnalyticContinuationRegion d k 1)) :
    DifferentiableOn ℂ (fun u : Fin (k * (d + 1)) → ℂ => F (BHW.fromDiffFlat k d u))
      (SCV.TubeDomain (FlatPositiveTimeDiffReal k d)) := by
  intro u hu
  have hz : BHW.fromDiffFlat k d u ∈ AnalyticContinuationRegion d k 1 := by
    have hu' : BHW.toDiffFlat k d (BHW.fromDiffFlat k d u) ∈
        SCV.TubeDomain (FlatPositiveTimeDiffReal k d) := by
      simpa [BHW.toDiffFlat_fromDiffFlat (n := k) (d := d) u] using hu
    exact (acr_one_iff_toDiffFlat_mem_tubeDomain_positiveTimeDiff
      (d := d) (k := k) (BHW.fromDiffFlat k d u)).mpr hu'
  have hF_at : DifferentiableAt ℂ F (BHW.fromDiffFlat k d u) :=
    (hF_holo _ hz).differentiableAt
      ((isOpen_analyticContinuationRegion_succ (d := d) (k := k) (r := 0)).mem_nhds hz)
  exact (hF_at.comp u (by
    simpa [BHW.fromDiffFlat] using differentiable_fromDiffFlat_local k d u)).differentiableWithinAt

/-- Transport holomorphicity from the positive-time-difference tube in flattened
    difference coordinates back to `C_k^(1)`. -/
private theorem differentiableOn_of_toDiffFlat_acrone_holo {d k : ℕ} [NeZero d]
    (G : (Fin (k * (d + 1)) → ℂ) → ℂ)
    (hG_holo : DifferentiableOn ℂ G (SCV.TubeDomain (FlatPositiveTimeDiffReal k d))) :
    DifferentiableOn ℂ (fun z : Fin k → Fin (d + 1) → ℂ => G (BHW.toDiffFlat k d z))
      (AnalyticContinuationRegion d k 1) := by
  intro z hz
  have hu : BHW.toDiffFlat k d z ∈ SCV.TubeDomain (FlatPositiveTimeDiffReal k d) :=
    (acr_one_iff_toDiffFlat_mem_tubeDomain_positiveTimeDiff (d := d) (k := k) z).mp hz
  have hG_at : DifferentiableAt ℂ G (BHW.toDiffFlat k d z) :=
    (hG_holo _ hu).differentiableAt
      ((SCV.tubeDomain_isOpen (isOpen_flatPositiveTimeDiffReal k d)).mem_nhds hu)
  exact (hG_at.comp z (differentiable_toDiffFlat_local k d z)).differentiableWithinAt

/-- **Base step of analytic continuation (r = 0 → r = 1).**

    Produces the first genuinely holomorphic witness on `C_k^(1)` directly from the
    Schwinger functional `OS.S k`. This avoids introducing a separate "base-region
    kernel" on `C_k^(0)`, which would be a stronger and less natural object than the
    reconstruction chain actually needs.

    In the current file, `C_k^(1)` has already been identified as a tube domain over
    the positive time-difference cone in flattened difference coordinates via
    `acr_one_iff_toDiffFlat_mem_tubeDomain_positiveTimeDiff`. So the remaining
    content is not target-domain geometry.

    The real missing input is a spectral/Laplace representation theorem for the
    Euclidean time-translation semigroup: for fixed spatial and test-function data,
    the relevant time-difference slice should be representable as a Laplace transform
    of a finite measure on `[0, ∞)`. That one-sided support is exactly what feeds the
    1D Paley-Wiener theorem on the positive time-difference tube.

    So this theorem is currently blocked by the positivity/spectral part of OS II
    (reflection positivity + Euclidean time translations -> positive-energy slice
    support), not by the tube-domain chart or the separate-to-joint holomorphicity
    mechanism.

    Ref: OS II, Section IV (base case of induction); Reed-Simon II, Section X.7;
    Streater-Wightman, §3.2-§3.3. -/
private theorem schwinger_continuation_base_step_of_flatWitness {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (k : ℕ)
    (G : (Fin (k * (d + 1)) → ℂ) → ℂ)
    (hG_holo : DifferentiableOn ℂ G (SCV.TubeDomain (FlatPositiveTimeDiffReal k d)))
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d k),
      OS.S k f = ∫ x : NPointDomain d k,
        G (BHW.toDiffFlat k d (fun j => wickRotatePoint (x j))) * (f.1 x)) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k 1) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          S_ext (fun j => wickRotatePoint (x j)) * (f.1 x)) := by
  let S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ := fun z => G (BHW.toDiffFlat k d z)
  refine ⟨S_ext, ?_, ?_⟩
  · simpa [S_ext] using
      differentiableOn_of_toDiffFlat_acrone_holo (d := d) (k := k) G hG_holo
  · intro f
    simpa [S_ext] using hG_euclid f

theorem schwinger_continuation_base_step {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k 1) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          S_ext (fun j => wickRotatePoint (x j)) * (f.1 x)) := by
  -- At this point the only missing content is to construct a holomorphic witness
  -- on the positive time-difference tube in flattened difference coordinates.
  obtain ⟨G, hG_holo, hG_euclid⟩ :
      ∃ (G : (Fin (k * (d + 1)) → ℂ) → ℂ),
        DifferentiableOn ℂ G (SCV.TubeDomain (FlatPositiveTimeDiffReal k d)) ∧
        (∀ (f : ZeroDiagonalSchwartz d k),
          OS.S k f = ∫ x : NPointDomain d k,
            G (BHW.toDiffFlat k d (fun j => wickRotatePoint (x j))) * (f.1 x)) := by
    sorry
  exact schwinger_continuation_base_step_of_flatWitness OS k G hG_holo hG_euclid

/-- **ξ-shift: the correct one-variable perturbation in the cumulative-sum structure.**

    In the cumulative-sum parametrization, the j-th new variable at level r is
      ξ[j] = z[j][r] - (if j = 0 then 0 else z[j-1][r])
    These k variables ξ[0], ..., ξ[k-1] are INDEPENDENT:
      C_k^(r+1) = C_k^(r) × UHP^k  (in the (z_base, ξ) parametrization).

    Moving ξ[j] by t (holding ξ[i] fixed for i ≠ j) requires shifting ALL z[i][r]
    for i ≥ j by +t simultaneously, since z[i][r] = ξ[0] + ... + ξ[i] (cumulative sum).

    WARNING: Updating only z[j][r] while keeping z[j+1][r],...,z[k-1][r] fixed changes
    BOTH ξ[j] (by +t) AND ξ[j+1] (by -t), which is NOT a single-variable extension.
    The test case in `test/acr_next_steps_test.lean` (d=1, k=2, r=1) confirms that a
    single-coordinate update can FAIL to land in ACR(r+1). -/
def xiShift {k d : ℕ} (j : Fin k) (r : Fin (d + 1))
    (z : Fin k → Fin (d + 1) → ℂ) (t : ℂ) : Fin k → Fin (d + 1) → ℂ :=
  fun i μ => if j.val ≤ i.val ∧ μ = r then z i μ + t else z i μ

/-- For r ≥ 1, the ξ-shift stays in C_k^(r). The shift only modifies column r,
    and C_k^(r) only constrains columns with μ.val ≤ r-1. -/
private theorem xiShift_stays_in_acr {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) (hr_pos : 0 < r)
    (z₀ : Fin k → Fin (d + 1) → ℂ)
    (hz₀ : z₀ ∈ AnalyticContinuationRegion d k r)
    (j : Fin k) (t : ℝ) :
    xiShift j ⟨r, hr⟩ z₀ (t : ℂ) ∈ AnalyticContinuationRegion d k r := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, (Nat.succ_pred_eq_of_pos hr_pos).symm⟩
  simp only [AnalyticContinuationRegion, Set.mem_setOf_eq] at hz₀ ⊢
  intro i μ hμ
  have hμ_ne : μ ≠ (⟨r' + 1, by omega⟩ : Fin (d + 1)) := by
    intro heq; have := congr_arg Fin.val heq; simp at this; omega
  -- xiShift is identity at μ ≠ ⟨r'+1, _⟩
  have h_eq : ∀ i' : Fin k, xiShift j ⟨r' + 1, by omega⟩ z₀ ↑t i' μ = z₀ i' μ := by
    intro i'
    unfold xiShift
    split_ifs with h
    · exact absurd h.2 hμ_ne
    · rfl
  rw [h_eq i]
  have h_prev : (if h : i.val = 0 then (0 : Fin (d + 1) → ℂ)
                 else xiShift j ⟨r' + 1, by omega⟩ z₀ ↑t ⟨i.val - 1, by omega⟩) μ =
                (if h : i.val = 0 then (0 : Fin (d + 1) → ℂ)
                 else z₀ ⟨i.val - 1, by omega⟩) μ := by
    by_cases hi0 : i.val = 0
    · simp [hi0]
    · simp only [hi0, ↓reduceDIte]; exact h_eq ⟨i.val - 1, by omega⟩
  rw [h_prev]
  exact hz₀ i μ hμ

/-- For r ≥ 1, ACR(r+1) is a subset of ACR(r): adding more imaginary-positivity
    constraints gives a smaller domain. -/
private theorem acr_succ_subset {d k r : ℕ} [NeZero d] (hr : 0 < r) :
    AnalyticContinuationRegion d k (r + 1) ⊆ AnalyticContinuationRegion d k r := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr) with ⟨s, rfl⟩
  intro z hz
  simpa [AnalyticContinuationRegion] using
    (fun i μ hμ => hz i μ (Nat.le_trans hμ (Nat.le_succ _)))

/-- **Mixed one-slice continuation domain** for the r → r+1 inductive step.

    `OneSliceContinuationDomain d k r hr i₀` is the "intermediate" domain where:
    - all ACR(r) positivity constraints hold (Im-differences > 0 for μ < r), AND
    - the new cumulative-difference coordinate for particle `i₀` at level r also
      has positive imaginary part: Im(z[i₀][r] - prev[i₀][r]) > 0,
    - but the other new r-th differences (for i ≠ i₀) remain unconstrained.

    **Why this domain matters**: ACR(r+1) = ⋂_{i₀} OneSliceContinuationDomain i₀
    (proved by `iInter_oneSliceContinuationDomain_eq_acr_succ`). The full Paley-Wiener
    continuation argument extends S_prev to ONE slice at a time: for each i₀, extend
    in the ξ[i₀][r] direction using 1D Paley-Wiener to get a holomorphic function on
    `OneSliceContinuationDomain i₀`. Then assemble all k slice extensions via Osgood's
    theorem to get holomorphicity on ACR(r+1).

    Ref: OS II, Theorem 4.1; Vladimirov §26 -/
def OneSliceContinuationDomain (d k r : ℕ) [NeZero d]
    (hr : r < d + 1) (i₀ : Fin k) : Set (Fin k → Fin (d + 1) → ℂ) :=
  { z |
      (∀ i : Fin k, ∀ μ : Fin (d + 1), μ.val < r →
        let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
        (z i μ - prev μ).im > 0) ∧
      let prev₀ := if h : i₀.val = 0 then 0 else z ⟨i₀.val - 1, by omega⟩
      (z i₀ ⟨r, hr⟩ - prev₀ ⟨r, hr⟩).im > 0 }

/-- Individual coordinate positivity condition is open (helper). -/
private theorem diffImPos_isOpen' {d k : ℕ} [NeZero d]
    (i : Fin k) (μ : Fin (d + 1)) :
    IsOpen { z : Fin k → Fin (d + 1) → ℂ |
      let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
      (z i μ - prev μ).im > 0 } := by
  by_cases hi : i.val = 0
  · simpa [hi] using isOpen_lt continuous_const
      (Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply i)))
  · let j : Fin k := ⟨i.val - 1, by omega⟩
    have hj' : Continuous fun z : Fin k → Fin (d + 1) → ℂ => (z j μ).im :=
      Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply j))
    have hi' : Continuous fun z : Fin k → Fin (d + 1) → ℂ => (z i μ).im :=
      Complex.continuous_im.comp ((continuous_apply μ).comp (continuous_apply i))
    simpa [hi, j, Complex.sub_im, sub_pos] using isOpen_lt hj' hi'

/-- `OneSliceContinuationDomain` is open. -/
theorem isOpen_oneSliceContinuationDomain {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) (i₀ : Fin k) :
    IsOpen (OneSliceContinuationDomain d k r hr i₀) := by
  have : OneSliceContinuationDomain d k r hr i₀ =
      (⋂ i : Fin k, ⋂ μ : Fin (d + 1),
        { z : Fin k → Fin (d + 1) → ℂ |
          μ.val < r →
            let prev := if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩
            (z i μ - prev μ).im > 0 }) ∩
      { z : Fin k → Fin (d + 1) → ℂ |
        let prev₀ := if h : i₀.val = 0 then 0 else z ⟨i₀.val - 1, by omega⟩
        (z i₀ ⟨r, hr⟩ - prev₀ ⟨r, hr⟩).im > 0 } := by
    ext z; simp [OneSliceContinuationDomain]
  rw [this]
  apply (isOpen_iInter_of_finite fun i : Fin k =>
    isOpen_iInter_of_finite fun μ : Fin (d + 1) => ?_).inter (diffImPos_isOpen' i₀ ⟨r, hr⟩)
  by_cases hμ : μ.val < r
  · simpa [hμ] using diffImPos_isOpen' (d := d) (k := k) i μ
  · simp [hμ]

/-- ACR(r+1) ⊆ OneSliceContinuationDomain for each i₀. -/
theorem acr_succ_subset_oneSliceContinuationDomain {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) (i₀ : Fin k) :
    AnalyticContinuationRegion d k (r + 1) ⊆ OneSliceContinuationDomain d k r hr i₀ := by
  intro z hz
  simp only [AnalyticContinuationRegion, OneSliceContinuationDomain, Set.mem_setOf_eq] at hz ⊢
  exact ⟨fun i μ hμ => hz i μ (Nat.le_of_lt hμ), hz i₀ ⟨r, hr⟩ (Nat.le_refl r)⟩

/-- OneSliceContinuationDomain ⊆ ACR(r) for r ≥ 1. -/
theorem oneSliceContinuationDomain_subset_acr {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) (hr_pos : 0 < r) (i₀ : Fin k) :
    OneSliceContinuationDomain d k r hr i₀ ⊆ AnalyticContinuationRegion d k r := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, (Nat.succ_pred_eq_of_pos hr_pos).symm⟩
  intro z hz
  simp only [OneSliceContinuationDomain, AnalyticContinuationRegion, Set.mem_setOf_eq] at hz ⊢
  intro i μ hμ
  exact hz.1 i μ (by omega)

/-- ACR(r+1) = ⋂_{i₀} OneSliceContinuationDomain d k r hr i₀. -/
theorem iInter_oneSliceContinuationDomain_eq_acr_succ {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) :
    (⋂ i₀ : Fin k, OneSliceContinuationDomain d k r hr i₀) =
      AnalyticContinuationRegion d k (r + 1) := by
  ext z
  simp only [Set.mem_iInter, OneSliceContinuationDomain, AnalyticContinuationRegion,
    Set.mem_setOf_eq]
  constructor
  · intro h i μ hμ
    rcases Nat.lt_or_eq_of_le hμ with hlt | rfl
    · exact (h i).1 i μ hlt
    · exact (h i).2
  · intro hz i₀
    exact ⟨fun i μ hμ => hz i μ (Nat.le_of_lt hμ), hz i₀ ⟨r, hr⟩ (Nat.le_refl r)⟩

/-- Updating the i₀-th row's r-th entry to `prev₀ ⟨r,hr⟩ + w` (with Im(w) > 0)
    lands in `OneSliceContinuationDomain d k r hr i₀`. -/
theorem sliceUpdate_mem_oneSliceContinuationDomain {d k r : ℕ} [NeZero d]
    (hr : r < d + 1) (hr_pos : 0 < r)
    (z₀ : Fin k → Fin (d + 1) → ℂ)
    (hz₀ : z₀ ∈ AnalyticContinuationRegion d k r)
    (i₀ : Fin k) {w : ℂ} (hw : 0 < w.im) :
    let prev₀ : Fin (d + 1) → ℂ :=
      if _ : i₀.val = 0 then 0 else z₀ ⟨i₀.val - 1, by omega⟩
    Function.update z₀ i₀
        (Function.update (z₀ i₀) ⟨r, hr⟩ (prev₀ ⟨r, hr⟩ + w))
      ∈ OneSliceContinuationDomain d k r hr i₀ := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, (Nat.succ_pred_eq_of_pos hr_pos).symm⟩
  simp only [OneSliceContinuationDomain, AnalyticContinuationRegion, Set.mem_setOf_eq] at hz₀ ⊢
  have hμ_ne : (⟨r' + 1, by omega⟩ : Fin (d + 1)) ≠ (⟨r' + 1, by omega⟩ : Fin (d + 1)) →
      False := fun h => h rfl
  refine ⟨fun i μ hμ => ?_, ?_⟩
  · have hμ_ne : μ ≠ (⟨r' + 1, by omega⟩ : Fin (d + 1)) :=
        fun heq => by simp [heq] at hμ
    have h_eq : ∀ j : Fin k, Function.update z₀ i₀
        (Function.update (z₀ i₀) (⟨r' + 1, by omega⟩ : Fin (d + 1))
          ((if h : i₀.val = 0 then (0 : Fin (d + 1) → ℂ)
            else z₀ ⟨i₀.val - 1, by omega⟩) ⟨r' + 1, by omega⟩ + w)) j μ = z₀ j μ := by
      intro j
      by_cases hj : j = i₀
      · subst hj; simp [hμ_ne]
      · simp [hj]
    rw [h_eq i]
    have h_prev_eq :
        (if h : i.val = 0 then (0 : Fin (d + 1) → ℂ)
          else Function.update z₀ i₀
            (Function.update (z₀ i₀) (⟨r' + 1, by omega⟩ : Fin (d + 1))
              ((if h : i₀.val = 0 then (0 : Fin (d + 1) → ℂ)
                else z₀ ⟨i₀.val - 1, by omega⟩) ⟨r' + 1, by omega⟩ + w))
            ⟨i.val - 1, by omega⟩) μ =
        (if h : i.val = 0 then (0 : Fin (d + 1) → ℂ) else z₀ ⟨i.val - 1, by omega⟩) μ := by
      by_cases hi0 : i.val = 0
      · simp [hi0]
      · simp only [hi0, ↓reduceDIte]; exact h_eq ⟨i.val - 1, by omega⟩
    rw [h_prev_eq]
    exact hz₀ i μ (by omega)
  · by_cases hi0 : i₀.val = 0
    · simpa [sub_eq_add_neg, Function.update, hi0] using hw
    · have hprev_ne : (⟨i₀.val - 1, by omega⟩ : Fin k) ≠ i₀ :=
        fun heq => absurd (congrArg Fin.val heq)
          (Nat.ne_of_lt (Nat.sub_lt (Nat.pos_of_ne_zero hi0) one_pos))
      simpa [sub_eq_add_neg, Function.update, hi0, hprev_ne, add_assoc, add_left_comm, add_comm]
        using hw


/-- **Domain restriction lemma: ACR(r+1) ⊆ ACR(r) (r ≥ 1).**

    This is a RESTRICTION lemma, not the OS II continuation step. Because
    ACR(r+1) ⊆ ACR(r) for r ≥ 1, any function holomorphic on ACR(r) is also
    holomorphic on ACR(r+1) by restriction (S_ext := S_prev).

    **This is NOT the full OS II argument.** The true OS II inductive step for r ≥ 1
    would extend holomorphicity to `OneSliceContinuationDomain`, which lies strictly
    between ACR(r+1) and ACR(r): `ACR(r+1) ⊆ OneSlice ⊆ ACR(r)`. Since OneSlice ⊆ ACR(r),
    a restriction argument suffices for holomorphicity on OneSlice, but not for the
    Paley-Wiener boundary value behavior needed to assemble the full OS continuation.
    The genuinely non-trivial OS II step is the base case r=0→1 (handled by
    `schwinger_continuation_base_step`), where ACR(0) (Im=0) and ACR(1) (Im>0)
    are disjoint and a Laplace/Paley-Wiener argument is indispensable.

    Ref: OS II, Theorem 4.1 (the domain inclusions) -/
theorem restrict_holomorphic_to_acr_succ {d : ℕ} [NeZero d]
    (k : ℕ) (r : ℕ) (_ : r < d + 1) (hr_pos : 0 < r)
    (S_prev : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_prev : DifferentiableOn ℂ S_prev (AnalyticContinuationRegion d k r)) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k (r + 1)) ∧
      ∀ z ∈ AnalyticContinuationRegion d k r, S_ext z = S_prev z :=
  ⟨S_prev, hS_prev.mono (acr_succ_subset hr_pos), fun _ _ => rfl⟩


/-- **Inductive continuation for `r ≥ 1` (OS II, Theorem 4.1).**

    Once the base-step has produced a holomorphic witness on `C_k^(1)`, every further
    stage `C_k^(r+1) ⊆ C_k^(r)` is obtained by restriction. The genuinely non-trivial
    analytic continuation is therefore concentrated in `schwinger_continuation_base_step`;
    this theorem is only the monotonicity step for the nested domains.

    Ref: OS II, Theorem 4.1; Reed-Simon II, Theorem IX.16 -/
theorem inductive_analytic_continuation {d : ℕ} [NeZero d]
    (k : ℕ) (r : ℕ) (hr : r < d + 1) (hr_pos : 0 < r)
    (S_prev : (Fin k → Fin (d + 1) → ℂ) → ℂ)
    (hS_prev : DifferentiableOn ℂ S_prev (AnalyticContinuationRegion d k r)) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k (r + 1)) ∧
      ∀ z ∈ AnalyticContinuationRegion d k r, S_ext z = S_prev z := by
  exact restrict_holomorphic_to_acr_succ k r hr hr_pos S_prev hS_prev

/-! ### Full analytic continuation from Euclidean to forward tube

After the base step, the active reconstruction chain already produces a holomorphic
witness on `C_k^(1)`, and `ForwardTube d k ⊆ C_k^(1)`. So the forward-tube existence
statement used below no longer depends on the separate Bochner route from
`C_k^(d+1)`.

The older Bochner approach from `C_k^(d+1)` remains mathematically interesting, but
it is not part of the active OS→Wightman pipeline here. The naive
"common SO(d+1)-orbit of the positive orthant, then convex hull" story is false, so
that side development needs a different geometric input before it can be reinstated.

Ref: OS II, Sections IV-V; Vladimirov Section 20.2 -/

/-- The forward tube already lies inside the first-step continuation region `C_k^(1)`,
    since each forward-cone difference has positive time component. -/
private theorem forwardTube_subset_acr_one {d k : ℕ} [NeZero d] :
    ForwardTube d k ⊆ AnalyticContinuationRegion d k 1 := by
  intro z hz
  rw [forwardTube_eq_imPreimage] at hz
  simp only [ForwardConeAbs, AnalyticContinuationRegion, Set.mem_setOf_eq] at hz ⊢
  intro i μ hμ
  have hμ0 : μ = 0 := Fin.ext (Nat.eq_zero_of_le_zero hμ)
  have htime :
      0 <
        ((z i 0).im -
          ((if h : i.val = 0 then (0 : Fin (d + 1) → ℝ)
            else fun ν => (z ⟨i.val - 1, by omega⟩ ν).im) 0)) := (hz i).1
  subst hμ0
  have htime' :
      ((if h : i.val = 0 then (0 : Fin (d + 1) → ℂ) else z ⟨i.val - 1, by omega⟩) 0).im <
        (z i 0).im := by
    by_cases hi : i.val = 0
    · simpa [hi, sub_pos] using htime
    · simpa [hi, sub_pos] using htime
  simpa [Complex.sub_im, sub_pos] using htime'

/-- Iterate analytic continuation from the base-step witness on `C_k^(1)` to `C_k^(d+1)`.

    The real analytic continuation starts at `r = 1`, not `r = 0`: the base-step
    theorem `schwinger_continuation_base_step` produces the first holomorphic witness
    on `ACR(1)` directly from the Schwinger functional. For `r ≥ 1`, all further steps
    are restrictions along the inclusions `ACR(r+1) ⊆ ACR(r)`.

    This avoids treating `ACR(0)` as an open complex holomorphic domain and removes
    the need for a separate pointwise "base-region kernel" theorem.

    Ref: OS II, Theorem 4.1 -/
theorem iterated_analytic_continuation
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (k : ℕ) :
    ∃ (S_ext : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_ext (AnalyticContinuationRegion d k (d + 1)) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          S_ext (fun j => wickRotatePoint (x j)) * (f.1 x)) := by
  obtain ⟨S₁, hS₁_hol, hS₁_rep⟩ := schwinger_continuation_base_step OS lgc k
  -- Invariant for r ≥ 1: holomorphicity on ACR(r) and preservation of the
  -- Euclidean pairing identity with OS.S.
  let P : ℕ → Prop := fun s =>
    ∃ (S_r : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ S_r (AnalyticContinuationRegion d k (s + 1)) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          S_r (fun j => wickRotatePoint (x j)) * (f.1 x))
  have hP0 : P 0 := ⟨S₁, hS₁_hol, hS₁_rep⟩
  have hstep : ∀ s, s + 1 < d + 1 → P s → P (s + 1) := by
    intro s hs hPs
    have hs_pos : 0 < s + 1 := Nat.succ_pos s
    rcases hPs with ⟨S_r, hS_r_hol, hS_r_rep⟩
    exact ⟨S_r, hS_r_hol.mono (acr_succ_subset hs_pos), hS_r_rep⟩
  have hP_all : ∀ s, s + 1 ≤ d + 1 → P s := by
    intro s hsle
    induction s with
    | zero =>
        exact hP0
    | succ s ih =>
        have hslt : s + 1 < d + 1 := by omega
        have hsle' : s + 1 ≤ d + 1 := by omega
        exact hstep (s := s) hslt (ih hsle')
  rcases hP_all d (by simp) with ⟨S_ext, hS_ext_hol, hS_ext_rep⟩
  exact ⟨S_ext, hS_ext_hol, hS_ext_rep⟩

theorem full_analytic_continuation
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (W_analytic : (Fin k → Fin (d + 1) → ℂ) → ℂ),
      DifferentiableOn ℂ W_analytic (ForwardTube d k) ∧
      (∀ (f : ZeroDiagonalSchwartz d k),
        OS.S k f = ∫ x : NPointDomain d k,
          W_analytic (fun j => wickRotatePoint (x j)) * (f.1 x)) := by
  obtain ⟨S₁, hS₁_hol, hS₁_euclid⟩ := schwinger_continuation_base_step OS lgc k
  refine ⟨S₁, hS₁_hol.mono (forwardTube_subset_acr_one (d := d) (k := k)), hS₁_euclid⟩

private theorem differentiableOn_flatten_forwardTube {d n : ℕ} [NeZero d]
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (ForwardTube d n)) :
    DifferentiableOn ℂ (F ∘ (flattenCLEquiv n (d + 1)).symm)
      (SCV.TubeDomain (ForwardConeFlat d n)) := by
  rw [← forwardTube_flatten_eq_tubeDomain]
  refine hF.comp (flattenCLEquiv n (d + 1)).symm.differentiableOn (fun w hw => ?_)
  obtain ⟨z, hz, rfl⟩ := hw
  convert hz using 1
  exact (flattenCLEquiv n (d + 1)).symm_apply_apply z

private theorem boundary_values_tempered_of_flatTempered {d : ℕ} [NeZero d]
    (n : ℕ)
    {F_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_hol : DifferentiableOn ℂ F_analytic (ForwardTube d n))
    (hTempered : SCV.HasFourierLaplaceReprTempered (ForwardConeFlat d n)
      (F_analytic ∘ (flattenCLEquiv n (d + 1)).symm)) :
    ∃ (W : SchwartzNPoint d n →L[ℂ] ℂ),
      ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            F_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W f)) := by
  let e := flattenCLEquiv n (d + 1)
  let eR := flattenCLEquivReal n (d + 1)
  let G : (Fin (n * (d + 1)) → ℂ) → ℂ := F_analytic ∘ e.symm
  let pushforward : SchwartzNPoint d n →L[ℂ]
      SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eR.symm
  have hG_hol : DifferentiableOn ℂ G (SCV.TubeDomain (ForwardConeFlat d n)) :=
    differentiableOn_flatten_forwardTube hF_hol
  have hdist_lin :
      IsLinearMap ℂ hTempered.dist :=
    SCV.fourierLaplace_dist_isLinearMap_tempered
      (forwardConeFlat_isOpen d n)
      (forwardConeFlat_convex d n)
      (forwardConeFlat_nonempty d n)
      (forwardConeFlat_isCone d n)
      hG_hol hTempered
  let W : SchwartzNPoint d n →L[ℂ] ℂ :=
    { toLinearMap :=
        { toFun := fun f => hTempered.dist (pushforward f)
          map_add' := fun f g => by
            rw [map_add]
            exact hdist_lin.map_add _ _
          map_smul' := fun c f => by
            rw [map_smul]
            exact hdist_lin.map_smul _ _ }
      cont := hTempered.dist_continuous.comp pushforward.continuous }
  refine ⟨W, ?_⟩
  intro f η hη
  have hηflat : eR η ∈ ForwardConeFlat d n :=
    ⟨η, (inForwardCone_iff_mem_forwardConeAbs η).mp hη, rfl⟩
  have hflat :
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ x : Fin (n * (d + 1)) → ℝ,
            G (fun i => ↑(x i) + ε * ↑(eR η i) * Complex.I) * (pushforward f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (hTempered.dist (pushforward f))) :=
    hTempered.boundary_value (pushforward f) (eR η) hηflat
  have hEq :
      (fun ε : ℝ =>
        ∫ x : Fin (n * (d + 1)) → ℝ,
          G (fun i => ↑(x i) + ε * ↑(eR η i) * Complex.I) * (pushforward f x))
      =
      (fun ε : ℝ =>
        ∫ y : NPointDomain d n,
          F_analytic (fun k μ => ↑(y k μ) + ε * ↑(η k μ) * Complex.I) * (f y)) := by
    funext ε
    rw [integral_flatten_change_of_variables n (d + 1)
      (fun x : Fin (n * (d + 1)) → ℝ =>
        G (fun i => ↑(x i) + ε * ↑(eR η i) * Complex.I) * (pushforward f x))]
    congr 1
    ext y
    have hFarg :
        G (fun i => ↑(eR y i) + ε * ↑(eR η i) * Complex.I) =
          F_analytic (fun k μ => ↑(y k μ) + ε * ↑(η k μ) * Complex.I) := by
      change F_analytic (e.symm (fun i => ↑(eR y i) + ε * ↑(eR η i) * Complex.I)) =
        F_analytic (fun k μ => ↑(y k μ) + ε * ↑(η k μ) * Complex.I)
      congr 1
      ext k μ
      have hyk : eR y (finProdFinEquiv (k, μ)) = y k μ := by
        simp [eR, flattenCLEquivReal_apply]
      have hηk : eR η (finProdFinEquiv (k, μ)) = η k μ := by
        simp [eR, flattenCLEquivReal_apply]
      rw [show (e.symm (fun i => ↑(eR y i) + ε * ↑(eR η i) * Complex.I)) k μ =
          (fun i => ↑(eR y i) + ε * ↑(eR η i) * Complex.I) (finProdFinEquiv (k, μ)) by
            simp [e, flattenCLEquiv_symm_apply]]
      simp [hyk, hηk]
    have hfarg : pushforward f (eR y) = f y := by
      simp [pushforward, eR]
    rw [hFarg, hfarg]
  rw [hEq] at hflat
  simpa [W, G, pushforward] using hflat

/-! ### Phase 4: Tempered boundary values

**Critical**: E0' (linear growth condition) is essential for temperedness.
Without growth control, boundary values might fail to be tempered
(the gap in OS I Lemma 8.8). E0' gives |W_n(f)| <= C_n * ||f||_{s,n}
where C_n has at most factorial growth.

Ref: OS II, Section VI -/

/--
The continuous-linear boundary-value witness is no longer the missing part of
Phase 4. Once the flattened continuation carries an honest tempered Fourier-Laplace
boundary-value package, `boundary_values_tempered_of_flatTempered` transports it
back to `NPointDomain` and constructs the required continuous linear functional.

So the remaining content here is exactly the theorem producing that honest tempered
flattened package for the specific `F_analytic` supplied by
`full_analytic_continuation`.
-/

theorem boundary_values_tempered
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n : ℕ) :
    ∃ (W_n : SchwartzNPoint d n → ℂ) (F_analytic : (Fin n → Fin (d + 1) → ℂ) → ℂ),
      -- W_n is continuous (tempered distribution)
      Continuous W_n ∧
      -- W_n is linear
      IsLinearMap ℂ W_n ∧
      -- F_analytic is holomorphic on the forward tube
      DifferentiableOn ℂ F_analytic (ForwardTube d n) ∧
      -- Boundary values of F_analytic give W_n
      (∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
        InForwardCone d n η →
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : NPointDomain d n,
            F_analytic (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
          (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n f))) ∧
      -- Euclidean restriction of F_analytic gives S_n on the corrected OS test space.
      (∀ (f : ZeroDiagonalSchwartz d n),
        OS.S n f = ∫ x : NPointDomain d n,
          F_analytic (fun k => wickRotatePoint (x k)) * (f.1 x)) := by
  obtain ⟨F_analytic, hF_hol, hF_euclid⟩ := full_analytic_continuation OS lgc n
  let G : (Fin (n * (d + 1)) → ℂ) → ℂ :=
    F_analytic ∘ (flattenCLEquiv n (d + 1)).symm
  have hG_hol : DifferentiableOn ℂ G (SCV.TubeDomain (ForwardConeFlat d n)) :=
    differentiableOn_flatten_forwardTube hF_hol
  -- Remaining content, now stated explicitly rather than hidden inside a structure:
  -- construct the flattened boundary distribution together with the two honest
  -- OS-II growth bounds. Those four fields are exactly what is needed to build
  -- `HasFourierLaplaceReprTempered` and hence the tempered Wightman boundary value.
  obtain ⟨Tflat, hTflat_cont, hBVflat, hpoly, hunif⟩ :
      ∃ (Tflat : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ → ℂ),
        Continuous Tflat ∧
        (∀ (f : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ)
            (η : Fin (n * (d + 1)) → ℝ), η ∈ ForwardConeFlat d n →
            Filter.Tendsto (fun ε : ℝ =>
              ∫ x : Fin (n * (d + 1)) → ℝ,
                G (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I) * f x)
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds (Tflat f))) ∧
        (∀ (K : Set (Fin (n * (d + 1)) → ℝ)), IsCompact K → K ⊆ ForwardConeFlat d n →
          ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
            ∀ (x y : Fin (n * (d + 1)) → ℝ), y ∈ K →
              ‖G (fun i => ↑(x i) + ↑(y i) * Complex.I)‖ ≤ C_bd * (1 + ‖x‖) ^ N) ∧
        (∀ (η : Fin (n * (d + 1)) → ℝ), η ∈ ForwardConeFlat d n →
          ∃ (C_bd : ℝ) (N : ℕ) (δ : ℝ), C_bd > 0 ∧ δ > 0 ∧
            ∀ (x : Fin (n * (d + 1)) → ℝ) (ε : ℝ), 0 < ε → ε < δ →
              ‖G (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I)‖ ≤ C_bd * (1 + ‖x‖) ^ N) := by
    sorry
  let hTempered :
      SCV.HasFourierLaplaceReprTempered (ForwardConeFlat d n) G :=
    SCV.exists_fourierLaplaceReprTempered
      (forwardConeFlat_isOpen d n)
      (forwardConeFlat_convex d n)
      (forwardConeFlat_nonempty d n)
      hG_hol hTflat_cont hBVflat hpoly hunif
  obtain ⟨W, hW_bv⟩ :=
    boundary_values_tempered_of_flatTempered (d := d) n hF_hol (by simpa [G] using hTempered)
  refine ⟨W, F_analytic, W.continuous, ?_, hF_hol, hW_bv, fun f => hF_euclid f⟩
  constructor
  · intro f g
    exact map_add W f g
  · intro c f
    exact map_smul W c f

/-! ### Constructing WightmanFunctions from OS Data

Each Wightman axiom is derived from the corresponding OS axiom via analytic
continuation. The helper lemmas below capture each derivation. -/

/-- The n-point Wightman distribution `W_n` extracted from `boundary_values_tempered`.

    `boundary_values_tempered` returns `∃ W_n F_analytic, Continuous W_n ∧ IsLinearMap ℂ W_n ∧ ...`.
    This definition extracts `W_n` via `.choose` (the first existential witness).

    `W_n` is the tempered distributional boundary value of the analytically continued
    function `F_analytic` on the forward tube. It is continuous (tempered) and linear.

    Note: `boundary_values_tempered` is deferred in this file, so `bvt_W` and
    downstream properties remain contingent on that theorem. -/
def bvt_W (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    SchwartzNPoint d n → ℂ :=
  (boundary_values_tempered OS lgc n).choose

/-- The holomorphic function `F_analytic` on the forward tube, extracted from
    `boundary_values_tempered`.

    `boundary_values_tempered` returns `∃ W_n F_analytic, ... ∧ DifferentiableOn ℂ F_analytic
    (ForwardTube d n) ∧ ...`. This definition extracts `F_analytic` via
    `.choose_spec.choose` (the second existential witness, nested inside the first).

    `F_analytic` is holomorphic on `ForwardTube d n`, its distributional boundary values
    recover `bvt_W` (the Wightman distribution), and its Euclidean restriction
    (via Wick rotation) recovers the Schwinger functions `OS.S n`.

    Note: `boundary_values_tempered` is deferred in this file, so `bvt_F` and
    downstream properties remain contingent on that theorem. -/
def bvt_F (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    (Fin n → Fin (d + 1) → ℂ) → ℂ :=
  (boundary_values_tempered OS lgc n).choose_spec.choose

theorem bvt_W_continuous (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    Continuous (bvt_W OS lgc n) :=
  (boundary_values_tempered OS lgc n).choose_spec.choose_spec.1

theorem bvt_F_holomorphic (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    DifferentiableOn ℂ (bvt_F OS lgc n) (ForwardTube d n) :=
  (boundary_values_tempered OS lgc n).choose_spec.choose_spec.2.2.1

theorem bvt_boundary_values (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          bvt_F OS lgc n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_W OS lgc n f)) :=
  (boundary_values_tempered OS lgc n).choose_spec.choose_spec.2.2.2.1

theorem bvt_euclidean_restriction (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    ∀ (f : ZeroDiagonalSchwartz d n),
      OS.S n f = ∫ x : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (x k)) * (f.1 x) :=
  (boundary_values_tempered OS lgc n).choose_spec.choose_spec.2.2.2.2

/-! #### Helper lemmas for property transfer: OS axiom → F_analytic → W_n

Each bvt_* property follows a three-step transfer:
1. OS axiom (E0-E4) gives a property of S_n
2. S_n = F_analytic ∘ wickRotate (Euclidean restriction) transfers to F_analytic
3. W_n = BV(F_analytic) (boundary value) transfers to W_n

The following helpers isolate the transfer steps as smaller sorry targets. -/

/-- E2R normalization: The 0-point BV is evaluation at the origin.

    For n = 0, the domain Fin 0 → Fin (d+1) → ℝ is a zero-dimensional space
    (a single point). The forward tube ForwardTube d 0 is all of the (trivial)
    domain. The analytic function F_analytic is a constant. The BV condition
    reduces to: the constant value times f(0) = W_0(f), so W_0(f) = c * f(0).
    Combining with the OS normalization (S_0 is normalized by the Euclidean
    restriction), we get c = 1, hence W_0(f) = f(0).

    This requires: (1) identifying the integral over the zero-dimensional space,
    (2) the OS normalization condition S_0(f) = f(0). -/
theorem bv_zero_point_is_evaluation (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (W_0 : SchwartzNPoint d 0 → ℂ)
    (F_0 : (Fin 0 → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d 0) (η : Fin 0 → Fin (d + 1) → ℝ),
      InForwardCone d 0 η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : Fin 0 → Fin (d + 1) → ℝ,
          F_0 (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_0 f)))
    (hEuclid : ∀ (f : ZeroDiagonalSchwartz d 0),
      OS.S 0 f = ∫ x : Fin 0 → Fin (d + 1) → ℝ,
        F_0 (fun k => wickRotatePoint (x k)) * (f.1 x)) :
    ∀ f : SchwartzNPoint d 0, W_0 f = f 0 := by
  intro f
  let η0 : Fin 0 → Fin (d + 1) → ℝ := fun k => Fin.elim0 k
  have hη0 : InForwardCone d 0 η0 := by
    intro k
    exact Fin.elim0 k
  set I0 : ℂ := ∫ x : Fin 0 → Fin (d + 1) → ℝ,
      F_0 (fun k => wickRotatePoint (x k)) * (f x)
  have hconst :
      ∀ ε : ℝ,
        (∫ x : Fin 0 → Fin (d + 1) → ℝ,
          F_0 (fun k μ => ↑(x k μ) + ε * ↑(η0 k μ) * Complex.I) * (f x)) = I0 := by
    intro ε
    unfold I0
    congr 1
    ext x
    have hz : (fun k μ => ↑(x k μ) + ε * ↑(η0 k μ) * Complex.I) =
        (fun k => wickRotatePoint (x k)) := by
      funext k
      exact Fin.elim0 k
    simp [hz]
  have hBV0 : Filter.Tendsto (fun ε : ℝ => I0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (W_0 f)) := by
    simpa [hconst] using hBV f η0 hη0
  have hI0 : Filter.Tendsto (fun ε : ℝ => I0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds I0) :=
    tendsto_const_nhds
  have hW0 : W_0 f = I0 :=
    tendsto_nhds_unique hBV0 hI0
  let f0 : ZeroDiagonalSchwartz d 0 := ⟨f, by
    intro k x hx
    rcases hx with ⟨i, _, _, _⟩
    exact Fin.elim0 i⟩
  calc
    W_0 f = I0 := hW0
    _ = OS.S 0 f0 := by simpa [I0, f0] using (hEuclid f0).symm
    _ = f 0 := lgc.normalized_zero f0

/-- E2R translation: Translation invariance transfers from S_n (via E1) through
    the analytic continuation to the BV.

    The argument: E1 says S_n is translation-invariant. The Euclidean restriction
    shows F_analytic is translation-invariant at Euclidean points. By analytic
    continuation, F_analytic is translation-invariant on the forward tube. The BV
    limit preserves translation invariance. -/
theorem bv_translation_invariance_transfer (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (hW_cont : Continuous W_n)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_hol : DifferentiableOn ℂ F_n (ForwardTube d n))
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hEuclid : ∀ (f : ZeroDiagonalSchwartz d n),
      OS.S n f = ∫ x : NPointDomain d n,
        F_n (fun k => wickRotatePoint (x k)) * (f.1 x))
    (hE1 : ∀ (a : SpacetimeDim d) (f g : ZeroDiagonalSchwartz d n),
      (∀ x, g.1 x = f.1 (fun i => x i + a)) →
      OS.S n f = OS.S n g) :
    ∀ (a : SpacetimeDim d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
      W_n f = W_n g := by
  -- Proof sketch: From hEuclid and hE1, F_n(wick(x)) = F_n(wick(x-a)) for all x, so F_n is
  -- invariant under the Euclidean shift wick_a = (i*a_0, a_1, ..., a_d).
  -- By distributional_uniqueness_forwardTube, F_n(z) = F_n(z - wick_a) on all of FT.
  -- The BV limit W_n(g) = lim ∫ F_n(x + iεη) f(x+a) dx = lim ∫ F_n(y - a + iεη) f(y) dy,
  -- and y - a + iεη = y - wick_a + iεη (up to the i*a_0 time component cancellation) — but
  -- this identification fails because a_0 ≠ i*a_0 (real vs imaginary time shift).
  -- Full proof requires the analytic continuation infrastructure (BHW + OS II Section VI).
  sorry

/-- E2R Lorentz: Lorentz covariance transfers from E1 (Euclidean rotation
    invariance) through BHW to the BV.

    The argument: E1 gives SO(d+1)-invariance of S_n. The analytic continuation
    extends this to SO(d+1,C)-invariance of F_analytic. The restricted Lorentz
    group SO+(1,d) embeds in SO(d+1,C) (Bargmann-Hall-Wightman), giving
    real Lorentz invariance of F_analytic. The BV preserves this invariance. -/
theorem bv_lorentz_covariance_transfer (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_hol : DifferentiableOn ℂ F_n (ForwardTube d n))
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hEuclid : ∀ (f : ZeroDiagonalSchwartz d n),
      OS.S n f = ∫ x : NPointDomain d n,
        F_n (fun k => wickRotatePoint (x k)) * (f.1 x))
    (hE1_rot : ∀ (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      R.transpose * R = 1 → R.det = 1 →
      ∀ (f g : ZeroDiagonalSchwartz d n),
      (∀ x, g.1 x = f.1 (fun i => R.mulVec (x i))) →
      OS.S n f = OS.S n g) :
    ∀ (Λ : LorentzGroup d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
      W_n f = W_n g := by
  sorry

/-- E2R locality: Local commutativity transfers from E3 (permutation symmetry)
    + edge-of-the-wedge to the BV.

    The argument: E3 says S_n is permutation-symmetric. The Euclidean restriction
    shows F_analytic is permutation-symmetric at Euclidean points. By analytic
    continuation (Jost's theorem), this extends to the permuted extended tube.
    Edge-of-the-wedge at the boundary gives local commutativity of W_n. -/
theorem bv_local_commutativity_transfer (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_hol : DifferentiableOn ℂ F_n (ForwardTube d n))
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hE3 : ∀ (σ : Equiv.Perm (Fin n)) (f g : ZeroDiagonalSchwartz d n),
      (∀ x, g.1 x = f.1 (fun i => x (σ i))) →
      OS.S n f = OS.S n g) :
    ∀ (i j : Fin n) (f g : SchwartzNPoint d n),
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      W_n f = W_n g := by
  sorry

/-- E2R positivity: Positive definiteness transfers from E2 (reflection positivity)
    through the Wick rotation.

    The argument: The Wightman inner product sum_{n,m} W_{n+m}(f*_n x f_m) is
    related to the OS inner product sum_{n,m} S_{n+m}(theta(f*_n) x f_m) by
    analytic continuation. E2 ensures the OS inner product is non-negative,
    hence the Wightman inner product is non-negative. -/
theorem bv_positive_definiteness_transfer (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (W : (n : ℕ) → SchwartzNPoint d n → ℂ)
    (hW_eq : ∀ n, W n = bvt_W OS lgc n)
    (hE2 : ∀ (F : BorchersSequence d),
      (∀ n, tsupport ((F.funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n) →
      (OSInnerProduct d OS.S F F).re ≥ 0) :
    ∀ F : BorchersSequence d, (WightmanInnerProduct d W F F).re ≥ 0 := by
  sorry

/-- E2R Hermiticity: Hermiticity of W_n from reality of Schwinger functions.

    The Schwinger functions are real-valued on real configurations. Under
    analytic continuation, this gives a Schwarz reflection principle for
    F_analytic. Taking BV, this yields the Hermiticity condition
    W_n(f~) = conj(W_n(f)). -/
theorem bv_hermiticity_transfer (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_hol : DifferentiableOn ℂ F_n (ForwardTube d n))
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hEuclid : ∀ (f : ZeroDiagonalSchwartz d n),
      OS.S n f = ∫ x : NPointDomain d n,
        F_n (fun k => wickRotatePoint (x k)) * (f.1 x)) :
    ∀ (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n,
        g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
      W_n g = starRingEnd ℂ (W_n f) := by
  sorry

/-- S44: W_0 = 1 (normalization).
    The 0-point Schwinger function S_0 = 1 (OS normalization). Its analytic
    continuation is the constant function 1 on the (trivial) forward tube.
    The distributional BV of 1 is evaluation: W_0(f) = f(0). -/
theorem bvt_normalized (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsNormalized d (bvt_W OS lgc) := by
  intro f
  exact bv_zero_point_is_evaluation OS lgc
    (bvt_W OS lgc 0)
    (bvt_F OS lgc 0)
    (bvt_boundary_values OS lgc 0)
    (bvt_euclidean_restriction OS lgc 0)
    f

/-- S45: Translation invariance of W_n from E1. -/
theorem bvt_translation_invariant (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsTranslationInvariantWeak d (bvt_W OS lgc) := by
  intro n a f g hfg
  exact bv_translation_invariance_transfer OS lgc n
    (bvt_W OS lgc n)
    (bvt_W_continuous OS lgc n)
    (bvt_F OS lgc n)
    (bvt_F_holomorphic OS lgc n)
    (bvt_boundary_values OS lgc n)
    (bvt_euclidean_restriction OS lgc n)
    (OS.E1_translation_invariant n)
    a f g hfg

/-- S46: Lorentz covariance of W_n from E1 via BHW. -/
theorem bvt_lorentz_covariant (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsLorentzCovariantWeak d (bvt_W OS lgc) := by
  intro n Λ f g hfg
  exact bv_lorentz_covariance_transfer OS lgc n
    (bvt_W OS lgc n)
    (bvt_F OS lgc n)
    (bvt_F_holomorphic OS lgc n)
    (bvt_boundary_values OS lgc n)
    (bvt_euclidean_restriction OS lgc n)
    (OS.E1_rotation_invariant n)
    Λ f g hfg

/-- S47: Local commutativity of W_n from E3 + edge-of-the-wedge. -/
theorem bvt_locally_commutative (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsLocallyCommutativeWeak d (bvt_W OS lgc) := by
  intro n i j f g hsupp hswap
  exact bv_local_commutativity_transfer OS lgc n
    (bvt_W OS lgc n)
    (bvt_F OS lgc n)
    (bvt_F_holomorphic OS lgc n)
    (bvt_boundary_values OS lgc n)
    (OS.E3_symmetric n)
    i j f g hsupp hswap

/-- S48: Positive definiteness of W_n from E2 (reflection positivity). -/
theorem bvt_positive_definite (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    IsPositiveDefinite d (bvt_W OS lgc) := by
  exact bv_positive_definiteness_transfer OS lgc
    (bvt_W OS lgc)
    (fun _ => rfl)
    OS.E2_reflection_positive

/-- S49: Hermiticity of W_n from reality of Schwinger functions. -/
theorem bvt_hermitian (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n : ℕ) (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n,
        g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
      bvt_W OS lgc n g = starRingEnd ℂ (bvt_W OS lgc n f) := by
  intro n f g hfg
  exact bv_hermiticity_transfer OS lgc n
    (bvt_W OS lgc n)
    (bvt_F OS lgc n)
    (bvt_F_holomorphic OS lgc n)
    (bvt_boundary_values OS lgc n)
    (bvt_euclidean_restriction OS lgc n)
    f g hfg

/-- The cluster property (R4) for the reconstructed Wightman functions.

    The cluster property of the boundary value distributions W_n follows from the
    cluster property E4 of the Schwinger functions via analytic continuation.

    The proof lifts E4 (distributional cluster in Euclidean space) to the Minkowski
    boundary values using the boundary value correspondence: the spatial translations
    commute with the Wick rotation, so the Euclidean factorization at large spacelike
    separation passes to the Minkowski distributional boundary values.

    Ref: OS I (1973), Section 5; OS II (1975), Section VI -/
theorem bvt_cluster (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∀ (n m : ℕ) (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
      ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
        ∀ a : SpacetimeDim d, a 0 = 0 → (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ (g_a : SchwartzNPoint d m),
            (∀ x : NPointDomain d m, g_a x = g (fun i => x i - a)) →
            ‖bvt_W OS lgc (n + m) (f.tensorProduct g_a) -
              bvt_W OS lgc n f * bvt_W OS lgc m g‖ < ε := by
  sorry

/-- Given OS axioms with linear growth condition, construct the full collection
    of Wightman functions from the analytic continuation boundary values. -/
def constructWightmanFunctions (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    WightmanFunctions d where
  W := bvt_W OS lgc
  linear := fun n => (boundary_values_tempered OS lgc n).choose_spec.choose_spec.2.1
  tempered := fun n => (boundary_values_tempered OS lgc n).choose_spec.choose_spec.1
  normalized := bvt_normalized OS lgc
  translation_invariant := bvt_translation_invariant OS lgc
  lorentz_covariant := bvt_lorentz_covariant OS lgc
  spectrum_condition := by
    intro n
    have h := (boundary_values_tempered OS lgc n).choose_spec.choose_spec
    exact ⟨(boundary_values_tempered OS lgc n).choose_spec.choose,
      h.2.2.1, h.2.2.2.1⟩
  locally_commutative := bvt_locally_commutative OS lgc
  positive_definite := bvt_positive_definite OS lgc
  hermitian := bvt_hermitian OS lgc
  cluster := bvt_cluster OS lgc

/-- The OS pre-Hilbert space constructed from the Wightman functions obtained
    via analytic continuation of Schwinger functions.

    In the OS reconstruction (OS II, 1975), the Wightman functions are obtained
    from the Schwinger functions by analytic continuation, using the linear growth
    condition E0' to control the distribution order growth.

    The pre-Hilbert space uses the Wightman inner product:
      ⟨F, G⟩ = Σ_{n,m} W_{n+m}(f̄_n ⊗ g_m)
    where W_n are the boundary values of the analytic continuation of S_n.

    **Requires the linear growth condition E0'**: Without it, the analytic
    continuation may fail to produce tempered boundary values (OS I, Lemma 8.8 gap).

    Ref: OS II (1975), Sections IV-VI -/
def osPreHilbertSpace (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :=
  PreHilbertSpace (constructWightmanFunctions OS lgc)

/-! ### The Bridge Theorems -/

/-- **Theorem R→E**: Wightman functions produce the honest zero-diagonal
    Euclidean Schwinger family on `°S`.

    This is intentionally weaker than the OS-II full-Schwartz surface:
    the raw Wick-rotated pairing is only packaged on `ZeroDiagonalSchwartz`,
    together with continuity there and the Wick-rotation relation to the
    Wightman boundary values. No `OSLinearGrowthCondition` is assumed in this
    direction. -/
theorem wightman_to_os_full (Wfn : WightmanFunctions d) :
    ∃ (S : SchwingerFunctions d),
      (∀ n, Continuous (S n)) ∧
      (∀ n, IsLinearMap ℂ (S n)) ∧
      IsWickRotationPair S Wfn.W := by
  refine ⟨constructZeroDiagonalSchwingerFunctions Wfn, ?_, ?_, ?_⟩
  · intro n
    simpa [constructZeroDiagonalSchwingerFunctions] using
      constructedSchwinger_tempered_zeroDiagonal Wfn n
  · intro n
    simpa [constructZeroDiagonalSchwingerFunctions] using
      constructedZeroDiagonalSchwinger_linear Wfn n
  intro n
  -- Use the BHW extension F_ext as the zero-diagonal Wick-rotation witness.
  -- F_ext = BHW extension, holomorphic on PET (hence on the forward tube).
  -- Its boundary values agree with W_n since F_ext = W_analytic on the forward tube.
  refine ⟨(W_analytic_BHW Wfn n).val,
    (W_analytic_BHW Wfn n).property.1.mono
      (ForwardTube_subset_ComplexExtended d n |>.trans
        (ComplexExtended_subset_Permuted d n)),
    ?_, fun _ => rfl⟩
  · -- Boundary values: use bhw_distributional_boundary_values directly.
    -- The previous approach tried to show x + iεη ∈ ForwardTube, which is false
    -- due to coordinate convention mismatch (absolute vs difference coordinates).
    intro f η hη
    exact bhw_distributional_boundary_values Wfn f η hη

/-- **Theorem E'→R'** (OS II surface): OS axioms together with the linear growth
    condition produce Wightman functions.

    This direction intentionally keeps the stronger OS-II hypothesis
    `OSLinearGrowthCondition`; it is the ingredient that repairs the OS-I gap
    in the reconstruction of tempered Wightman boundary values. -/
theorem os_to_wightman_full (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ∃ (Wfn : WightmanFunctions d),
      -- The Wightman functions are the Wick rotation of the honest zero-diagonal
      -- Schwinger family carried by `OS`.
      IsWickRotationPair OS.schwinger Wfn.W := by
  refine ⟨constructWightmanFunctions OS lgc, fun n => ?_⟩
  -- The analytic continuation, boundary values, and euclidean restriction are
  -- exactly the fields constructed inside `boundary_values_tempered`.
  have h := (boundary_values_tempered OS lgc n).choose_spec.choose_spec
  exact ⟨(boundary_values_tempered OS lgc n).choose_spec.choose,
    h.2.2.1, h.2.2.2.1, fun f => by
      simpa [OsterwalderSchraderAxioms.schwinger] using h.2.2.2.2 f⟩

/-! ### Wired Corollaries

The theorem wiring to canonical names now lives in
`Wightman/Reconstruction/Main.lean`. The `_full` theorems above remain the
implementation-level results used by that wiring layer. -/

end
